#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  launch_campaign.sh --wave wave1|wave2|all [--groups C1:lcdm,C2:w0wa] [--max-cores 57] [--omp-threads 4] [--covmat PATH] [--concurrent-groups N] [--resume]

Each group uses chains*omp_threads cores. The default is 4 chains with
OMP_NUM_THREADS=4, so floor(57/16)=3 concurrent groups unless
--concurrent-groups is lower.
EOF
}

wave="wave1"
groups_arg=""
max_cores="${SBT_MAX_CORES:-57}"
chains=4
omp_threads=4
covmat="configs/covmats/e1_planck_lcdm.covmat"
concurrent_groups=""
resume_flag=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --wave) wave="$2"; shift 2 ;;
    --groups) groups_arg="$2"; shift 2 ;;
    --max-cores) max_cores="$2"; shift 2 ;;
    --omp-threads) omp_threads="$2"; shift 2 ;;
    --covmat) covmat="$2"; shift 2 ;;
    --concurrent-groups) concurrent_groups="$2"; shift 2 ;;
    --resume) resume_flag="--resume"; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

export SBT_MAX_CORES="$max_cores"
export COBAYA_PACKAGES_PATH="${COBAYA_PACKAGES_PATH:-/mnt/data-drive/sbt-de/data/raw/planck_2018/cobaya-packages}"
export PYTHONPATH="${COBAYA_PACKAGES_PATH}/code/planck/clik-main/lib/python/site-packages:${PYTHONPATH:-}"
export LD_LIBRARY_PATH="${COBAYA_PACKAGES_PATH}/code/planck/clik-main/lib:${LD_LIBRARY_PATH:-}"

if [[ "$chains" -lt 1 || "$omp_threads" -lt 1 || "$max_cores" -lt 1 ]]; then
  echo "--chains, --omp-threads, and --max-cores must be positive integers" >&2
  exit 2
fi
if [[ ! -f "$covmat" ]]; then
  echo "--covmat does not exist: $covmat" >&2
  exit 2
fi

if [[ -n "$groups_arg" ]]; then
  IFS=',' read -r -a groups <<< "$groups_arg"
elif [[ "$wave" == "wave1" ]]; then
  groups=("C1:lcdm" "C2:lcdm" "C2:wcdm" "C2:w0wa")
elif [[ "$wave" == "wave2" ]]; then
  groups=(
    "C3:lcdm" "C3:wcdm" "C3:w0wa"
    "C4:lcdm" "C4:wcdm" "C4:w0wa"
    "C5:lcdm" "C5:wcdm" "C5:w0wa"
  )
elif [[ "$wave" == "all" ]]; then
  groups=(
    "C1:lcdm" "C1:wcdm" "C1:w0wa"
    "C2:lcdm" "C2:wcdm" "C2:w0wa"
    "C3:lcdm" "C3:wcdm" "C3:w0wa"
    "C4:lcdm" "C4:wcdm" "C4:w0wa"
    "C5:lcdm" "C5:wcdm" "C5:w0wa"
  )
else
  echo "Unknown wave: $wave" >&2
  exit 2
fi

cores_per_group=$(( chains * omp_threads ))
core_groups=$(( max_cores / cores_per_group ))
if [[ "$core_groups" -lt 1 ]]; then
  echo "--max-cores must be at least chains*omp_threads (${cores_per_group})" >&2
  exit 2
fi
if [[ -z "$concurrent_groups" || "$concurrent_groups" -gt "$core_groups" ]]; then
  concurrent_groups="$core_groups"
fi

mkdir -p runs/E1/campaign_status
running=0
declare -A pid_to_run_id=()
declare -A pid_to_status_file=()
succeeded=()
failed=()

wait_for_one_group() {
  local completed_pid=""
  local exit_code=0
  set +e
  wait -n -p completed_pid
  exit_code=$?
  set -e
  if [[ "$exit_code" -eq 127 ]]; then
    return 127
  fi
  local completed_run_id="${pid_to_run_id[$completed_pid]:-unknown-pid-${completed_pid}}"
  local completed_status_file="${pid_to_status_file[$completed_pid]:-runs/E1/campaign_status/${completed_run_id}.status}"
  unset "pid_to_run_id[$completed_pid]"
  unset "pid_to_status_file[$completed_pid]"
  running=$((running - 1))
  if [[ "$exit_code" -eq 0 ]]; then
    succeeded+=("$completed_run_id")
    echo "GROUP SUCCEEDED: ${completed_run_id}" | tee -a "$completed_status_file"
  else
    failed+=("${completed_run_id}:${exit_code}")
    echo "GROUP FAILED: ${completed_run_id} exit=${exit_code}" | tee -a "$completed_status_file"
  fi
}

for group in "${groups[@]}"; do
  combo="${group%%:*}"
  model="${group##*:}"
  run_id="E1A_${combo}_${model}"
  outdir="runs/E1/${run_id}"
  status_file="runs/E1/campaign_status/${run_id}.status"
  echo "launching ${run_id} (${chains} chains x OMP=${omp_threads}; ${cores_per_group} cores/group)" | tee "$status_file"
  python experiments/E1_desi_dr2_repro/run_group.py \
    --config configs/experiments/E1.yaml \
    --run-id "$run_id" \
    --combination "$combo" \
    --model "$model" \
    --run-mode production \
    --chains "$chains" \
    --omp-threads "$omp_threads" \
    --rminus1-stop 0.01 \
    --rminus1-cl-stop 0.2 \
    --max-samples 40000 \
    --covmat "$covmat" \
    --outdir "$outdir" \
    $resume_flag > "${outdir}.launcher.log" 2>&1 &
  pid=$!
  pid_to_run_id[$pid]="$run_id"
  pid_to_status_file[$pid]="$status_file"
  running=$((running + 1))
  if [[ "$running" -ge "$concurrent_groups" ]]; then
    wait_for_one_group || true
  fi
done

while [[ "$running" -gt 0 ]]; do
  wait_for_one_group || true
done

echo "campaign wave ${wave} complete"
echo "GROUP SUMMARY: succeeded=${#succeeded[@]} failed=${#failed[@]}"
if [[ "${#succeeded[@]}" -gt 0 ]]; then
  printf 'SUCCEEDED: %s\n' "${succeeded[@]}"
fi
if [[ "${#failed[@]}" -gt 0 ]]; then
  printf 'FAILED: %s\n' "${failed[@]}"
fi

if [[ "${#failed[@]}" -gt 0 && "${#succeeded[@]}" -eq 0 ]]; then
  exit 1
fi
