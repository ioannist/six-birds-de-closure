#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  launch_compressed_campaign.sh [--groups C1:lcdm,C2:w0wa] [--max-cores 57] [--chains 4] [--omp-threads 1] [--max-samples 6000] [--resume]

Runs the compressed-CMB E1 track. Each group uses chains*omp_threads cores.
EOF
}

groups_arg=""
max_cores="${SBT_MAX_CORES:-57}"
chains=4
omp_threads=1
max_samples=6000
resume_flag=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --groups) groups_arg="$2"; shift 2 ;;
    --max-cores) max_cores="$2"; shift 2 ;;
    --chains) chains="$2"; shift 2 ;;
    --omp-threads) omp_threads="$2"; shift 2 ;;
    --max-samples) max_samples="$2"; shift 2 ;;
    --resume) resume_flag="--resume"; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

if [[ -n "$groups_arg" ]]; then
  IFS=',' read -r -a groups <<< "$groups_arg"
else
  groups=(
    "C1:lcdm" "C1:wcdm" "C1:w0wa"
    "C2:lcdm" "C2:wcdm" "C2:w0wa"
    "C3:lcdm" "C3:wcdm" "C3:w0wa"
    "C4:lcdm" "C4:wcdm" "C4:w0wa"
    "C5:lcdm" "C5:wcdm" "C5:w0wa"
  )
fi

cores_per_group=$(( chains * omp_threads ))
concurrent_groups=$(( max_cores / cores_per_group ))
if [[ "$concurrent_groups" -lt 1 ]]; then
  echo "--max-cores must be at least chains*omp_threads (${cores_per_group})" >&2
  exit 2
fi

mkdir -p runs/E1/compressed_campaign_status
running=0
declare -A pid_to_run_id=()
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
  local run_id="${pid_to_run_id[$completed_pid]:-unknown-pid-${completed_pid}}"
  unset "pid_to_run_id[$completed_pid]"
  running=$((running - 1))
  if [[ "$exit_code" -eq 0 ]]; then
    succeeded+=("$run_id")
    echo "GROUP SUCCEEDED: ${run_id}"
  else
    failed+=("${run_id}:${exit_code}")
    echo "GROUP FAILED: ${run_id} exit=${exit_code}"
  fi
}

for group in "${groups[@]}"; do
  combo="${group%%:*}"
  model="${group##*:}"
  run_id="E1C_${combo}_${model}"
  outdir="runs/E1/${run_id}"
  echo "launching ${run_id} (${chains} chains x OMP=${omp_threads}; ${cores_per_group} cores/group)"
  python experiments/E1_desi_dr2_repro/run_group_compressed.py \
    --config configs/experiments/E1_compressed.yaml \
    --run-id "$run_id" \
    --combination "$combo" \
    --model "$model" \
    --run-mode production \
    --chains "$chains" \
    --omp-threads "$omp_threads" \
    --max-samples "$max_samples" \
    --outdir "$outdir" \
    $resume_flag > "${outdir}.compressed.launcher.log" 2>&1 &
  pid=$!
  pid_to_run_id[$pid]="$run_id"
  running=$((running + 1))
  if [[ "$running" -ge "$concurrent_groups" ]]; then
    wait_for_one_group || true
  fi
done

while [[ "$running" -gt 0 ]]; do
  wait_for_one_group || true
done

echo "compressed campaign complete"
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
