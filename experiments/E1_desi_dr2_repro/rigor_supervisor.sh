#!/usr/bin/env bash
# ============================================================================
# Unattended supervisor for the full-clik E1-A "RIGOR" track (full-fidelity).
#
# Purpose: produce the full-Planck-clik reproduction numbers for the PAPER, to
# confirm 100% alignment with published DESI DR2. This is NOT the gate path
# (the compressed track gates E1-A); it is a background confirmation run.
#
# Problem it works around: the Planck `clik` Fortran likelihood is unstable on
# this box under parallel cobaya chains -- chains intermittently HANG at ~0% CPU
# (rows stop growing) and occasionally SEGFAULT. See runs/E1/RIGOR_TRACK_NOTE.md.
#
# Strategy: keep CLASS fast (OMP=3), low concurrency (2 groups), and run a
# supervisor loop that (a) launches the campaign with --resume, (b) kills any
# chain stuck at ~0% CPU across two consecutive checks so cobaya --resume
# restarts it, (c) repeats until all groups converge (Rhat-1<0.01) or a wall cap.
# Dead/segfaulted chains are tolerated by the no-MPI runner (>=2 survivors) and
# restarted on the next --resume cycle.
#
# Usage:  nohup bash experiments/E1_desi_dr2_repro/rigor_supervisor.sh >runs/E1/rigor_supervisor.log 2>&1 &
# Check:  cat runs/E1/rigor_status.txt   (updated every ~5 min)
# ============================================================================
set +e +u
cd /home/repos/six-birds-de-closure
source scripts/env.sh 2>/dev/null
export PATH=/mnt/data-drive/sbt-de/micromamba/envs/sbt-de/bin:$PATH
export SBT_MAX_CORES=36

GROUPS="C3:lcdm,C5:lcdm,C2:w0wa,C3:w0wa,C4:w0wa,C5:w0wa"
GROUP_DIRS="E1A_C3_lcdm E1A_C5_lcdm E1A_C2_w0wa E1A_C3_w0wa E1A_C4_w0wa E1A_C5_w0wa"
COVMAT=configs/covmats/e1_planck_lcdm.covmat
STATUS=runs/E1/rigor_status.txt
WALL_CAP_H=10
PY=/mnt/data-drive/sbt-de/micromamba/envs/sbt-de/bin/python
start=$(date +%s)

converged_count() {
  local n=0
  for g in $GROUP_DIRS; do
    [ -f "runs/E1/$g/summary.json" ] || continue
    local r=$($PY -c "import json,sys
try:
 s=json.load(open('runs/E1/$g/summary.json')); d=s.get('mcmc',{}).get('diagnostics',{}) or {}
 r=d.get('max_rhat_minus_one'); print('OK' if (r is not None and r<0.01) else 'no')
except Exception: print('no')" 2>/dev/null)
    [ "$r" = "OK" ] && n=$((n+1))
  done
  echo "$n"
}

write_status() {
  { echo "RIGOR-TRACK status @ $(date '+%Y-%m-%d %H:%M')  (full-clik full-fidelity, background)";
    echo "elapsed: $(( ($(date +%s)-start)/60 )) min   wall_cap: ${WALL_CAP_H}h";
    echo "converged groups: $(converged_count)/6   [target Rhat-1<0.01]";
    echo "live chains: $(ps -eo cmd 2>/dev/null|grep 'cobaya-run --packages'|grep -v grep|wc -l)   cores: $(ps -eo %cpu,cmd 2>/dev/null|grep -E 'cobaya-run|run_group\.py'|grep -v grep|awk '{s+=$1}END{printf "%.0f",s/100}')";
    for g in $GROUP_DIRS; do
      rows=$(cat runs/E1/$g/chains/*chain*.txt 2>/dev/null|wc -l)
      r=$($PY -c "import json
try:
 s=json.load(open('runs/E1/$g/summary.json')); print('%.4f'%s['mcmc']['diagnostics']['max_rhat_minus_one'])
except Exception: print('-')" 2>/dev/null)
      echo "  $g: rows=$rows Rhat-1=$r"
    done
  } > "$STATUS" 2>&1
}

# track PIDs that were at ~0% CPU last check, so we only kill SUSTAINED-idle chains
declare -A idle_prev

iter=0
while true; do
  done_n=$(converged_count)
  write_status
  if [ "$done_n" -ge 6 ]; then echo "SUPERVISOR: all 6 groups converged"; write_status; break; fi
  elapsed_h=$(( ($(date +%s)-start)/3600 ))
  if [ "$elapsed_h" -ge "$WALL_CAP_H" ]; then echo "SUPERVISOR: wall cap ${WALL_CAP_H}h reached, stopping"; write_status; break; fi
  iter=$((iter+1))
  echo "SUPERVISOR iter=$iter converged=$done_n/6 elapsed=${elapsed_h}h $(date '+%H:%M')"

  # launch the campaign (resume) in the background
  bash experiments/E1_desi_dr2_repro/launch_campaign.sh \
    --wave all --groups "$GROUPS" --concurrent-groups 2 \
    --omp-threads 3 --max-cores 36 --covmat "$COVMAT" --resume \
    > runs/E1/rigor_track.log 2>&1 &
  LP=$!

  # monitor while the launcher runs; kill chains stuck at ~0% CPU across 2 checks
  while kill -0 "$LP" 2>/dev/null; do
    sleep 300
    write_status
    declare -A idle_now=()
    while read -r pid cpu; do
      [ -z "$pid" ] && continue
      # cpu as integer percent
      ci=${cpu%.*}; [ -z "$ci" ] && ci=0
      if [ "$ci" -lt 3 ]; then
        idle_now[$pid]=1
        if [ -n "${idle_prev[$pid]}" ]; then
          echo "SUPERVISOR: killing hung chain pid=$pid (0% CPU x2) $(date '+%H:%M')"
          kill -9 "$pid" 2>/dev/null
        fi
      fi
    done < <(ps -eo pid,%cpu,cmd 2>/dev/null | grep 'cobaya-run --packages' | grep -v grep | awk '{print $1, $2}')
    idle_prev=()
    for k in "${!idle_now[@]}"; do idle_prev[$k]=1; done
  done
  echo "SUPERVISOR: launcher exited, will re-check convergence + resume if needed"
  sleep 10
done
echo "SUPERVISOR DONE @ $(date '+%Y-%m-%d %H:%M'); see $STATUS"
