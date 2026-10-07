# E1-A full-clik "RIGOR" track — what it is and what to check later

**Status:** background, unattended. **Not** the gate path. Come back to it; do not block on it.

## What this is
The **full-Planck-`clik`** reproduction of E1-A (standard ΛCDM/wCDM/w0waCDM over DESI DR2 BAO +
full Planck + SN), run to confirm **100% alignment with the published DESI DR2 numbers** for the
paper. It is the high-fidelity confirmation of the result that the **compressed-CMB track already
gates** (see below). Outputs: `runs/E1/E1A_<combo>_<model>/` (note the `E1A_` prefix; the compressed
track uses `E1C_`).

## Why it runs in the background (the instability)
The Planck `clik` Fortran likelihood is **unstable on this box** under parallel cobaya chains:
chains intermittently **HANG at ~0% CPU** (rows stop growing) and occasionally **SEGFAULT**. This was
reproduced across three runner designs (chunked, MPI, independent no-MPI) and at both high and low
concurrency. It is a `clik`/threading fragility on this single box, **not** a science problem — the
3 groups that did finish recover the right values (see below).

## What gates E1-A instead (already done / in progress)
The **compressed-CMB track** (`runs/E1/E1C_*`, config `configs/experiments/E1_compressed.yaml`):
classy background-only + Gaussian BAO/SN + Planck 2018 compressed distance priors (Chen-Huang-Wang
2019, arXiv:1808.05724; verified against Table I). Stable, fast, full 60-core use, and free of any
Six-Birds closure-residual machinery (the anti-leakage lint passes on the whole E1-A path).
**That** is what passes `G-E1-REPRO-*`. The rigor track only upgrades those numbers to full-clik
fidelity for the paper's confirmation column.

## How to run / resume it (unattended)
```bash
cd /home/repos/six-birds-de-closure
nohup bash experiments/E1_desi_dr2_repro/rigor_supervisor.sh > runs/E1/rigor_supervisor.log 2>&1 &
```
The supervisor keeps CLASS fast (OMP=3), runs 2 groups concurrently (~24-36 cores), and works around
the hang by killing any chain stuck at ~0% CPU across two 5-min checks so cobaya `--resume` restarts
it. It loops until all 6 remaining groups converge or a **10h wall cap**.

## What to check when you come back
1. `cat runs/E1/rigor_status.txt` — updated every ~5 min: converged groups N/6, per-group rows + R̂−1.
2. `tail runs/E1/rigor_supervisor.log` — supervisor iterations + any hung-chain kills.
3. **Done = all 6 groups `Rhat-1 < 0.01`** with `summary.json` written. The 6 are: C3_lcdm, C5_lcdm,
   C2_w0wa, C3_w0wa, C4_w0wa, C5_w0wa. (Already converged + saved earlier, do NOT rerun: **C1_lcdm,
   C2_lcdm, C4_lcdm** — H0 66.8 / 67.9 / 68.1, R̂−1<0.01.)
4. When all are converged, evaluate the full-clik gates:
   ```bash
   python experiments/E1_desi_dr2_repro/analyze.py   # point at the E1A_* (full-clik) run root
   ```
   and compare to `configs/references/desi_dr2_published.yaml`. Expect tighter agreement than the
   compressed track (this is the full likelihood).

## Honest fallback
If the supervisor hits the 10h wall cap with groups still under-converged, the full-clik rigor track
is **AOR-blocked on this box** (clik instability) and should be statused as such — the paper then
reports the **compressed-track** reproduction as the gate-passing result and notes the full-clik
confirmation is pending a stabler node. **Do not fake or hand-tune any number to force agreement.**

---
## FINAL OUTCOME (recorded 2026-05-31, manager review)
**The supervisor is dead and the track DID NOT complete — statused AOR-BLOCKED (clik instability) per the fallback above.**
Converged 3/9 (full-clik, reliable): `E1A_C1_lcdm` H0=66.84 (~1σ below Planck ref), `E1A_C2_lcdm` H0=67.89,
`E1A_C4_lcdm` H0=68.11 (all R̂−1<0.01). The other 6 (C3/C5 lcdm R̂−1=0.90/0.47; all four w0wa hung at 0% CPU)
never converged — their `summary.json` is from non-converged chains and must NOT be used. The compressed-track
(`E1C_*`) reproduction remains the gate-passing E1-A result; the full-clik confirmation is partial + pending a
stabler node. Under the 2026-05-31 REPLAN, E1/E2 are FROZEN — this confirmation is no longer on the critical path.
See `runs/E1/rigor_status.txt` (FINAL).
