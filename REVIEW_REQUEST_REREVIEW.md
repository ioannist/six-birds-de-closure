# RE-REVIEW — Six Birds "Dark Energy as Closure": did the NOT-READY blockers actually close?

You previously reviewed this repository and returned **NOT-READY**, with a prioritized list of 20 findings
(6 blockers, 12 majors, 2 minors), a §4 contract sweep, a §5 completeness table, a §6 implementation-risk
register, and one "single highest-value improvement" (a `CONTRACT_HARDENING_ADDENDUM.md`). This is the
**re-review**: a remediation pass has been applied. Your job is to decide whether the blockers are genuinely
closed and to re-issue a verdict — **not** to rubber-stamp. Be at least as skeptical as last time.

This is a static blueprint/harness review. Do **not** run experiments, build, fit, or prove anything. You
have a fresh zip of the entire repository; unzip and grep freely.

## How the remediation was done (so you can audit it, not trust it)
The manager (a) ran an independent read-only verification pass over your findings, **and** (b) re-derived the
physics personally. Notably, on **four findings the manager OVERRODE its own verification pass**, which had
wrongly called them false-positive: **#3 (w_eff sign), #4 (P4 positivity≠stability), #5 (P1 biconditional),
#10 (IDE continuity)**. The manager fixed them anyway. **You must independently re-derive these four and
confirm the *new text is correct*, not merely "changed".** If the manager's re-derivation is itself wrong,
say so — this is the single most important thing to check.

The complete change ledger is in **`plan/CONTRACT_HARDENING_ADDENDUM.md` §8** (file → finding → change). Start
there, then verify against the actual files. Where any file disagrees with the addendum on the items it
covers, the addendum is intended to win (and `REGISTRY.md` wins over both on items it covers).

## §A — Re-derive the contested physics fixes (spend the most effort here)
For each, ignore the prose and check the math from scratch:
- **#3 `w_eff`** (`GROUNDING_BRIEF.md:107`, `04` eq. 19, `E3` eq. E3.1, `CONTRACT_HARDENING_ADDENDUM.md` §6):
  is `w_eff = −1 + ((1+z)/3)·d/dz[ln ρ_eff]` (≡ `−1 − (1/3)·d ln ρ_eff/d ln a`) now the **single** form used
  everywhere? Does it pass the sanity checks (const ρ ⇒ −1; ρ∝(1+z)³ ⇒ 0)? Any file still carrying the old
  sign?
- **#4 P4** (`04` §6.4 proof step 2, `G-FORMAL-14`, ADDENDUM §4): are the **two certificates** — (a)
  native-currency positivity `ρ_eff>0` and (b) dynamical stability `Re λ ≤ 0` (Lyapunov `J*C+CJ ⪯ 0`) — now
  correctly stated as a **conjunction, not an equivalence**? Is the claim that a `C`-PSD operator implies
  *instability* (growing energy) correct as written? Is the continuous-generator vs discrete-map criterion
  (`Re λ ≤ 0` vs spectral radius `≤ 1`) handled? Does the Lean target (T5, `05`) match?
- **#5 P1** (`04` §6.1, `G-FORMAL-11`, ADDENDUM §6): is the biconditional now correctly split into the
  unconditional direction (`RM_p>0 ⇒ splitObs≠∅`) and the converse under **(H-faithful)** (faithful readout +
  nondegenerate legal-quotient metric)? Is (H-faithful) the right/sufficient hypothesis?
- **#10 IDE** (`GROUNDING_BRIEF.md:205`, ADDENDUM §6, vs `E6`): are the continuity equations now
  `ρ̇_DE + 3H(1+w_DE)ρ_DE = −Q`, `ρ̇_dm + 3H ρ_dm = +Q` (with the `(1+w_DE)` factor and correct conversion)?

## §B — Verify the remaining blockers/majors actually closed (and PROPAGATED)
Propagation has historically been the failure mode — check every site, not just the one cited.
- **#8 (within-3% = pass):** confirm no OOS gate anywhere treats "within 3%" as a pass; E1 `G-E1-SBT-OOS` now
  scores it a tie. (It was the lone straggler — verify it's gone and nothing regressed.)
- **#9 (E2 30%→20%):** confirm the rewrite/mixture boundary is `0.2`/`20%` in **all** of `E2` §8.4/§8.6,
  `07-pass-fail-gates.md`, `00-overview.md`, and `GROUNDING_BRIEF.md` — and consistent with REGISTRY §11.9.
- **#11 (SPT key):** confirm the **primary** SPT-3G D1 power-spectrum data product is now `arXiv:2506.20707`
  (with 2018 = `2212.05642`) in **all** files (`03`, `02`, `00`, `E8`), and that `2601.16277` survives **only**
  as the neutrino-mass *framing* reference. Is 2506.20707 in fact the correct D1 TT/TE/EE release?
- **#12 (DESI_RSD_FS):** is the compressed `fσ8`+geometry now the **default/primary** leg (not a degraded
  fallback), with the DR1 paper demoted to a method control?
- **#16 (T3 inverse):** does the Lean `BlockCurrency` now require `K_LL` **PosDef** (so `(K_LL)⁻¹` is the
  genuine inverse), with the singular/Moore–Penrose case explicitly deferred to paper-proof?
- **#18 (determinism):** does `G-E1-REPRO-DET` now distinguish deterministic forward-eval (`<1e-12`) from
  MAP/sampler tolerance from statistical chain equivalence, per REGISTRY §2.1?
- **#1 (residuals):** is the theoretical-vs-empirical split (`RM_p` vs `\widehat{RM}_p` needing a declared
  forward model on real data) now explicit (`04` §4 caveat + ADDENDUM §3)?
- **#7 (E4 Planck-collapse):** does the E4 pass criterion now reward *mismatch reduction* (std + holonomy)
  rather than convergence to the Planck value?

## §C — Scrutinize the NEW addendum as fresh attack surface
`CONTRACT_HARDENING_ADDENDUM.md` is new (≈250 lines) and therefore unreviewed. Check it for *new* defects:
- §1 observable dictionary & §2 Schur realization: are the per-sector `(L_p, D_p, C_p, K-blocks)` shapes and
  the whitening/pseudoinverse conventions correct and internally consistent? Are the stated target dimensions
  (`n_p`, `m_p`) plausible and compatible with `G-FORMAL-4`'s rank ceiling?
- §4 P4, §5 Hubble bridges, §6 formulas index, §7 coherence normalization: any new math error, over-claim, or
  contradiction with `04`/`REGISTRY`? Is the §7 "shared-basis dimensionless amplitude" actually well-defined
  and normalization-invariant, or does it smuggle in a hidden scale choice?
- Does the addendum contradict `REGISTRY.md` anywhere (it must not — REGISTRY wins on items it covers)?

## §D — Confirm the two deliberately-unfixed items are acceptable
- **#19** `idea.md:417` "phantom crossing without ghosts" was **not** edited because `idea.md` is the user's
  source program, not a plan deliverable; the plan/ops forbidden-token sweep is claimed clean. Verify that
  claim (grep plan/ + ops/), and judge whether leaving the source heading is acceptable.
- **#20** No Lean project exists yet; `ops/bootstrap/ralph.md` makes Lean scaffold + green `lake build` the
  mandatory packet-0. Acceptable as scheduled, or a blocker?

## §E — Re-run your §4 / §5 / §6
- Repeat the §4 forbidden-token / threshold sweep on the *current* tree (it should now be clean except the
  flagged `idea.md` source heading).
- Update the §5 completeness table for the items that moved.
- Update the §6 implementation-risk register: which of your original top risks (Schur dictionary, Hubble
  bridges, real-CCL E5, DESI reproduction, P4-trivial, coherence-gate, OOS-non-decisive) are *reduced* by this
  remediation, and which are untouched (correctly, since they are runtime risks, not blueprint defects)?

## Output
A fresh overall verdict — **READY-TO-EXECUTE / READY-WITH-NITS / NOT-READY** — then:
1. **Per-finding closure table** (your 20 findings + the 2 sweep items): for each — *closed-correctly* /
   *closed-but-fix-is-wrong* / *not-closed* / *correctly-waived* — with `file:line` evidence.
2. **§A verdict**: are the four overridden physics fixes (#3,4,5,10) mathematically correct as now written?
   (If any is still wrong, that is a blocker.)
3. **New defects introduced by the remediation or the addendum** (severity + `file:line` + fix), if any.
4. The refreshed §4 sweep, §5 completeness delta, and §6 risk register.
5. The single highest-value remaining improvement before kickoff (if any).

For context, the prior review prompt is `REVIEW_REQUEST_FINAL.md` (round 1) and your verdict drove this
remediation; this file (`REVIEW_REQUEST_REREVIEW.md`) is round 2.
