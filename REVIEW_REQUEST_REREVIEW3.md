# RE-REVIEW (round 3) — Six Birds "Dark Energy as Closure": did the round-2 NOT-READY items close?

You reviewed this repository twice. Round 1 → **NOT-READY** (20 findings). After remediation, round 2 →
**NOT-READY** again, with **four load-bearing issues** plus several nits. This is round 3: a second
remediation pass has been applied to exactly the round-2 issues. Decide whether they are genuinely closed
and re-issue a verdict — **not** a rubber-stamp. The round-2 fixes were *propagation-heavy* (the recurring
failure mode), so check **every** site, and treat the **new three-certificate P4 framing** as fresh,
unreviewed attack surface.

Static review only: do **not** run experiments, build, fit, or prove. A fresh full-repo zip is provided;
unzip and grep freely. The complete round-2 change ledger is in **`plan/CONTRACT_HARDENING_ADDENDUM.md` §8
("Round 2")** — start there, then verify against the files. Where a file disagrees with the addendum on the
items it covers, the addendum wins (REGISTRY wins over both on items it covers).

## §A — The four round-2 blockers/majors: closed correctly, and propagated?

**1. P4 stability propagation (was the #1 blocker).** Round 2 introduced an explicit **three-certificate**
model — **P-dens** (`ρ_eff>0`), **P-adeq** (rewrite-operator/adequacy positivity `sym_C(R[Ξ]) ⪰ 0` ↔ Schur
`Ξ_C ⪰ 0`), **S-stab** (dynamical stability `Re λ(J) ≤ 0` on the *continuous-generator* Jacobian `J`).
Verify, from scratch:
- Is the three-way split **mathematically correct**? In particular: (a) is P-adeq (a PSD *positivity*
  certificate on the rewrite operator) genuinely **distinct** from S-stab (no growing mode), and is it
  legitimate to keep it as a separate certificate rather than a bug? (b) Is the **continuous-generator**
  declaration (`Re λ(J) ≤ 0`; discrete one-step map ⇒ spectral radius `≤ 1`) now consistent **everywhere**?
- Check **all** P4 sites agree with `CONTRACT_HARDENING_ADDENDUM.md` §4: `REGISTRY.md` §11.2, `04` §6.4 +
  `G-FORMAL-14`, `E0` §6(ii), `E3` §4.1/§4.2 + `G-E3-CONSTRUCT`, `06-results-manifest.md` (`stable_readout`,
  `lambda_min_sym`, `max_Re_eig`). Is the old "operator PSD = stability" bundling gone from REGISTRY? Is the
  "discrete map + `Re λ≤0`" and "wrong-sign kinetic term" language gone (except as negation/literature)?
- The remediation argued `06`'s `lambda_min_sym` is the **legitimate P-adeq field** (not a stale stability
  test) and kept it. Do you agree, or is it still wrong?

**2. Schur double-whitening (was a blocker).** Round 2 fixed `CONTRACT_HARDENING_ADDENDUM.md` §1–§2 to the
**un-whitened** convention: `(L_p,D_p)` un-whitened, `C_p=Σ_p⁻¹` enters once via `K = L_p^* C_p L_p` (matching
`04` §1.2′). Confirm there is **no** remaining "L,D are C-whitened" *and* "K=L*CL" double-count, and that the
residual `d`-metric (whitened coords) vs the Schur blocks (un-whitened L,D + C) are now clearly one
convention applied once.

**3. E6 `Q_Ξ` sign (was a major).** Round 2 changed (E6-5) to `Q_Ξ = +(1+z)H·R′(z) − 3H(1+w_eff)R` and added
a locked derivation + sign-sanity test. **Re-derive it yourself** from `ρ̇ + 3H(1+w)ρ = −Q` with
`ρ̇ = −(1+z)H·R′`. Is the leading sign now correct? Does the sanity test (`R=R₀(1+z)`, `w=−1` ⇒ `Q>0`,
DE losing) hold?

**4. DESI_RSD_FS propagation (was a major).** Round 2 made the **DR2 compressed `fσ₈`** the primary RSD/growth
leg and demoted DR1 full-shape `arXiv:2411.12026` to a method/MG-reproduction control. The remediation found
the mislabel was **broader** than round 2 cited and also corrected `E5` (two rows + the arXiv-anchor footer),
`02`, `00`, `03`, and a second E7 table row (`E7` §·, the "PRIME" data row). Verify: does **any** file still
present `2411.12026` / "DESI DR2 full-shape" as the *primary RSD data product* (vs. the `(μ₀,Σ₀)`
reproduction reference, which is legitimately DR1)? Is `03:55`'s release-name usage (tagged "DR1 … NOT a DR2
data product") acceptable?

## §B — The round-2 nits: closed?
- **P1 biconditional** propagated: `E7` §· and `06` F-5 now state `RM_p>0 ⇒ splitObs≠∅` unconditionally, the
  biconditional only under **(H-faithful)** (matching `04` §6.1)? Any bare `splitObs≠∅ ⇔ RM_p>0` left?
- **Coherence-amplitude invariance** (`CONTRACT_HARDENING_ADDENDUM.md` §7): reworded from "manifestly
  invariant to per-kernel rescaling" to "invariant once the basis/whitening are frozen (recorded in the
  manifest)". Is the claim now correct (no hidden scale freedom)?
- **Lyapunov adjoint notation**: `J*C+CJ → J^*C+CJ` (with `J^*` defined) in `04` §6.4 and addendum §4?
- **E2 p-value**: the "η-shape uncorrelated" *failure* is now `p>0.05` in `00` E2 row and `GROUNDING_BRIEF`
  (matching `E2` `G-E2-SHAPE`)?
- **RM_p wording** (`04` §4.2): "computed from data" now routed through the declared forward/microstate
  model (estimator `\widehat{RM}_p`)?

## §C — Did the remediation introduce any NEW defect?
The three-certificate P4 text, the Schur convention rewrite, the E6 derivation block, and the reworded E5/E7
data rows are all new prose. Check them for any new math error, mislabel, or contradiction with `REGISTRY`/
`04`. Does the addendum §8 "Round 2" ledger accurately describe what changed?

## §D — Standing waivers (unchanged): still acceptable?
- `idea.md:417` "phantom crossing without ghosts" — user's source program, not a deliverable; plan/ops sweep
  clean. Acceptable?
- No Lean project yet — `ops/bootstrap/ralph.md` packet-0 scaffolds it before any T1–T7. Acceptable?

## Output
Fresh verdict — **READY-TO-EXECUTE / READY-WITH-NITS / NOT-READY** — then:
1. A **closure table** for the four round-2 issues + the five nits: *closed-correctly / closed-but-wrong /
   not-closed*, with `file:line` evidence.
2. **§A re-derivations**: is the three-certificate P4 model correct, and is the E6 `Q_Ξ` sign now right?
3. Any **new defect** introduced by this round (severity + `file:line` + fix).
4. A refreshed §4 contract sweep + §6 risk-register delta.
5. The single highest-value remaining improvement before kickoff (if any) — or an explicit statement that
   none remain and implementation may begin.

Context: round-1 prompt = `REVIEW_REQUEST_FINAL.md`; round-2 prompt = `REVIEW_REQUEST_REREVIEW.md`; this is
round 3 (`REVIEW_REQUEST_REREVIEW3.md`).
