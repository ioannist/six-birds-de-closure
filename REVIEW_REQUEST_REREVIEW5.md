# RE-REVIEW (round 5) — Six Birds "Dark Energy as Closure": verify under the LOCKED P4 naming convention

Five review rounds in. Your round-4 review (on the v6 zip) confirmed: **Schur whitening is fixed, DESI RSD
labeling is fixed, E3 F2-attribution is fixed**, and the **P4 three-certificate math is correct**. You
found the repo "internally more coherent than v5." The *only* reason you returned NOT-READY was a
**naming-convention mismatch**: the round-4 prompt criterion (which I, the manager, wrote) demanded
"stable-readout/no-growing-mode = S-stab only" (call it **Option A**), while the repo deliberately adopted
the opposite (**Option B**). You correctly said: *"If the project wants the v6 convention, the review
prompt/contract should be updated."*

**This prompt does that.** Option B is now the LOCKED, canonical convention. The reason for choosing it over
Option A: the names **`G-E8-STABLEREADOUT`** (a locked gate ID, REGISTRY §11.3) and the Lean target
**`PhantomStableReadout`** institutionally bind the word "stable-readout" to the **P4 deliverable**.
Reserving "stable-readout" for the S-stab component alone (Option A) would force renaming a locked gate ID
and a Lean target — a *worse* contract change than the naming question. So the project keeps "stable-readout"
for the deliverable and uses "no-growing-mode" for the stability component.

## THE LOCKED CONVENTION (REGISTRY §11.2 — judge against THIS, not the retired Option A)
- **`stable-readout certificate`** and the boolean **`stable_readout`** = the **FULL P4 pass** = the
  conjunction **P-dens ∧ P-adeq ∧ S-stab**.
- **`no-growing-mode`** and **`S-stab`** = the **stability component ONLY**: `max Re λ(J) ≤ 0` on the
  continuous-generator Jacobian `J` (Gershgorin/Lyapunov `J^*C+CJ ⪯ 0`; discrete one-step map ⇒ spectral
  radius `≤ 1`).
- **`P-dens`** = native-currency density positivity `ρ_eff > 0`.
- **`P-adeq`** = rewrite-operator/adequacy positivity `sym_C(R[Ξ]) ⪰ 0` ↔ Schur `Ξ_C ⪰ 0`.
- **Allowed special cases** (consistent, not defects): (i) E0's toy `stable_readout` records the **subset**
  P-dens ∧ S-stab (P-adeq deferred to E3) — scoped in the text and REGISTRY §11.2; (ii) a gate/manifest that
  **imports** the full E3 certificate and at E8 **re-verifies the S-stab/no-growing-mode component**
  (`max Re λ≤0`) — e.g. `G-E8-STABLEREADOUT`; (iii) the **Lean witness** proving S-stab + crossing (not the
  full bundle) — the numerical P-dens/P-adeq are the E3 checks.

## Manager's pre-submitted evidence (verify or refute)
An exhaustive terminology audit of **all ~22 plan/ops files** classified **195** occurrences of
{stable-readout, stable_readout, no-growing-mode, S-stab, P-dens, P-adeq} against the locked convention:
**0 violations**, 187 consistent, 8 bare-mention "ambiguous" (E0 toy-3 titles/charter + one E5 gate
parenthetical, now clarified). Please independently confirm.

## §A — Verify consistency under the LOCKED convention
1. **No Option-A remnant.** `grep -rn "S-stab" plan/ | grep -i only` and similar — confirm **no file**
   asserts "stable-readout / stable_readout = S-stab only" (the retired Option A). (The round-4 culprit
   `CONTRACT_HARDENING_ADDENDUM.md` ledger has been fixed.)
2. **Bundle vs component used correctly.** Spot-check `REGISTRY.md` §11.2, `04` §6.4 + §7 + `G-FORMAL-14`,
   `E3` §4.1/§4.2 + `G-E3-CONSTRUCT`, `06`, `07`, `E8` `G-E8-STABLEREADOUT`, `GROUNDING_BRIEF`, `01`, `09`,
   `README`: is "stable-readout certificate" used for the **bundle** and "no-growing-mode" for **S-stab**,
   per the convention? Are the three allowed special cases (E0 subset, E8 S-stab re-check, Lean witness)
   each properly **scoped** where they appear?
3. **Carry-over closes.** Re-confirm A.1 Schur whitening, A.2 DESI RSD labeling, and A.4 E3 F2-attribution
   are still closed (they were in round 4).

## §B — New defects?
The round-5 edits (REGISTRY §11.2 wording, addendum ledger, E8/manifest gate clarifications, the E5 gate
parenthetical, the Lean-scope note) are new text. Any new contradiction, broken table, or math error?

## §C — Standing waivers (unchanged): `idea.md:417` source heading; no Lean project yet (packet-0 scaffolds).
Still acceptable?

## Output
Verdict — **READY-TO-EXECUTE / READY-WITH-NITS / NOT-READY** — then:
1. Confirm/refute the manager's audit (0 violations under Option B).
2. Any remaining inconsistency under the **locked convention** (`file:line` + fix). Do **not** re-flag
   "stable-readout = the bundle" as a defect — that is now the canonical, intended convention.
3. Any genuinely new defect.
4. If READY, say so plainly and state that implementation may begin; if NOT-READY, the exhaustive remaining
   list so it closes in one pass.

Context chain: `REVIEW_REQUEST_FINAL.md` (r1) → `REVIEW_REQUEST_REREVIEW.md` (r2) →
`REVIEW_REQUEST_REREVIEW3.md` (r3) → `REVIEW_REQUEST_REREVIEW4.md` (r4, Option-A criterion — **superseded**) →
this is r5 (Option-B locked).
