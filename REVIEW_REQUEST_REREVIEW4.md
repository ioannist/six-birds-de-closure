# RE-REVIEW (round 4) — Six Birds "Dark Energy as Closure": is the propagation finally complete?

Three prior reviews → NOT-READY each time, but the defect set has shrunk every round to **propagation
tails** (the same correct fix not reaching every sibling file). Round 3 flagged: (a) Schur whitening
contradiction in `04` vs the addendum; (b) DESI `2411.12026` still mislabeled "DR2 full-shape" primary in
several files; (c) P4's three-certificate contract not fully propagated; plus nits (E3 F2-attribution,
addendum SN-whitening typo, E0 P-adeq scope). A fourth remediation pass has been applied. Decide whether the
propagation is now **complete** and re-issue a verdict.

Static review only; a fresh full-repo zip is provided. The round-3 ledger is in
`plan/CONTRACT_HARDENING_ADDENDUM.md` §8 ("Round 2" table covers rounds 2–3 fixes). Your job is a
**completeness grep**, not a re-derivation (the round-3 math — Q_Ξ sign, three certificates — was already
verified correct). Confirm or refute, with `file:line`:

## §A — Did the round-3 fixes reach EVERY site?
1. **Schur whitening.** `grep -n "whitened" plan/04-formal-foundations.md plan/CONTRACT_HARDENING_ADDENDUM.md`.
   Is the convention now uniformly **un-whitened `(L,D)` with `C=Σ⁻¹` entering once via `K=L*CL`**, the
   residual `d`-metric the only thing in whitened coords? Is the addendum §1 SN row whitening now
   `C_SN^{1/2}=Σ_SN^{−1/2}` (not `Σ^{1/2}`)? Any remaining double-whitening?
2. **DESI RSD label.** `grep -rn "DR2 full-shape" plan/`. Should appear **only** at `03:55` as the
   release-name, explicitly tagged "DR1 … NOT a DR2 data product". Confirm every execution-facing file
   (E5 ×3, E6, E7 ×3, E8, 00, 01, 02, 03) now states **DR2 compressed `fσ₈` = primary; DR1 full-shape
   `2411.12026` = method/MG-reproduction control**. Any "DR2 full-shape" as a primary data product left?
3. **P4 three certificates (P-dens ∧ P-adeq ∧ S-stab).** Confirm **all** of `REGISTRY` §11.2, `04` §6.4 +
   `G-FORMAL-14`, `E3` §4.1/§4.2 + `G-E3-CONSTRUCT`, `06`, `01:163`, `09:280`, `GROUNDING_BRIEF`, `README`
   name the **three** certificates and that "stable-readout/no-growing-mode" denotes **S-stab only** (not the
   bundle). Confirm E0 explicitly scopes itself to P-dens + S-stab with P-adeq deferred to E1/E3 (a
   single-sector toy). Is `06`'s `lambda_min_sym` retained as the **P-adeq** field (correct) rather than a
   stale stability test?
4. **E3 F2-attribution.** `grep -rn "operator-rewrite repair" plan/`. Confirm no file calls the operator
   rewrite an **F2 repair/branch**; everywhere it must be **P1's cosmology extension of F2** (F2 = source
   refinement + minimal target coarsening only). Were `E3:117` and `E3:602` fixed?

## §B — New defects from this round?
The Schur prose rewrite (`04`), the P4 three-cert edits across 8 files, the E0 scope note, and the DESI
relabels are all new text. Any new math error, broken table, or contradiction with `REGISTRY`/addendum?

## §C — Standing waivers (unchanged): `idea.md:417` source heading; no Lean project yet (packet-0 scaffolds).
Still acceptable?

## Output
Verdict — **READY-TO-EXECUTE / READY-WITH-NITS / NOT-READY** — then:
1. A **completeness table** for §A.1–§A.4: *fully-propagated / still-incomplete* with `file:line`.
2. Any **new defect** (severity + `file:line` + fix).
3. If NOT-READY, the **exhaustive** list of every remaining site (so it can be closed in one pass, not
   another round). If READY, say so plainly and state that implementation may begin.

Context chain: `REVIEW_REQUEST_FINAL.md` (r1) → `REVIEW_REQUEST_REREVIEW.md` (r2) →
`REVIEW_REQUEST_REREVIEW3.md` (r3) → this is r4.
