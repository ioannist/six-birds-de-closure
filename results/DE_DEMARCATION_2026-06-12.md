# Dark Energy in the Six Birds Grammar: the assembled demarcation

**Status: ASSEMBLED RESULT (Legs C1+C2 of the relanding, completed 2026-06-12; WP-DEA battery verdicts integrated).** This document assembles the program's
answer to "explain the mysteries around dark energy" in the genre the SM-QM-GR paper established: not a derivation of a selection from inside its
own layer, but a **proved forced/contingent split** — every mystery assigned a computed grade with can-fail controls, plus falsifiable
discriminators where the structure forces a side. Grounding: `results/DE_DEMARCATION_RELANDING_2026-06-11.md` (the reframe + error review),
the new corpus (`../six-birds-sm-qm-gr/`), and this repo's computed legs (`results/DE_window/`, `results/DE_dual/`, `results/E5SP/`,
`results/DE_audit/` pending).

---

## 0. The one-paragraph answer

Dark energy decomposes under the grammar into a **thin forced skeleton** and **proved-contingent residue**, exactly like the Standard Model does.
**Forced (computed):** the *form* — a constant-slot term that is the shadow price of a global closure budget (one global price over heterogeneous
local allocations; screened from in-layer vacuum-energy shifts by the binding budget, with the multiplier absorbing the shift — the unimodular
reading, computed with must-flip controls in `results/DE_dual/`); the *window* — record-bearing admissibility bounds the Λ-analog strictly and
two-sidedly, with the upper edge at order-unity λ-to-matter ratio (`results/DE_window/`); the *typing* of the two classic paradoxes — the 10¹²⁰
mismatch as a cross-layer route-mismatch (the fork theorem), and the phantom crossing as a chart artifact (an inference-level correction has no
kinetic term to be ghostly). **Contingent (proved, not lamented):** the *value* — F50 bounded-moduli, no in-layer value-law; any claimed in-layer
derivation must smuggle a selection (computed, with the κ-control proving the same audit can constrain what is constrainable). **The named
residue:** the selection/measure predicate (why near the window's top) — required, unspecified, and now precisely located (the E021-P2 slot), with
the record layer as the SBT-native candidate and a broad anthropic landscape *certified non-collapsing* (Cluster B). The empirical tensions (w(z),
H0, S8, duality) are typed as calibrated **audit questions** — rewrite-Λ may show structured staging/probe dependence, fundamental-Λ must not —
with the current-data verdict computed: the calibrated constant-null (the "why ΛCDM works" leg) plus a powered audit that fires on the known SN-vs-BAO dataset tension and names the split that drives it.

---

## 0a. Scope, grades, and provenance (external-review-hardened, 2026-06-12)

Two distinctions govern every claim below; read them first.

**LOCAL (computed + controlled in this repo; the toy legs were independently re-run by the external reviewer — `tests/test_de_window|dual|measure`,
12 passed):** Leg A window (`results/DE_window/`), Leg B dual-recognition (`results/DE_dual/`), Leg C2 real-data audit (`results/DE_audit/`),
the measure probe (`results/DE_measure/`), Claim S (`lean/SbtCosmo/Derivation/ClosurePrice.lean`), and the S8/growth boundary (`results/E5SP/`).

**IMPORTED (load-bearing, from the dependency corpus `../six-birds-sm-qm-gr/`):** the RT = ledger/shadow-price *recognition*, the QM↔GR fork
theorem, the E021 missing-layer card, and the Cluster-B anthropic-landscape-non-collapse result — these *motivate and frame* the local legs; they
are not local proofs, and are tagged **(imported)** below. **PROMOTED (2026-06-12, post-review):** the F50 "Λ-value = bounded-moduli" verdict
(`step54`) has been **vendored with provenance and independently reproduced in this repo** (`results/DE_step54_repro/`) — it is no longer
import-conditional. The audit leg is likewise now **third-party-recomputable without `classy`** (`results/DE_audit_repro/REPRODUCE.md` — the
external reviewer's blocker removed; tests + validator + a B1 smoke re-fit run classy-free and reproduce the frozen χ²).

**Grade vocabulary (and the one thing the value question is NOT).** Results here are at **toy-RECOGNITION / DEMARCATION** grade — the layer-agnostic
*form* recognized and the forced/contingent boundary proved on finite carriers — **not** physical derivation from nature. This is the *maximal honest
grade for the targets*, not a consolation prize: for an **emergent** quantity, "the value is a contingent modulus, not proof-derivable" is the
**proven answer** to the value question (a value born by emergence is constitutively run-only — the corrected reading of the entire magnitude chain,
`results/MAGNITUDE_IS_EMERGENT_NOT_PROVABLE_2026-06-03.md`), **not an open gap to be closed later**. Reading "value unresolved" as unfinished business
is the reductionist framing the program explicitly rejects. **What is NOT claimed:** a derivation of Λ's value; empirical confirmation that dark
energy *is* closure; a refutation of a fundamental Λ. **What IS claimed:** the forced/contingent split, computed and measured, with one residue isolated.

## 1. The nine mysteries, each at its computed grade

### 1.1 The cosmological-constant problem (the 10¹²⁰ mismatch) — **COMPUTE (typed defect)**
The "worst prediction in physics" computes a QM-layer quantity (vacuum energy) and equates it to a GR-layer background term. The fork theorem
(*imported*, `../six-birds-sm-qm-gr` §5.1–5.2: QM and GR are sibling access-quotients of a common refinement; the ladder *fails*; route mismatch is
a typed, finite, non-empty defect) types this identification as a **cross-layer route mismatch** — a booked audit defect, not a paradox. Cluster-B Step 8 sharpens
the factorization: *given* a selected vacuum φ\*, Λ descends (obstruction 0); **what fails to descend is the selector φ\*** (obstruction 4). The
E021 missing-layer card specifies the repair shape: a UV→IR subtraction ledger (P6) booking the ~120-order mismatch as a monotone audit defect
instead of an unaudited cancellation. **Leg-B's computed decoupling is the toy realization of the dissolution**: with a binding global budget, an
in-layer vacuum shift moves the dynamics by nothing (5.7×10⁻¹⁴) and is absorbed exactly into the multiplier (`results/DE_dual/vacuum_shift.csv`),
with a must-flip control (the same coupling unscreened without the budget). **Scope (precise):** this is the *grammar/toy* realization of the
screening pattern — "in a global-budget dual carrier, in-layer offsets are screened while the multiplier absorbs them" — the **same structural
pattern as unimodular gravity's trace-free decoupling**, computed and controlled; it is **not** a proof that real-QFT vacuum energy decouples in
nature. The contribution is the *recognition* that the 10¹²⁰-mismatch dissolves *when Λ is a budget-dual rather than a source*, plus a toy that
realizes it — not a finished derivation of the real decoupling.

### 1.2 Λ's value — **PROVE-BLIND (locally reproduced) + window**
The value verdict rests on **two independent supports** — the F50 sweep, now reproduced in this repo, and a local emergence argument:
- **(reproduced locally, 2026-06-12 — promotion executed)** F50 bounded-moduli (origin `../six-birds-sm-qm-gr` §7.3, `step54`; vendored with a
  sha256+commit provenance manifest into `external/step54_repro/` and **independently re-run and re-derived here** —
  `results/DE_step54_repro/VERDICT.md`: background 15/18 admissible, fails {−5,−3,+10}, degeneracy 15, verdict
  `BOUNDED_MODULI_NO_INLAYER_VALUE_LAW`; κ-control boundary reproduced, passes ≤10 / fails ≥15 — via our own re-derivation script, not the source
  classification code): the background term has a degenerate admissible set — no singleton selector — so **no in-layer value-law exists; any claimed
  in-layer derivation of Λ's value must smuggle a selection.** The κ-control proves the same audit *can* constrain closure-constrained parameters,
  so the blindness verdict is discriminating, not vacuous.
- **(local, independent)** the **run-only / emergence argument**: a value *born by emergence* is constitutively not proof-reducible — the corrected,
  load-bearing reading of our entire magnitude chain (Avenues C/D, topological, criticality, transmutation, LT3), which proved only
  *non-reducibility-by-proof* = the *definition* of emergence, not a shortfall (`results/MAGNITUDE_IS_EMERGENT_NOT_PROVABLE_2026-06-03.md`). This is a
  **local** result and it reaches the **same** conclusion the imported F50 does, by a different route the reductionist read of this leg misses.
Either way Λ's value is classified with N_gen and the EW scale: **irreducibly observed-input** — and the framework's own genre laws (F47/F26)
predicted it in advance. This is not an open gap: it is the **proven character of the quantity**. The in-layer content is the **window** (§1.3).

### 1.3 The coincidence problem ("why now") — **COMPUTE (window) + the located residue**
`results/DE_window/` (WP-DEW): on a record-bearing cosmological carrier with a λ-free record-stability predicate RS (the SM-track predicate
class), the λ-window is **strict** (RS does real selecting work inside bare admissibility), **two-sided** (negative edge: crunch *erases formed
records* — witnessed; positive edge: growth shutoff starves the distinguishable pair — witnessed; both bisected), with the **upper edge at
order-unity λ-to-matter ratio at first-record** (R ≈ 17 max). Typed caveats: the negative edge is horizon-indexed (eternal records forbid λ<0);
the positive edge's *location* is population-dependent (existence + ordering is the content). **The honest negative:** R(λ) spans 7 decades
across the window — the window is an *upper bound* (the Weinberg shape, recovered structurally under a record selector with live controls),
**not** a pinch to order unity. The coincidence problem therefore splits: **[bounded above: COMPUTED] ⊕ [near-top typicality: a measure
question]** — and the measure question is exactly the **E021-P2 selection-predicate slot**: required content the corpus proves is currently
unfilled, with Cluster-B *certifying* that a broad anthropic landscape does not collapse the degeneracy while decaying-degeneracy criteria do.
"Why now" is not answered; it is **located**, with the record layer as the computable, non-anthropic selector candidate.

**The record-measure probe (WP-DEM, `results/DE_measure/` — the frontier probe, executed):** for each preregistered measure class over the RS
window, the induced typicality of R and the collapse criterion (P(top decade) ≥ 0.8 ∧ 90%-width ≤ 1.5 decades, declared in advance):
- **Flat-in-λ classes** (flat dλ; ×N_rec; ×f_coll): P(top decade) = 0.85 / 0.68 / 0.68, width 1.50–1.92 decades, **median a_λ/a_rec = 1.18–1.49
  — a typical record lives essentially *at* λ-domination.** The bare flat-dλ class misses the strict width cut by 0.0023 decades in the base
  run and **flips to collapsing in all three robustness variants** — it sits on the collapse boundary.
- **Flat-in-log-λ classes**: robustly non-collapsing (width 4.4–4.9 decades; median epoch ratio 8–13) — the residue survives there, as
  predicted before running.
- **The demarcation finding:** the typicality work is done by the **prior's linearity in λ** (non-singular density near the top), **not by
  record abundance** — the record weights mildly *broaden* the flat prior and fail to rescue the log prior. And no carrier-native measure was
  defensible without adding new content (declared honestly — itself an E021-P2 finding).
**Net:** the coincidence residue is now *conditionalized precisely*: **typical under prior-linearity-in-λ (epoch ratio ~1), surviving under
log-priors, with the measure choice — sharpened to the single question "is the physical prior over the λ-modulus non-singular near zero?" —
the irreducible E021-P2 content.** That is the known anthropic-measure crux, isolated, with the record-weighting shown not to be load-bearing.

### 1.4 Phantom crossing / ghost problem — **DEMARCATION + forced discriminator**
A *fundamental* field with w < −1 generically needs a wrong-sign kinetic term (ghost). An *inference-level closure correction* `Δ_H(z)` has no
kinetic term — there is no microphysical w to be pathological. The forced discriminator: **apparent crossing is natural for an artifact and
pathological for a substance** — DESI-like crossing *without* ghost instabilities elsewhere is evidence *for* the rewrite chart. **Computed
(WP-DEA B1b, `results/DE_audit/`):** the same best-fit w0wa expansion history (our pipeline's DESI-like preference, ΔAIC −9.6 vs ΛCDM) rendered
in both charts — the fluid chart crosses w = −1 at **z ≈ 0.439**; the additive chart's `Δ_H(z)` is **finite, positive, and regular through the
same redshifts** (range [0.499, 0.760] in E²-units). The crossing is a **chart artifact of forcing the fluid parameterization** — a
representation statement (which chart carries the pathology), not a choice of physical interpretation.

### 1.5 w(z)/DESI evolving dark energy + dataset/duality inconsistencies — **calibrated audit questions**
The pre-registered discriminators (original DE paper §5.5): a packaging-induced correction may show **structured staging/probe-split
dependence**; a fundamental Λ must not (beyond known systematics). Duality-violation claims that mimic evolving w(z) are the lens/calibration
artifact channel of the same audit family. **Computed (WP-DEA B1/B2, `results/DE_audit/`, preregistered + calibrated):**
- **B1 — the calibrated constant-null:** the rewrite family fit through the *same* C3 likelihood as ΛCDM/w0wa (dynesty, identical nuisances)
  gives `m = 0.131 (+0.074/−0.073)` — **constant-compatible**, with ΔAIC = +1.85 vs ΛCDM (pays the Occam penalty). The R025 constraint-null
  reproduced on our own pipeline: **a constant is the rewrite that current geometry lever-arms select — the grammar's account of why ΛCDM
  works.** (Alongside: the proper ΛCDM-vs-w0wa comparison shows the DESI-like mild evolving preference, ΔAIC −9.6 / ΔBIC +1.1 — feeding §1.4.)
- **B2 — the powered staging audit fires, on the right thing:** after fixing the injection class (a globally-injected rewrite shifts all splits
  coherently and is invisible to a cross-split statistic *by construction* — the audit is powered by **probe-localized** injections,
  ε_detect = 0.20 SN-tilt / 0.10 BAO-tilt at TPR ≥ 0.8), the real data exceed the powered null (S = 9.63 > p95 = 8.33), driven by the
  **high-z SN split**, at SN-localized-equivalent ε ≈ 0.2. Disciplined reading: **structured probe dependence consistent with the known mild
  SN-vs-BAO dataset tension — not closure evidence, not a Λ statement.** Mystery #3 (dataset inconsistencies / the duality-mimicking class)
  thereby gets a computed leg: the audit battery detects the literature-known tension and names the split that drives it.

### 1.6 The Hubble tension — **typed: a route-indexed readout (audit protocol demonstrated; tension itself out of scope on-box)**
H0 is a route/lens/staging-indexed readout, not a closure-independent scalar. The grammar's claim is modest and falsifiable: the tension is a
**statused route residual** to be audited (structured route dependence vs systematics), not (yet) evidence of new physics. Our E4 result stands as
the honest boundary: the *signed* route-holonomy version is structurally zero (exact 1-form); the unsigned route-residual protocol is
**demonstrated (WP-DEA B3)** on available routes (SN-only / BAO-only vs joint), statused under the powered probe-localized calibration
(`powered_probe_localized_dataset_tension_audit`) — the same machinery that fired on the SN-vs-BAO tension in §1.5. The SH0ES-vs-Planck tension
itself requires calibrator data we do not hold — typed, not claimed.

### 1.7 S8/growth tension — **done: the banked boundary result**
`results/E5SP/EMPIRICAL_BOUNDARY_RESULT.md`: the growth chart cannot currently bear the decisive closure audit — slack and strong-binding live in
different probe types (support-failure theorem); where the strong-nonlinear regime is observed, the residual is omitted nonlinearity/systematics,
not a closure price (carrier-identifiability NO-GO, anti-vacuity live). This is the growth-chart demarcation, already externally reviewed: the
S8 discourse's probe-dependence is exactly what the audit framework predicts for an under-supported chart.

### 1.8 Interacting dark sector & modified gravity — **DEMARCATION (rival rewrite families)**
Both are typed as **alternative completions/rewrite families repairing the same closure failure**. Their notorious mutual degeneracy (each can
mimic evolving w, shift H0, move S8) is *explained* by rewrite non-uniqueness — the original DE paper's own point ("one may always introduce an
arbitrary Δ_H(z); we agree"). The demarcation: on geometry data the family members are equivalent (the equivalence class is the honest object);
they split only under the audit battery's staging/probe/growth discriminators. No member is privileged without an audit signature — and ΛCDM is
the family's minimal element, which is why it keeps winning information criteria.

### 1.9 The anthropic principle — **replaced by a computable selector question**
F50 proves *some* selection source is required for a value (the moduli verdict); Cluster B *computes* — *(imported, not reproduced here)* — that a
broad anthropic landscape fails to collapse the degeneracy (10→10→…→10, certified) while decaying-degeneracy criteria succeed — so "anthropics" is
demoted (conditional on that import) from explanation to one (non-working, as tested) candidate for the E021-P2 slot. The record-stability predicate is the SBT-native alternative: λ-free, computable,
control-equipped (Leg A), and already load-bearing elsewhere in the grammar (it grounds the SM gauge selection, forbids proton decay, and
classicalizes gravity — the cross-track spine). **The record-measure probe (WP-DEM) has now run this question:** record-*bearing* does real
selecting work (the window), but record-*abundance* weighting is **not** the load-bearing element of coincidence-typicality — the prior's
linearity in λ is (§1.3). The anthropic question is thereby replaced, not by a finished selector, but by its **sharpest computable form**: the
E021-P2 slot reduces to whether the physical prior over the λ-modulus is non-singular near zero. Filling *that* requires content beyond the
current carrier — exactly as F50 demands, and now demonstrated rather than asserted.

---

## 2. The forced skeleton, assembled (what Six Birds positively says dark energy IS)

The statement below is a **grammar-level recognition at toy/recognition grade** — what the layer-agnostic structure *recognizes the constant-slot form
to be*, every clause computed and controlled — **not an ontology claim that nature's dark energy is proven to be this**. Read "is" as "is recognized,
in the grammar, as":

> **Dark energy is the constant-slot shadow price of maintaining a closed global (FLRW-class) description against a binding closure budget.**
> Its *form* is forced by the currency–constraint law (whose gravitational instantiation is Ryu–Takayanagi — *imported recognition*, externally
> settled in `../six-birds-sm-qm-gr` §5.4; it *motivates* this leg, it is not re-proved here):
> one global price over heterogeneous local allocations — hence spatially constant, non-clustering, w = −1-formed; screened from in-layer
> vacuum-energy shifts by the binding budget (the multiplier absorbs them — the unimodular reading, computed); collapsing to zero if the budget
> unbinds (Claim S's active-budget hypothesis, visible). Its *value* is the budget level — proved in-layer-moduli (F50), bounded by the
> record-bearing window (upper edge at order-unity coincidence ratio), with the residual "why near the top" located at the unfilled
> selection-predicate slot. Its *empirical signature space* is the calibrated audit battery; on current geometry data the honest verdict is the
> constant-rewrite null — which is the grammar's account of ΛCDM's success.

Chain of custody for each clause: Claim S (`lean/SbtCosmo/Derivation/ClosurePrice.lean`, Lean-checked witnesses + paper-level theorem) → the
currency–constraint law (`To Spend a Stone`) → its gravitational recognition (RT, `../six-birds-sm-qm-gr` §5.4, externally settled — *imported*) → the
cosmological form leg (`results/DE_dual/`, controls live) → the window leg (`results/DE_window/`, controls live) → the value demarcation
(F50 `step54`) → the audits (`results/DE_audit/`, landed: the calibrated constant-null + the powered probe-dependence audit).

## 3. Falsifiers / discriminators (the skin in the game)
1. **A clean in-layer derivation of Λ's value** (no smuggled selection) falsifies the F50/E021 reading (recorded falsifier of the new corpus).
2. **Structured staging/probe dependence of the inferred correction** (surviving the calibrated false-alarm rate) is evidence for rewrite-Λ;
   its robust absence as lever arms grow keeps fundamental-Λ live (the audits are symmetric — both outcomes are informative).
3. **A confirmed fundamental phantom crossing** (w < −1 with a ghost-free fundamental realization, not chart-relocatable) cuts against the
   artifact reading of §1.4.
4. **A record-measure that collapses the window degeneracy to near the top edge** would complete the coincidence leg; a proof that no admissible
   record-measure does so would close it negatively — both are buildable.
5. The cross-track spine inherits the new paper's falsifiers: a confirmed proton decay or BMV-positive entanglement would damage the record-layer
   grounding this assembly leans on.

## 4. Honest bounds
All carrier results are finite toys (enumeration-strength; no frame transfer); the RT recognition and Leg-B dual are RECOGNITION grade (organize
known structure under one law — the 1/4G coefficient, continuum Einstein equation, and a genuine horizon/de-Sitter treatment are open); the window
edges' *locations* are carrier-indexed (existence/ordering/ratio-at-edge are the content); the battery's expected null means current geometry data
cannot distinguish the readings — the program's empirical content lives in the calibrated audits and the named falsifiers, not in a value. Nothing
here refutes a fundamental Λ (the original paper's scope line stands). The selection-predicate slot is the genuine open frontier, and it is named,
typed, and equipped with one computable candidate.
