# LT3 Endpoint Memo: Canonical Terminal Rung `j*` Theorem-or-Counterexample

> **Mathematical review correction (2026-10-01):** the finite counterexample
> below does refute determination of the stated cap by the stated six Boolean
> channels. It does not refute determination from a full presentation, and it
> does not establish that a run constructs a canonical endpoint. The previous
> interpretive preface identifying this with Cantor strict extension and
> claiming that proof cannot reach run-produced content was unsupported.
> A proof can formalize a finite run; a no-shortcut or no-descent theorem needs
> an explicitly restricted observer, input record, or resource model.

Status: endpoint-only theory assessment memo. No Lean, data, plan, or
results changes.

Governing inputs:

- `math/DERIVATION_TRANSMUTATION_F4_2026-06-02.md`.
- `plan/EXTERNAL_RULING_TRANSMUTATION_2026-06-03.md`.
- `results/DARK_ENERGY_AS_CLOSURE_RESULT_2026-06-02.md`.

## 0. Verdict

**Outcome B: no canonical endpoint in the current primitives.**

There is a clean finite counterexample. Two admissible presentations of the
same finite underlying system can have the same six-channel SBT record at the
P1--P6 bookkeeping level, while their no-ladder terminal caps differ:

```text
Presentation A: |im(f_A)| = 1,  |Def(f_A)| = 2.
Presentation B: |im(f_B)| = 2,  |Def(f_B)| = 4.
```

Both presentations have:

```text
P1: update descends;
P2: finite representability/gating passes;
P3: route mismatch zero;
P4: fixed finite bounded-interface staging active;
P5: quotient saturation idempotent;
P6: finite audit passes.
```

The terminal cap

```text
j*_cap(f) := |Def(f)| = 2^{|im(f)|}
```

is therefore not a function of the six-channel record alone. It depends on
presentation/host data, specifically the chosen lens granularity
`|im(f)|`. If one enriches the record to include the full lens or its
cardinality, then the two records are no longer identical; that enrichment is
precisely new endpoint data, not a consequence of the six primitives alone.

Thus the current corpus cannot fix the endpoint `j*`. The endpoint knob is
real. Native transmutation remains PARTIAL: form fixed, coefficient and
endpoint free.

## 1. Defining the Terminal Rung

The packet gives three candidate meanings of `j*`. Only one is both
structural and non-vacuous enough to test a canonical endpoint theorem.

### 1.1 Idempotent-Saturation Stage

For a fixed deterministic packaging operator `e`, the no-go theorem records:

```text
e o e = e  =>  e^n = e for all n >= 1.
```

This is canonical in the trivial sense that a fixed idempotent saturates after
one application. But it is not the terminal rung of a P4 running ladder. It
says repeated application of the same package does not run. If we defined

```text
j*_idem = 1,
```

then outcome A would be true but vacuous: it would kill transmutation rather
than terminate it after a meaningful staged run. This is not the endpoint
needed by Route E.

### 1.2 Enablement-Birth Stage

To Notch uses a prediction gap

```text
gap = max(NLL_1 - NLL_2, 0)
```

and births a richer theory when the gap exceeds a threshold. This is the
right enablement shape, but the threshold is part of the audit/laboratory
design. Therefore

```text
j*_birth(theta) = first j with gap_j > theta
```

is not canonical unless `theta` is itself structurally fixed. The current
corpus does not fix it.

### 1.3 No-Ladder Cap Stage: Target Chosen

The strongest threshold-free candidate is the no-ladder cap inside a fixed
finite interface.

For a deterministic interface

```text
f : X -> Y,
```

the No-Go paper defines

```text
Def(f) = { g o f : X -> {0,1} | g : Y -> {0,1} }.
```

It proves

```text
|Def(f)| = 2^{|im(f)|}.
```

Thus no infinite strictly increasing ladder of definable predicates can live
inside the fixed interface. The cardinal terminal cap is:

```text
j*_cap(f) := |Def(f)| = 2^{|im(f)|}.
```

This is the target of the counterexample. It is the best candidate for A
because it is threshold-free and comes directly from no-ladder machinery.

Remark. If one asks for the sharp maximum length of a nested inclusion chain
of definable predicates, the cap is `|im(f)|+1` rather than `2^{|im(f)|}`.
That sharper cap also depends on `|im(f)|`, so the counterexample below
works for either convention. I use the No-Go paper's cardinal bound because
it is the corpus-native statement.

## 2. Presentation-Invariance Test

### 2.1 Admissible Presentation

For this memo, an admissible finite presentation is a finite FATCD-style SBT
description carrying:

- a finite substrate `Z`;
- a deterministic update `F : Z -> Z`;
- a deterministic interface/lens `f : Z -> Y`;
- the quotient/package saturation induced by `f`;
- a finite audit record;
- six role-channel statuses satisfying the exact-six bookkeeping discipline.

This is deliberately modest: it is exactly the finite deterministic setting
used by the no-ladder front and compatible with Foundations II's admissibility
architecture.

### 2.2 Six-Channel Record Identity

The relevant record for the endpoint theorem is the six-channel SBT
bookkeeping record, not the entire presentation. Write it as

```text
R_6(P) =
  (P1 status/witness summary,
   P2 status/witness summary,
   P3 status/witness summary,
   P4 status/witness summary,
   P5 status/witness summary,
   P6 status/witness summary).
```

For the counterexample, the shared record is:

| channel | shared record |
|---|---|
| P1 | Update descends through the quotient; no rewrite obstruction. |
| P2 | Finite representable macro interface; gate passes. |
| P3 | Route mismatch diagnostic exists and is zero. |
| P4 | Fixed finite bounded-interface staging record; no stage failure. |
| P5 | Quotient saturation/package is idempotent. |
| P6 | Finite audit/provenance record passes; no budget violation. |

This record intentionally does not include the full lens cardinality
`|im(f)|`. If that cardinality is added to P4/P5/P6 as a new field, then the
record is no longer merely the six-channel bookkeeping record; it has been
enriched with endpoint-relevant host data. That enrichment is allowed in a
future theorem, but it is not forced by P1--P6.

This distinction is exactly the Foundations II/III warning:

- selected lifts are non-unique;
- lower-level content does not determine structural-categorical content;
- cross-level comparison needs explicit bridge data;
- BirdInt cells are profile-relative and host-bound;
- primitive labels are not a total algebra that decodes quantitative status.

### 2.3 The Two Presentations

Let the underlying system be the same in both presentations:

```text
Z = {0,1,2,3}
F = id_Z.
```

Presentation A uses the one-block lens:

```text
Y_A = {*}
f_A(z) = *  for all z in Z.
```

Presentation B uses the two-block lens:

```text
Y_B = {0,1}
f_B(0)=0, f_B(1)=0, f_B(2)=1, f_B(3)=1.
```

Both are finite deterministic interfaces on the same underlying dynamics.

### 2.4 Admissibility Check

**P1.** Since `F=id_Z`, if `f(z)=f(z')` then

```text
f(F(z)) = f(z) = f(z') = f(F(z')).
```

So the update descends through both quotients.

**P2.** Both macro interfaces are finite images of a finite substrate. The
macro states are representable.

**P3.** The two standard routes commute because the update is identity:

```text
f o F = f = F^sharp o f.
```

Thus route mismatch is zero in both presentations.

**P4.** Both presentations have a fixed finite bounded interface. Taking the
same bounded-interface witness `C_0=2` covers both images at the initial
stage, and the fixed-interface no-ladder theorem applies to each.

**P5.** The saturation operator induced by either quotient is idempotent:
once a predicate is saturated on fibers of `f`, saturating again changes
nothing.

**P6.** The finite audit record passes: all checks above are finite and
replayable, no nonzero mismatch or budget violation is present.

Therefore both presentations are admissible and carry the same six-channel
record `R_6`.

### 2.5 Different Terminal Caps

For Presentation A,

```text
|im(f_A)| = 1,
|Def(f_A)| = 2^1 = 2.
```

For Presentation B,

```text
|im(f_B)| = 2,
|Def(f_B)| = 2^2 = 4.
```

Hence

```text
j*_cap(P_A) = 2,
j*_cap(P_B) = 4.
```

The same conclusion holds with the sharp nested-chain cap:

```text
j*_chain(P_A) = 2,
j*_chain(P_B) = 3.
```

Thus `j*` differs while the six-channel records match.

### 2.6 Consequence

The endpoint is not record-invariant:

```text
R_6(P_A) = R_6(P_B)
but
j*(P_A) != j*(P_B).
```

Therefore no theorem can compute `j*` from the current P1--P6 bookkeeping
record alone. The endpoint lives in lens/presentation/host data below the
resolution of the six-channel record.

## 3. No Free Threshold

The counterexample uses no fitted threshold. It is based only on the
fixed-interface no-ladder cap:

```text
j*_cap(f) = |Def(f)|.
```

This makes the negative result stronger. Even the threshold-free structural
candidate is not presentation-invariant. The enablement-birth version is
weaker for outcome A because it has the explicit threshold knob `theta`.

Thus the result is not:

```text
theta differs, so j* differs.
```

It is:

```text
the no-ladder cap itself differs under admissible presentations with the same
six-channel record.
```

## 4. Anti-Tautology and Scope

This counterexample does not smuggle the dark-energy answer. It does not use
`10^-120`, `Omega_Lambda`, `H_0`, a hidden volume `399`, or an IR cutoff. It
uses only a four-point finite substrate and two ordinary quotient lenses.

The presentations differ in lens granularity. That is not a cheat; it is the
point. Foundations II explicitly says lower-level content does not force a
unique selected lift, and Foundations III says directed-cell status is
profile-relative and host-bound. If a future version of the theory wants the
endpoint to be canonical, it must add a rule selecting the lens/granularity or
include endpoint-relevant cardinal data in the record.

There is a strong-record caveat:

```text
If "identical record" is strengthened to mean identical full FATCD/BirdInt
presentation including the complete lens f and its cardinality, then this
counterexample no longer has identical records.
```

But that strengthened notion makes the endpoint data part of the record. It
does not prove that P1--P6 determine `j*`; it proves only that `j*` can be
read after the presentation has already supplied the lens. The question in
Route E is whether current SBT primitives fix the endpoint without adding
such presentation data. They do not.

## 5. Verdict and What Remains

Outcome B is established at the paper-math level:

```text
two admissible presentations;
same underlying finite system;
same six-channel P1--P6 record;
different threshold-free no-ladder terminal cap.
```

Consequence:

```text
current primitives cannot fix j*.
```

The native transmutation route remains:

```text
form fixed;
beta coefficient free;
endpoint j* free.
```

This closes the endpoint gate negatively. The dark-energy magnitude needs new
structure: a canonical lens/granularity selector, a structural endpoint field
in the BirdInt record, or a theorem that selected lifts satisfying additional
constraints all produce the same endpoint. None is present in the current
corpus.

Lean status. I did not add Lean in this packet. A small finite formalization
is straightforward but would mechanize only the toy forgetting map, not the
paper-level admissibility claim. A faithful Lean follow-up should define:

```text
structure SixRecord
def cap(K : Nat) := 2^K
two presentations with the same SixRecord and K=1, K=2
theorem same_record_different_cap : ...
```

The mathematical content that matters here is the paper-level scoping: the
six-channel record forgets endpoint-relevant lens cardinality unless the
record is explicitly enriched.

## References

- `math/DERIVATION_TRANSMUTATION_F4_2026-06-02.md`: native
  transmutation PARTIAL, with `j*` isolated as a remaining knob.
- `plan/EXTERNAL_RULING_TRANSMUTATION_2026-06-03.md`: reviewer ruling naming
  endpoint as the single surgical probe.
- `docs/papers/Tsiokos_2026_Six_Birds_No_Go_Theorems_for_Audited_Emergence.tex`:
  idempotent no-ladder, bounded-interface no-ladder, `|Def(f)|=2^{|im(f)|}`,
  extension escape by changing the interface.
- `docs/papers/Tsiokos_2026_Six_Birds_Foundations_of_Emergence_Calculus.tex`:
  idempotence defect, closure saturation, bounded-interface `C_0`.
- `docs/papers/Tsiokos_2026_Six_Birds_Foundations_II_Admissibility_Meta_Theory_and_the_Exact_Six_Program.tex`:
  selected-lift non-uniqueness, lower-to-higher non-determinacy,
  level-profile architecture, scoped exact-six.
- `docs/papers/Tsiokos_2026_Six_Birds_Foundations_III_A_Finite_Audited_Interaction_Calculus_for_SBT.tex`:
  BirdInt profile-relative typed records, no total six-symbol algebra,
  host-bound model realizations.
- `docs/papers/Tsiokos_2026_To_Notch_a_Stone_with_Six_Birds_Time_as_a_Theory_Artifact_of_Order_Measure_and_Arrow.tex`:
  enablement-birth threshold and why it is not threshold-free.
- `docs/papers/Tsiokos_2026_Adequacy_Residuals_and_Blind_Spot_Currency.tex`:
  staged residual recurrence that a terminal endpoint would have to stop.
