# Xi_cosmo vs. Schur Adequacy Residual: Reconciliation Note

Status: R1 math note and Lean-mechanization plan. No Lean implementation is
included in this packet.

Review update (2026-10-01): the current Lean implementation corrects the
P-adeq coordinate convention to `C * symC C R = U^* Xi U`, with `C > 0`.
This is a sufficient invertible congruence realization of the quadratic
form, not an assertion that `symC C R` itself is Euclidean PSD or that `U`
is an isometry. The finite native Gram joint PSD is now derived rather
than supplied. Singular Moore-Penrose support calculus remains an imported
mathematical result, with no local full mechanization.

Support extension (2026-10-02): `lean/SbtCosmo/Adequacy/Support.lean` now
constructs the finite real Moore-Penrose inverse and proves the full projection,
optimal-residual, and exact-adequacy statements, including singular native
rank, with an explicit invertible-whitening return. See
[`SINGULAR_ADEQUACY_PROOFS_2026-10-02.md`](SINGULAR_ADEQUACY_PROOFS_2026-10-02.md).
The deferred references below describe the original mechanization plan;
empirical whitening, legal quotient construction, and nonlinear rewrite
selection remain separate obligations.

Authoritative inputs checked:

- `plan/04-formal-foundations.md` Sections 1, 3.1, 3.2, 6.1, 6.2, 7, 9.1.
- `plan/CONTRACT_HARDENING_ADDENDUM.md` Sections 2, 3, 4, 6, 7.
- `docs/papers/Tsiokos_2026_Adequacy_Residuals_and_Blind_Spot_Currency.tex`,
  especially `def:xi:adequacy-residual`,
  `thm:xi:projection-identity`,
  `thm:xi:optimal-residual-identity`,
  `thm:xi:exact-adequacy`,
  `thm:xi:chain-rule`, the data-processing laws, and
  `thm:xi:blind-spot-witness`.
- `docs/papers/Tsiokos_2026_Emergence_IS_the_Needle_Killer.tex`,
  especially `thm:main:adequacy-interface` and the formed-layer membrane
  Schur-interface discussion.
- `docs/papers/Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex`,
  especially `thm:F2` and `thm:F11`.

## 0. The Question and the Answer

Question. Reconcile the program phrase "`Xi_cosmo` is the least
audit-closed rewrite" with the corpus adequacy residual
`Xi_C(D | L) = K_DD - K_DL K_LL^dagger K_LD`. Is `Xi_cosmo` itself an
adequacy residual between probe families, or is it a distinct rewrite
operator `Delta` that drives that residual to budget?

Answer. The theorem-grade object is the Schur adequacy residual
`Xi_C(D | L)`: it is the leftover content that the native FLRW/GR probe
family `L` cannot explain about the enriched/dissolving probe family `D`.
The repair is distinct: `Delta_SBT` is the admissible low-rank rewrite
coordinate, and `R[Delta_SBT]` is the operator applied to the macro readout.
The project should therefore use `Xi_cosmo` for the cosmological residual
content, sector-by-sector represented by `Xi_C(D | L)` or by its shared
low-rank residual coordinates, and reserve `Delta_SBT` / `R[Delta_SBT]` for
the repair. The equivalence between the empirical four-residual audit cost and
the Schur energy of that content is per-sector numerical/conditional `[C]`,
not an unconditional theorem. In exact adequacy, `Xi_C(D | L)=0`, the zero
rewrite is selected, so a native FLRW/Lambda account is not ruled out.

## 1. Definitions

### 1.1 Legal quotient and Schur residual

Let `E` be the carrier space for a fixed finite probe sector and let
`C=C^* >= 0` be the audit energy. The corpus first removes zero-audit
directions:

```text
E_C = (Ker C)^perp,       C_0 = C restricted to E_C,       C_0 > 0.
```

A probe family `F:E -> Y` is null-legal when it vanishes on `Ker C`; then
`F_0:F|E_C -> Y` is its legal restriction. All Schur statements below are read
on this legal quotient.

For native and dissolving probe families

```text
L:E -> Y_native,          D:E -> Z_dissolving,
```

the corpus block currencies are

```text
K_LL = L_0 C_0^{-1} L_0^*
K_DL = D_0 C_0^{-1} L_0^*
K_LD = K_DL^*
K_DD = D_0 C_0^{-1} D_0^*.
```

The adequacy residual is the Schur complement

```text
Xi_C(D | L) = K_DD - K_DL K_LL^dagger K_LD.
```

This is the residual/diagnostic, not the rewrite.

Per `CONTRACT_HARDENING_ADDENDUM.md` Section 2, experiment-sector matrices use
the un-whitened data-design convention. If `L_p` and `D_p` are un-whitened
predictor matrices in observation coordinates and `C_p = Sigma_p^{-1}`, then

```text
K_LL = L_p^* C_p L_p
K_DD = D_p^* C_p D_p
K_DL = D_p^* C_p L_p
K_LD = K_DL^*.
```

This is the same Schur construction with adjoints oriented by the data matrix
convention. The rule is strict: either use un-whitened `L_p,D_p` and insert
`C_p` once, or pre-whiten to `C_p^{1/2}L_p,C_p^{1/2}D_p` and then use ordinary
Gram blocks. Do not do both.

### 1.2 Low-rank residual coordinates and rewrite

The admissible residual-coordinate class is the low-rank ansatz `A` from
`plan/04` Section 3.1:

```text
Xi_cosmo(z, ell, p)
  = a_0 phi_0(z)
  + a_1 phi_1(z) psi_1(ell) s_p
  + a_2 phi_2(z) c_p
```

with fixed shared shapes and only the declared small set of coefficients free.
These coordinates parameterize the residual content seen by the sector Schur
blocks. They are not arbitrary per-probe functions.

This is an intended representation, not an established equality for the Python
`XiCosmo.evaluate` function. That function returns a signed scalar basis ansatz;
it neither constructs these probe families and Gram blocks nor proves a
Schur-realization identity. A scalar coordinate may be signed even when its
represented matrix is PSD, but the coordinate-to-matrix map must be supplied
and verified before transferring the matrix positivity theorem.

The rewrite is the macro correction

```text
rho_eff(z) = rho_FLRW(z; theta) + R[Delta](z),
```

where `Delta in A` is the coefficient vector/operator parameter and `R[Delta]`
is linear in those coefficients for fixed basis shapes. The least repair is
selected by the audit objective

```text
Delta_SBT = argmin_Delta [
  sum_p RM_p(Delta)
  + sum_{p,q} LG_{p,q}(Delta)
  + sum_{p,q} PPD_{p -> q}(Delta)
  + lambda complexity(Delta)
].
```

For theorem statements below, the clean mathematical form is the constrained
version:

```text
F_Omega = { Delta in A | Xi_C(D_Delta | L) <=_L Omega },
```

where `<=_L` is Loewner order and `D_Delta` is the residual dissolving readout
after applying `R[Delta]`. Among feasible repairs, choose a Loewner-minimal
post-rewrite residual, or the least element if one exists, and then the
least-complex representative inside that minimal stratum. The scalar objective
above is the implemented numerical surrogate for this constrained selection;
its equivalence to the Schur-energy audit is `[C]` sector by sector.

### 1.3 C-adjoint and symmetrized rewrite

On the legal macro state space with `C>0`, define

```text
<x,y>_C = x^* C y,
R^{dagger_C} = C^{-1} R^* C,
sym_C(R) = (R + R^{dagger_C}) / 2.
```

`sym_C(R) >=_C 0` means

```text
<x, sym_C(R) x>_C >= 0        for every legal x.
```

The P-adeq certificate concerns this C-symmetric part only. It is a positivity
certificate; it is not the S-stab/no-growing-mode stability certificate.

## 2. Theorem-Grade Results

### Theorem 1 [T]: Schur residual positivity

Statement. Under the corpus legal-quotient and null-legality hypotheses,

```text
Xi_C(D | L) = T_D (I - P_L) T_D^* >= 0,
```

where

```text
T_L = L_0 C_0^{-1/2},
T_D = D_0 C_0^{-1/2},
```

and `P_L` is the orthogonal projection onto `Ran(T_L^*)`.

Proof. The corpus projection theorem expands the block currencies as

```text
K_LL = T_L T_L^*
K_DD = T_D T_D^*
K_DL = T_D T_L^*
K_LD = T_L T_D^*.
```

The Moore-Penrose projection identity gives

```text
T_L^* (T_L T_L^*)^dagger T_L = P_L.
```

Therefore

```text
K_DL K_LL^dagger K_LD
  = T_D T_L^* (T_L T_L^*)^dagger T_L T_D^*
  = T_D P_L T_D^*.
```

Substitution into the Schur definition gives

```text
Xi_C(D | L)
  = T_D T_D^* - T_D P_L T_D^*
  = T_D (I - P_L) T_D^*.
```

For every vector `z` in the dissolving response space,

```text
z^* Xi_C(D | L) z
  = ((I-P_L)T_D^*z)^* ((I-P_L)T_D^*z)
  >= 0,
```

because `I-P_L` is an orthogonal projection. Hence
`Xi_C(D | L) >= 0`.

Lean-positive-definite variant. If `K_LL` is positive definite, so that
`K_LL^{-1}` is a genuine inverse, and the joint block matrix

```text
[ K_LL  K_LD
  K_DL  K_DD ]
```

is positive semidefinite, then the ordinary Schur complement

```text
K_DD - K_DL K_LL^{-1} K_LD
```

is positive semidefinite. For any `z`, set
`y = -K_LL^{-1}K_LD z`; the joint PSD inequality for `(y,z)` reduces exactly
to `z^*(K_DD - K_DL K_LL^{-1}K_LD)z >= 0`. This is the finite matrix case R2
should mechanize first.

What is imported. The projection identity itself is
`thm:xi:projection-identity` in
`Tsiokos_2026_Adequacy_Residuals_and_Blind_Spot_Currency.tex`. The
positive-definite Schur-complement proof above is elementary and is the
appropriate Lean T3 core.

### Theorem 2 [T, corpus exact-adequacy anchor]: zero residual iff native exact adequacy

Statement. On the legal quotient,

```text
Xi_C(D | L) = 0
  iff D_0 = A_* L_0
  iff exists A, D_0 = A L_0
  iff Ker L_0 subset Ker D_0,
```

where `A_* = K_DL K_LL^dagger`.

Proof. The full four-way equivalence is the corpus theorem
`thm:xi:exact-adequacy`. The easy implications are direct:

1. `D_0 = A_*L_0` implies `exists A, D_0=AL_0` by taking `A=A_*`.
2. If `D_0=AL_0` and `v in Ker L_0`, then `D_0 v = A L_0 v = 0`; hence
   `Ker L_0 subset Ker D_0`.

The hard implications use the optimal residual identity and the finite
Douglas/Fillmore-Williams factorization criterion:

```text
(D_0 - A L_0) C_0^{-1} (D_0 - A L_0)^*
  = Xi_C(D | L) + (A-A_*) K_LL (A-A_*)^*.
```

If `Xi_C=0`, applying this at `A=A_*` forces `D_0=A_*L_0`. Conversely,
kernel containment gives a factorization `D_0=AL_0`; substituting that
factorization into the optimal residual identity makes the left side zero, and
both right-side summands are PSD, so `Xi_C=0`.

Rewrite consequence. Define "no dark-energy rewrite needed" in the exact
audit sense as:

```text
0 in A, complexity(0)=0,
J(0)=0, and the zero-budget exact audit is closed by Delta=0.
```

Then

```text
Xi_C(D | L)=0
  iff exists A, D_0=AL_0
  iff Delta_SBT=0 in the exact-audit/no-rewrite-needed sense.
```

The forward direction is: if `Xi_C=0`, native FLRW already explains the
dissolving family, and the zero rewrite has zero residual cost and zero
complexity. To conclude that the selector actually returns zero, additionally
require nonnegative audit and complexity costs and either strictly positive
complexity for every nonzero rewrite or a declared preference for zero among
tied minimizers. Otherwise zero is an available minimizer, not necessarily
the selected one. The reverse direction is:
if the selected zero rewrite closes the exact audit, the post-rewrite
dissolving residual is just the native Schur residual, so it must be zero.

Important delimitation. If the declared residual budget is nonzero, `Delta=0`
can be acceptable with `Xi_C(D | L) <=_L Omega` rather than `Xi_C=0`. The
exact equivalence above is the zero-budget/exact-adequacy statement. This is
the formal reason the program does not rule out a fundamental Lambda: when the
native FLRW/Lambda lens is exactly adequate, no SBT dark-energy rewrite is
called for.

### Theorem 3 [T under Schur-realization hypothesis]: P-adeq link

Statement. Let `V_C` be the legal macro state Hilbert space with the
`C`-inner product, and let `Z` be the dissolving residual response space.
Assume the rewrite is Schur-realized by an order isomorphism

```text
U : V_C -> Z
```

meaning `U` is unitary from `<,>_C` to the response inner product and the
C-symmetric rewrite part is the pullback of the Schur residual:

```text
<x, sym_C(R[Delta]) y>_C = <U x, Xi_C(D | L) U y>_Z
```

for all legal `x,y`. Equivalently, in C-orthonormal coordinates,

```text
sym_C(R[Delta]) = U^{-1} Xi_C(D | L) U.
```

In original coordinates the quadratic-form identity is
`C sym_C(R[Delta]) = U^* Xi_C(D|L) U`; if `U` is the stated isometry,
then `U^*U=C`. An arbitrary invertible `U` with the first identity suffices
for the positivity equivalence, even without the isometry condition.

Then

```text
sym_C(R[Delta]) >=_C 0    iff    Xi_C(D | L) >= 0.
```

Proof. For any legal `x`,

```text
<x, sym_C(R[Delta]) x>_C
  = <Ux, Xi_C(D | L) Ux>_Z.
```

If `Xi_C(D | L) >= 0`, the right-hand side is nonnegative for all `x`, so
`sym_C(R[Delta]) >=_C 0`. Conversely, if `sym_C(R[Delta]) >=_C 0` and `U` is
onto, every `z in Z` is `Ux` for some `x`; hence

```text
<z, Xi_C(D | L) z>_Z
  = <x, sym_C(R[Delta]) x>_C
  >= 0.
```

Thus the two PSD statements are equivalent.

Scope. This theorem is not true for an arbitrary additive operator `R`. The
equivalence is the definition and proof obligation of a legal Schur-realized
rewrite chart. If the empirical implementation supplies only an injective
transport into a represented subspace, then `Xi_C >= 0` implies positivity of
the represented symmetric rewrite, but the converse holds only on that
represented subspace. The full P-adeq equivalence used in the P4 certificate
therefore requires the recorded `U`/coordinate realization to be
order-reflecting.

Since Theorem 1 gives `Xi_C(D | L) >= 0`, a Schur-realized rewrite
automatically passes the P-adeq positivity certificate. This remains distinct
from S-stab: no-growing-mode stability is an eigenvalue/Lyapunov/Gershgorin
condition on the continuous-generator Jacobian, not a consequence of PSD
adequacy positivity.

### Theorem 4 [T as a selection theorem; [C] for empirical surrogate]: minimal rewrite

Statement. For a fixed finite sector and an exact Schur-realized rewrite
family, define

```text
Xi_Delta = Xi_C(D_Delta | L)
F_Omega = { Delta in A | Xi_Delta <=_L Omega }.
```

If `F_Omega` is nonempty and `Delta_SBT` is chosen by the two-stage rule

1. choose a Loewner-minimal `Xi_Delta` among feasible `Delta`, or the least
   element if one exists;
2. among feasible repairs with that selected minimal residual, minimize
   `complexity(Delta)`;

then `Delta_SBT` is Loewner-/complexity-minimal among audit-closing rewrites.

Proof. Loewner order is only a partial order, so the theorem asserts
minimality rather than uniqueness unless the feasible residuals have a least
element. The first clause is exactly the first-stage selection rule: no
feasible repair has a strictly smaller post-rewrite residual than the selected
minimal residual. The second clause is the definition of the tie-break on that
minimal stratum. If `A` is finite, existence is immediate. If `A` is compact
and the residual map and complexity functional are continuous/lower
semicontinuous, existence follows by the usual finite-dimensional compactness
argument.

Corpus relation. For each fixed `Delta`, the residual `Xi_C(D_Delta | L)` is
itself Loewner-minimal among linear native explanation maps by
`thm:xi:optimal-residual-identity`:

```text
(D_Delta - A L_0) C_0^{-1} (D_Delta - A L_0)^*
  = Xi_C(D_Delta | L)
    + (A-A_*) K_LL (A-A_*)^*.
```

Thus the Schur part is not a chosen fudge residual. It is the forced leftover
after the best native explanation. The rewrite selection then searches the
declared low-rank class `A` for the least repair that brings that forced
leftover inside budget.

Delimitation. The implemented scalar objective

```text
sum RM + sum LG + sum PPD + lambda complexity
```

is theorem-equivalent to the two-stage Schur rule only if the sector audit
costs are proven to be the Schur quadratic energies and the scalarization is
order-reflecting on the feasible set. In this project that equivalence is
currently a per-sector numerical reconciliation `[C]`, not a theorem.

## 3. What Remains Conditional `[C]`

The identity

```text
per-sector audit cost J_p(Delta)
  = Schur energy of the residual readout after whitening
```

is not theorem-grade for real data in the current contract. It depends on:

- the empirical `L_p,D_p,C_p` matrices for the sector;
- nuisance marginalization and shared-nuisance handling;
- the declared forward/microstate model for `widehat{RM}_p` on real data;
- finite data covariances and whitening choices;
- the equality between the scalar residual batteries `RM/LG/PPD` and the
  Schur quadratic form in the selected residual coordinates.

Therefore the composite reconciliation

```text
"least audit rewrite" = "Schur residual energy closed to budget"
```

is `[C]` recognition-grade and must be reported sector by sector with

```text
|| Xi_C^{(p)} - audit_cost_p ||
```

and the achieved tolerance. The target is `<1%` relative by
`G-FORMAL-3`; failure to reach it is not a theorem failure but is statused
`budgeted` with the achieved residual.

To lift one sector from `[C]` to `[T]`, R2/R3 would need an exact finite
definition of that sector's residual readout, covariance, nuisance
marginalization, and audit functionals, followed by an algebraic proof that
the resulting `J_p` is the same quadratic form as the Schur energy. For real
survey data this is generally an empirical-estimator statement, so `[C]` is
the honest grade.

## 4. F2 and F11 Grounding

F2 grounding. Foundations IV `thm:F2` states Descent-Repair Normal Form:
`r o F` descends through `q` iff the split-pair obstruction is empty; when it
is nonempty, the canonical repairs are exactly source refinement and minimal
target coarsening. The operator rewrite `R[Delta_SBT]` is not a third repair
inside F2. In this cosmology program it is the P1 operator-rewrite extension
used after the route-mismatch obstruction has been identified: F2 supplies the
descent obstruction and its two canonical structural repairs, while the SBT
rewrite chart is the cosmology-specific branch for repairing the failed FLRW
macro readout.

F11 grounding. Foundations IV `thm:F11` says an accepted exact current-layer
claim must factor through the access quotient. Applied here, the Schur
residual prevents overreading enriched/dissolving probe content as if native
FLRW already had access to it: native claims must factor through the
cosmological access quotient, and any QFT-vacuum-to-cosmological-Lambda
identification requires an explicit bridge. The Schur residual is the priced
leftover after native access is exhausted; it does not license an
unbridged cross-layer identification.

## 5. Lean T3 Mechanization Plan

Target namespace/file for R2:

```text
lean/SbtCosmo/Adequacy/Reconciliation.lean
namespace SbtCosmo.Adequacy.Reconciliation
```

The existing R0 scaffold remains mathlib-free. T3 genuinely needs mathlib:
finite matrices, adjoints, positive semidefinite/positive definite matrices,
Loewner order, inverses, and eventually orthogonal projections or inner-product
space machinery. R2 should add mathlib explicitly and pin it through
`lake-manifest.json` under the existing Lean `v4.28.0` toolchain, preferably
using the mathlib `v4.28.0` tag or the resolved compatible commit recorded by
Lake. There should be no fallback to Lean 4.30.0.

Recommended R2 dependency shape:

```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"
```

then run `lake update` so the concrete commit is recorded in
`lean/lake-manifest.json`.

### Lemmas and grades

1. `BlockCurrencyPD`
   - Data: finite matrices `KLL KLD KDL KDD` over `R` or `C`, with `KLL`
     positive definite and the joint block PSD.
   - Grade: `faithful`.
   - Mathlib: required.

2. `schur_complement_psd_of_joint_psd`
   - Statement: if `KLL` is positive definite and the joint block is PSD, then
     `KDD - KDL * KLL^{-1} * KLD` is PSD.
   - Proof route: quadratic-form proof with `y = -KLL^{-1}KLD z`, or an
     existing mathlib Schur-complement lemma if available.
   - Grade: `faithful`.
   - This is the first Lean T3 theorem.

3. `projection_identity_packaged`
   - Statement: under exposed hypotheses identifying
     `KLL=T_L*T_L^*`, `KDD=T_D*T_D^*`, `KDL=T_D*T_L^*`, and
     `P_L=T_L^*(T_LT_L^*)^dagger T_L`, prove
     `Xi = T_D(I-P_L)T_D^*` and PSD.
   - Grade: `faithful` for the packaged algebraic statement; full
     square-root/projection construction may be `narrowed_surrogate` if
     postponed.
   - Mathlib: required.

4. `exact_adequacy_easy_chain`
   - Statement: `D_0=A_*L_0 -> exists A, D_0=AL_0 -> Ker L_0 subset Ker D_0`.
   - Grade: `faithful`.
   - Mathlib: linear algebra required but not spectral machinery.

5. `exact_adequacy_full`
   - Statement: the four-way exact-adequacy equivalence.
   - Grade for R2: `narrowed_surrogate`, unless R2 also proves the finite
     Douglas/factorization direction in mathlib. The note imports the full
     theorem from the corpus paper; Lean should not pretend to have proved the
     hard directions unless they are actually discharged.

6. `cAdjoint`, `symC`, `schur_realized_rewrite`
   - Define C-adjoint and C-symmetric part for `C` positive definite.
   - Define a structure carrying the order-isomorphism/unitary realization
     `U` and the equality `sym_C(R)=U^{-1}Xi U`.
   - Grade: definitions, no claim.
   - Mathlib: required.

7. `p_adeq_iff_xi_psd`
   - Statement: for a Schur-realized rewrite with order-isomorphism `U`,
     `sym_C(R) >=_C 0 iff Xi >= 0`.
   - Grade: `faithful` under the realization hypothesis.
   - Scope note: for injective non-surjective `U`, mechanize only implication
     or subspace equivalence.

8. `zero_xi_iff_zero_rewrite_exact_budget`
   - Statement: if the exact-audit objective has nonnegative residual cost,
     `complexity(0)=0`, and zero repair closes exactly iff post-rewrite
     residual is zero, then `Xi=0 iff Delta_SBT=0` in the exact-audit sense.
   - Grade: `faithful` for the abstract optimization record; empirical
     identification of `J_p` with Schur energy remains `[C]`.
   - Mathlib: may be mathlib-free if formulated over an abstract preorder and
     nonnegative cost, but T3 will already import mathlib.

9. `minimal_rewrite_selection`
   - Statement: the two-stage argmin rule returns a Loewner-/complexity-minimal
     feasible repair.
   - Grade: `faithful` as a selection theorem over finite `A`; `[C]` if tied
     to the empirical scalar objective.

10. `per_sector_reconciliation_witness`
    - Not a theorem. R2 should define the expected JSON/CSV witness fields or
      a Lean-side record shape only if useful:
      `sector`, dimensions, `min_eig_Xi`, `audit_cost`, `schur_energy`,
      relative error, status.
    - Grade: `[C] numerical witness`.

### T3 build discipline

R2 must keep `lake build` green under Lean `v4.28.0`, with no `sorry`,
`admit`, local `axiom`, `opaque`, or `constant`. If mathlib resolution fails,
stop and report; do not silently remove mathlib or fall back to another Lean
version. The mathlib-free R0 modules should remain no-claim scaffolds until
their packets arrive.

## 6. Final Reconciliation Contract

The rigorous contract is:

```text
Xi_C(D | L)      = theorem-grade Schur residual / leftover content.
Xi_cosmo         = cosmological residual content, represented sector-by-sector
                   by Xi_C and globally by the shared low-rank coordinates.
Delta_SBT        = selected low-rank repair coordinate.
R[Delta_SBT]     = macro rewrite operator induced by the repair.
```

The theorem-grade relation is:

```text
Xi_C(D | L) >= 0,
Xi_C(D | L)=0 iff D_0 factors through L_0,
Schur-realized sym_C(R[Delta]) >= 0 iff Xi_C(D | L) >= 0.
```

The conditional empirical relation is:

```text
sum(RM, LG, PPD) for sector p
  ~= Schur energy of the post-rewrite residual readout
```

with the stated numerical tolerance and AOR status. This is the point at which
the program moves from theorem-grade algebra to recognition-grade empirical
reconciliation.
