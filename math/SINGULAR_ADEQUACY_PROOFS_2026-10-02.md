# Singular-support adequacy mechanization, 2026-10-02

Baseline: `18a0ca2`. This packet closes the previously deferred finite real
singular-native-block and exact-adequacy Lean obligations. The paper is
unchanged. Construction and adversarial review are by the same reviewer.

## Exact original targets and return

The source is `../six-birds-papers/Tsiokos_2026_Adequacy_Residuals_and_Blind_Spot_Currency.tex`,
specifically the projection, optimal-residual, and exact-adequacy theorems.
Their finite-stage spaces are finite-dimensional Hilbert spaces. The repository
reconciliation note applies them on the legal energy quotient, with

```
T_L = L_0 C_0^(-1/2), T_D = D_0 C_0^(-1/2),
K_LL = T_L T_L*, K_DL = T_D T_L*,
Xi = T_D T_D* - K_DL K_LL^dagger K_LD.
```

The new module `lean/SbtCosmo/Adequacy/Support.lean` accepts the actual finite
real whitened matrices L=T_L and D=T_D. It constructs K_LL^dagger from the
spectral theorem and proves:

1. The projection identity and positive semidefiniteness of Xi at every native
   rank, including zero and deficient rank.
2. The complete equivalence
   `Xi=0 iff D=A_* L iff exists A, D=A L iff Ker L subset Ker D`.
3. The optimal-residual identity for every linear explanation A, and its
   Loewner-minimality consequence.
4. Exact return of factorization to unwhitened probes through any supplied
   invertible whitening B, and the original weighted block/error formulas
   when `C_0^(-1)=B B*`.
5. The blind-spot witness equivalence `Xi!=0 iff exists v, L v=0 and D v!=0`.
6. Nonnegative scalar audit energy for W>=0; zero scalar energy detects exact
   adequacy for W>0. Mere semidefiniteness does not ensure this detection.

This preserves the original finite real mathematical claims and strengthens
their mechanization. It does not construct empirical probe families, prove
their null legality, derive a physical gravitational readout, equate a signed
scalar ansatz with a matrix residual, or prove the arbitrary low-rank rewrite
selector exists. Complex and infinite-dimensional versions are not claimed
as new local Lean coverage.

## Construction rather than supplied support identities

For a real Hermitian matrix K, the imported, kernel-checked mathlib spectral
theorem constructs a unitary U and real eigenvalues d with `K=U diag(d) U*`.
Define

```
G = U diag(d_i^(-1)) U*, with 0^(-1)=0.
```

Scalar cancellation with a separate zero-eigenvalue branch proves

```
K G K=K, G K G=G, (K G)*=K G, (G K)*=G K.
```

Lean also proves uniqueness from these four Penrose identities. If H is another
such inverse, `(K G)(K H)=K H` and `(K H)(K G)=K G`; transposing the first
identity gives the same left side as the second, hence K H=K G. The analogous
calculation gives H K=G K. Substitution into H=H K H then gives H=G K G=G.
Thus the construction supplies the actual Moore-Penrose inverse, independently
of the choice of eigenbasis. No inverse existence or target equivalence is
carried as an additional proof field.

Take K=L L*. Set `P=L* G L`. From `K(G K-I)=0`, the Gram null-space identity
gives `L*(G K-I)=0`. Taking adjoints and using G*=G yields K G L=L. Therefore

```
L P=L, P*=P, P²=P, L(I-P)=0.
```

The module additionally proves that P has kernel Ker L and range Ran L*, so
this is the required orthogonal native-support projector, not an arbitrary
idempotent package.

Let `Q=I-P` and `A_*=D L* G`. Expanding the Schur formula gives

```
Xi = D Q D* = (D Q)(D Q)*
   = (D-A_*L)(D-A_*L)*.
```

The last equality is an actual residual Gram identity. Its positivity follows
from a checked Gram-positivity theorem, not a supplied joint-PSD hypothesis.
Gram faithfulness proves Xi=0 iff D=A_*L. Exact factorization implies kernel
containment directly. Conversely, kernel containment and L Q=0 give D Q=0
by applying the containment to every Qv; hence Xi=0. This supplies the full
cycle without assuming the difficult converse in a structure field.

For an arbitrary A, write

```
D-A L = E-F, E=D-A_* L, F=(A-A_*)L.
```

Since E L*=0, both cross Grams vanish. Thus

```
(D-A L)(D-A L)* = Xi + (A-A_*) (L L*) (A-A_*)*.
```

The added term is the Gram of `(A-A_*)L`, hence PSD. This is exactly the
original Loewner-minimum theorem for linear explanation maps. It does not
prove that an unrelated empirical scalar objective selects a least residual
over every allowed nonlinear rewrite.

## Whitening and compatibility

Given unwhitened L_0,D_0 and any invertible B, the theorem
`whitened_exact_adequacy` proves

```
Xi(L_0 B,D_0 B)=0 iff exists A, D_0=A L_0.
```

The return cancels B on the right using its actual inverse. It makes no
assumption that L_0 is invertible. The weighted identities explicitly expose
the factor B B*, so a chosen B must really represent the legal inverse audit
energy before those formulas are identified with C_0^(-1). Construction of the
legal quotient and that empirical whitening remains a separate obligation.

For a positive-definite native Gram, `spectralInverse_eq_inverse` proves that
G equals the genuine matrix inverse. `residual_eq_positiveDefinite` identifies
the new support residual with `Reconciliation.adequacyResidual` on that domain.
The older total ordinary-inverse definition is retained as a positive-definite
convention; it is not silently applied to singular native blocks.

## Scalar audit faithfulness

For W>=0, cyclicity of trace and the residual Gram identity give

```
tr(W Xi) = tr(E* W E) >= 0, with E=D Q.
```

For W>0, zero trace makes the PSD matrix E* W E zero. Its quadratic form at
any v is `(Ev)* W(Ev)`, which is strictly positive if Ev!=0. Hence E=0,
Xi=0, and exact factorization follows. These steps are mechanized.

If W is merely semidefinite, trace zero can hide a nonzero residual. Lean
contains an exact counterexample with W=0, a zero native family, and the
identity target. This does not invalidate the closure-price theorem under its
strict sensitivity hypothesis. It prevents transferring a scalar zero-budget
verdict into an unweighted exact-adequacy conclusion without a faithful weight.

## Boundary examples and verification

The module includes exact kernel-checked calculations for

```
L = [[1,1,0], [2,2,0]],
K = [[2,4], [4,8]],
K^dagger = [[1/50,1/25], [1/25,2/25]].
```

The native Gram is proved singular. D=[3,3,0] has zero residual, whereas
D=[3,3,1] has residual [1]. The example inverse is identified with the spectral
construction through Penrose uniqueness, not numerical agreement. The general
zero-native theorem also verifies the extreme rank-zero case.

The new module adds 42 theorem declarations. The default `SbtCosmoAdequacy`
target includes it. Verification and source hashes are in
`results/singular_adequacy_2026-10-02/verification.json`; the expanded raw axiom
audit is `lean/manifests/axiom_audit_support_2026-10-02.txt`. Historical audits
are retained. These are Lean-only changes; the previously passing Python suite
is historical evidence and was not rerun as a substitute for kernel checking.

The adversarial self-review checks the zero-eigenvalue branch, actual inverse
construction and uniqueness, native range and kernel, rectangular matrix
orientations, positivity of the excess Gram, invertible whitening return,
scalar-weight faithfulness, and genuinely singular examples. The finite
real target is now proved. General convex-duality mechanization, arbitrary
low-rank rewrite selection, and the original physical/value/measure boundaries
remain separate obligations; this packet is not completion of the whole paper.
