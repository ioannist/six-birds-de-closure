# Actual positive-ground and Step26 Jacobians, 2026-10-03

Baseline: `0dc7f85`. Adversarial self-review by one reviewer, not independent
review. The paper, original runtime, frozen results, earlier proofs and prior
receipts are unchanged. The analytical derivative obligation now returns to
arbitrary backgrounds, including the original nonconstant template; this is
not a substituted constant-background stability theorem.

## Earned linearization and existing-selector return

For the original eight-site Hamiltonian H_v, let g(v) be the existing constructed
positive unit ground vector and e(v) its ground energy. The normalized eigen
equation is

```
F(v,(u,e))=((H_v-eI)u, (sum_i u_i^2-1)/2)=0.
```

Its exact derivative with respect to (u,e) is the bordered operator

```
B_(v,g,e)(w,eta)=((H_v-eI)w-eta*g, sum_i g_i*w_i).
```

The kernel is trivial. Symmetry and normalization force eta=0; the previous
proved simplicity of the actual lowest eigenspace forces w=c*g; the second
border equation then forces c=0. Finite dimension earns surjectivity, so the
inverse is constructed. No inverse, spectral gap, differentiability, eigenbasis
or stability is supplied as a premise.

The full polynomial equation and its exact derivative are mechanized. The
Mathlib implicit-function theorem is applied to the earned invertible partial
derivative. Crucially, the resulting branch is returned to the EXISTING selector:
its continuous graph satisfies F=0, and local implicit uniqueness identifies
it with the implicit branch. This proves g(v) and e(v) are C-infinity at EVERY
real potential v, including nonconstant v. No global uniform gap or analyticity
is inferred, and excited eigenvalue multiplicities cause no difficulty.

For a perturbation h of v, the actual selector derivative is the first component
of

```
B_(v,g,e)^(-1) (-diag(g)*h,0).
```

The derivative, tangency and differentiated full eigen equation are proved,
and the normalized linear system has a unique solution. This is a construction
of the derivative of the actual selector, not a theorem assuming that derivative.

## Actual quadratic sourcing and normalized iteration

The unchanged source potential is

```
v_b,k(u)[i]=b[i]+k*((gradient u[i])^2+b[i]*u[i]^2).
```

Its C-infinity regularity and exact derivative

```
dv[h][i]=2k*((gradient u)[i]*(gradient h)[i]+b[i]*u[i]*h[i])
```

are proved for every real background, coupling and field. Composing the earned
source and selector derivatives constructs the actual real positive-representative
ground-map Jacobian J. Every output derivative is tangent to the selected unit
ground field, and the full differentiated eigen equation returns to unchanged
sourcing. No supplied nonlinear fixed point or computed Jacobian is needed for
this derivative theorem.

At an actual unit fixed point u=g(v_b,k(u)), the derivative of normalization is
`P_u h=h-u*(sum_i u_i*h_i)`. The exact normalized affine-relaxation derivative is

```
P_u [(1-m)I+mJ].
```

For tangent h, tangency of J at the fixed point earns the exact return
`(1-m)h+mJh`. Consequently any actual real tangent eigenmode with eigenvalue t
has normalized multiplier1-m+mt. The eigenmode condition is an explicit legitimate
hypothesis; no numerical eigenmode or spectral crossing is constructed here.

The prior all-background/all-coupling Brouwer construction supplies positive
actual fixed points and their normalized derivatives for every b,k,m. This
existential result does not identify the branch found by a numerical continuation
or prove stability/convergence. The zero-coupling control changes the actual
source: its ground map is constant, its J is zero, and the normalized tangent
multiplier is1-m for every actual background, including nonconstant ones.

## Exact original-target boundary

The mathematical map selects the positive real representative. All formulas
hold for that declared real map. Its interpretation as the source's phase-aligned
iteration is local to positive real fields; an arbitrary signed or complex input
can use a different phase representative. No original complex-initialization
run, erroneous complex phase-sign rule, historical floating diagonalization or
finite-budget trace is silently replaced by these mathematical derivatives.

This closes the earned nonconstant-selector/source/normalization derivative
obligation. Certification of numerical fixed-point branches and their spectral
bounds remains open. Smoothness of the linear ground selector does not imply
uniqueness or smooth continuation of nonlinear self-consistent branches.
The old numerical diagnostics are historical evidence, not a fresh rerun or
interval certificate: at half mixing they report radius0.9116 at k=15 and1.4305
at k=20 on the declared positive continuation branch. Those estimates do not
restore the paper's k>=15 runaway interpretation; its finite-budget separation
must remain distinguished from a stability or nonexistence boundary.

No stability verdict, physical Lambda bridge, background blindness or unrestricted
selector impossibility is inferred. No new downgrade of supported claims is
made. The full original-target goal remains incomplete.

## Verification

Five new roots add51 theorems. Full `lake build` passes8187 jobs with warnings
as errors. All51 exported statements and transitive standard-only axiom
closures are freshly checked. Cumulative1644 retains the exact immutable1593
prefix and appends51 fresh closures; the full cumulative command is not rerun.
Previous proof-source/toolchain identity, original Step26 source pin, direct
implicit-function/derivative source hashes and exported domains are checked by
`scripts/de_ground_jacobian_verify.py`. Receipts are in
`results/ground_jacobian_2026-10-03/`. Only trailing whitespace in the build
receipt is normalized; the old replayed informational tactic message is retained.
