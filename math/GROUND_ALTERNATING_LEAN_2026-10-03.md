# Actual Step26 alternating-slice iteration, 2026-10-03

Baseline: `0912889`. Adversarial self-review by one reviewer; not independent
review. The paper, original runtime, frozen results, previous proofs and prior
receipts are unchanged. This is a constructive local dynamical result within
the unchanged eight-site model, not a replacement background template for the
historical run.

## Exact original mechanism and earned selector

For the actual periodic Hamiltonian

```
H_v u[i]=(1+v[i])*u[i]-(u[i-1]+u[i+1])/2,
v_b,k(u)[i]=b+k*((gradient u[i])^2+b*u[i]^2),
```

restrict to constant background b and positive alternating unit fields

```
u(p)=[a,o,a,o,a,o,a,o],
a=sqrt((1+p)/8), o=sqrt((1-p)/8), -1<p<1.
```

The actual central gradient vanishes on this slice. The potential becomes
`[c+d,c-d,...]`, where c=b+kb/8 and d=kbp/8. Its constructed positive unit
ground vector has odd/even amplitude ratio `sqrt(1+d^2)+d`, eigenvalue
`1+c-sqrt(1+d^2)` and density contrast

```
q(p)=-d/sqrt(1+d^2).
```

Positivity, normalization and the full eight-site eigen equation are proved.
Symmetry and positive overlap with the previously constructed positive ground
prove that this eigenvalue is the actual lowest eigenvalue, rather than assuming
that an eigenvector is a ground state. Actual positive-ground uniqueness then
identifies the intrinsic selector with this vector. Its contrast lies strictly
in(-1,1), and its field is exactly u(q(p)). No supplied derivative, spectral
mode, Jacobian, nonlinear fixed point or floating solution is used.

## Native normalized mixing and iteration

Mix actual fields as `(1-m)u(p)+m*u(q(p))`, then apply the original Euclidean
normalization. For 0<=m<=1 every coordinate is strictly positive, its norm is
nonzero, and the resulting field is exactly u(F(p)), with F(p) the normalized
squared-amplitude contrast. The slice is invariant at every finite iteration,
and actual field and contrast iterates are returned to scalar F iterates.
The input p=0 is the original constructed uniform fixed point for every b,k.

The exact selected response has q'(0)=-kb/8. Differentiation through the actual
mixing and normalization gives

```
F'(0)=1-m-m*kb/8.
```

For m>0 this alternating mode has |F'(0)|<1 precisely when
`-1<kb/8<2/m-1`. For the source's m=1/2, the condition is `-8<kb<24`.
This is a linear criterion for this mode, not an all-mode stability criterion.

The nonlinear return is also proved. When |F'(0)|<1, differentiability supplies
a local gain bound with a factor r<1. Actual iterates stay in that neighborhood,
obey the geometric contrast bound, and their actual fields converge to uniform.
When |F'(0)|>1, a gain r>1 forces every nonzero sufficiently small alternating
perturbation to leave a fixed contrast neighborhood after finitely many actual
iterations. The escape neighborhood is independent of the starting perturbation;
p can be arbitrarily close to zero. This is stronger than one-step amplification.
It does not claim unbounded fields, no fixed point, permanent nonconvergence or
absence of another stable branch. Unit normalization keeps all fields bounded.
At the boundary kb=-8 or24, no nonlinear verdict is inferred.

Concrete controls at m=1/2 use b=1,k=30 and b=100,k=3/10; both have actual
finite escape. At b=1,k=10 and b=0,k=3/10 the alternating mode decays locally.
Changing either coupling or background can affect this mechanism. The b=100
control is deliberately outside the frozen offset sweep and is not a claimed
new failure of one of its historical sampled rows.

## Original-target boundary

The model, sourcing, eight-site ground selection and normalized relaxation are
retained. This control changes only background/coupling and restricts the
initial fields to an earned invariant sector. The real positive representative
is the declared domain; no result about the source's erroneous global complex
phase alignment is inferred. No original nonconstant template, frozen complex
initialization, historical floating iteration or sampled numerical spectral
crossing is silently replaced by this constant-background construction.

Other spatial modes can be unstable even when this mode decays. A complete
all-mode nonlinear stability analysis of the original nonconstant template
still requires its earned selector derivative, spectral/error bounds and
branch identification. Existing all-background/all-coupling existence proofs
remain valid. These new local iteration results do not restore an existential
coupling boundary, background blindness or unrestricted selector impossibility.
No physical Lambda bridge is supplied. No new downgrade of previously supported
claims is made; the full original-target goal remains incomplete.

## Verification

Three new roots add65 theorems. Full `lake build` passes8182 jobs with warnings
as errors. All65 exported statements and transitive standard-only axiom
closures are freshly checked. Cumulative1593 retains the exact immutable1528
prefix and appends65 fresh closures; the full cumulative command is not rerun.
Prior proof-source/toolchain identity, original Step26 source pin and exact
exported domains are checked by `scripts/de_ground_alternating_verify.py`.
Receipts are in `results/ground_alternating_2026-10-03/`. Only trailing
whitespace in the build receipt is normalized; its informational tactic message
is retained, and no diagnostic content is removed.
