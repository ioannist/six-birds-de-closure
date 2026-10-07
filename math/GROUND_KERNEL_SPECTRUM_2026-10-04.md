# Original determinant signs, expanding modes and native escape

This packet continues the exact sample/derivative and coordinate packets at
`ef2d81f`. It leaves the paper, source experiment and immutable numeric proposals
unchanged. Review is adversarial self-review; no independent reviewer was used.

## Mathematical construction

For the actual normalized half-mixing derivative A at an identified original
branch root, test the shifted matrix B=A-ell I. The previously proved derivative
entry boxes contain every entry, retaining nonlinear source feedback, the energy
response and normalization projection. A freely chosen dyadic preconditioner C
satisfies the whole-box induced infinity-norm test ||I-CB|| <= 1/1000 < 1.
Its construction proposes data; it does not supply a numerical inverse theorem.

The new determinant lemma proves det(I-L)>0 whenever ||L||<1. If det(I-tL)
vanished for 0<=t<=1, a nonzero vector h=tLh would contradict the norm bound.
The determinant is continuous along this path, starts at 1 and cannot cross zero.
Applied to L=I-CB, this earns det(C)det(B)>0.

Seven exact LU data proposals certify the sign of det(C). All rational factors
are represented by integer matrices with positive common denominators. The kernel
checks the cleared integer product identity, lower and upper triangularity, unit
lower diagonal and signed upper diagonal product. Positive denominators are
established before cancellation. The real triangular determinant theorem then
returns the claimed sign of det(C), hence of the actual shifted derivative.
No midpoint eigenvalue, approximate inverse equality or supplied determinant sign
is used in a concrete return theorem. No row permutation is silently omitted;
these particular factor proposals require none.

## Populated concrete returns

`GroundOriginalSpectrum.concrete_signs` proves these actual signs:

| Coupling | Shift ell | Sign of det(A-ell I) |
|---|---|---|
| 79/5 | -1 | positive |
| 159/10 | -1 | negative |
| 20 | -1 | positive |
| 20 | -36/25 | positive |
| 20 | -71/50 | negative |
| 30 | -249/100 | positive |
| 30 | -247/100 | negative |

The coupling-parameter continuity of the actual constructed ground branch earns
**two distinct minus-one contacts**, one in (79/5,159/10) and another in
(159/10,20). `actual_two_contacts` returns nonzero tangent real modes, full native
minus-one modes and the actual native derivative at the contacts. It has no
supplied determinant-sign, continuous-branch or mode hypothesis. It does not
assert the contacts are first, unique, simple or transverse.

At fixed couplings 20 and 30, determinant continuity in ell earns actual real
expanding eigenvalues in (-36/25,-71/50) and (-249/100,-247/100), respectively.
A determinant zero returns a nonzero actual field eigenmode; invertible real/imag
coordinate bases return a full coordinate eigenmode, normalized to norm 1.
No proposed eigenvector or eigenbasis is assumed.

The existing full derivative norm bounds are 3/2 and 3. Both brackets imply
|ell|>1 and ||DF||<|ell|^2. The actual branch root is unit and fixed, and the
original tolerance guards hold. Applying the previously proved nonlinear native
escape theorem therefore earns, at each of 20 and 30, a fixed positive escape
radius and arbitrarily close **unit complex initial states** whose finite actual
native orbit segments reach outside that radius. Every step through the escape
is active and legal. The original phase bug is retained in the native map.
The existence of a local quadratic remainder is earned analytically, rather
than supplied as an escape hypothesis.

Concrete sign, contact, mode and escape declarations have no hard spectral or
escape premises. The finite-family signed test takes only an index in Fin 7.
Generic transfer lemmas retain their displayed algebraic, norm and containment
hypotheses; the closed numeric leaves populate them in the final application.

## Verification and substantive controls

Fourteen new modules contain 49 new theorems: 18 generic bridge theorems, 21 closed
numeric leaf theorems, eight actual original-parameter returns and two controls.
The controls reject a zero preconditioner through its actual defect row budget,
and reject the reversed determinant sign through the actual signed triangular
product. They change substantive mathematical inputs, rather than deleting a
record field.

Seven leaf modules are built in four bounded batches. A fresh full default build
has 8844 jobs. All 49 new statements and transitive axiom closures are checked;
the closures use only `Classical.choice`, `Quot.sound` and `propext`. The cumulative
2678-declaration audit preserves the immutable 2629-declaration prior raw prefix
and appends the fresh 49-declaration suffix. A full cumulative audit command was
not rerun. The verifier preserves prior proof, runtime, paper and data identity,
checks pinned Lean/mathlib sources, regenerates proposals read-only, checks exact
manifests and exported signatures, and fingerprints the packet.

Receipts are in `results/ground_spectral_2026-10-04/`. Old numeric replay and the
Python test suite were not rerun in this Lean/math-only packet. Rational proposal
construction is external; the represented comparisons are kernel checked. IEEE
per-operation emulation and JSON/IEEE parsing are not proved in Lean.

## Original-target boundary and next construction

This closes the concrete kernel determinant, expanding-mode and nonlinear local
escape obligations at 20 and 30. It does **not** prove the frozen experiment
initialization belongs to an attracting basin or escapes; all orbits escape;
amplitudes are unbounded; or every coupling above 15 is unstable. Coupling 15
remains proved locally attracting. A native finite local escape conclusion does
not supply any of these stronger assertions.

The next constructive route is a certified finite orbit prefix for the original
initialization, followed by a returned local basin or a precisely scoped finite
source outcome. The eighteen background-offset sample roots and derivative norms
also remain to be instantiated in the kernel. First-contact localization and
simplicity/transversality would require additional spectral control beyond these
sign reversals. The physical Lambda bridge and previously recorded wrong or
project-sized targets remain separate. The original-paper goal is incomplete.
