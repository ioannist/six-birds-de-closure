# Original access fork and adopted mediator strengthening, 2026-10-02

Baseline: `4430aea`. The paper and frozen experiment outputs are unchanged.
This is mathematical construction and adversarial self-review by one reviewer,
with Lean kernel checking and a separately implemented rational audit. It is
not independent human review or a physical QM/GR derivation.

## Targets and source correction

The original paper sections 2.4 and 6.3 import a common-refinement fork: QM and
GR are declared access quotients which do not determine each other, and their
completions allegedly do not commute. It then calls the vacuum-energy mismatch
a cross-layer route defect. These are different mathematical obligations.

The current source corpus paper,
`../six-birds-papers/Tsiokos_2026_To_Kill_Three_Stones_with_Six_Birds_A_Common_Grammar_for_the_SM_QM_and_GR.tex`,
sections 5.1--5.3, corrects the commutation claim and makes the physical common
carrier a hypothesis. Its Q1/Q2 repairs are in
`../six-birds-sm-qm-gr/review_2026/repairs/q1_access_provenance/` and
`q2_route_mismatch/`. They support the narrow abstract fork, but the original
Boolean conditional means commute. The old 0.5 was a distance between completed
tables, not a commutator. The physical common-carrier/quantization interpretation
and the numerical vacuum-discrepancy bridge remain unconstructed.

The user explicitly adopted this strengthening on 2026-10-02:

> any deterministic mediator that determines both readouts must retain all four coordinates

The precise adopted theorem is full-state recoverability on the declared
four-bit carrier, with injectivity, sharp record counts and partition uniqueness
as consequences. A generic version also retains arbitrary four-mode tuples on
an arbitrary underlying carrier. No uniqueness of physical architecture is
inferred from uniqueness of this information partition.

## 1. Actual maps and a direct full-state return

Let H=Bool^4, with x=(d0,d1,d2,d3), and set

```
qQM(x)=(d0,d1,d2), qGR(x)=(d0,d2,d3).
```

For r:H->Y, define "target factors through r" by existence of a total decoder
Y->target-type which agrees at every r(x). The joint endpoint map is injective:
its first record supplies d0,d1,d2 and its second supplies d3.

More strongly, suppose decoders q,g satisfy

```
q(r(x))=qQM(x), g(r(x))=qGR(x).
```

Then the explicit map

```
decode(y)=(q(y).d0, q(y).d1, q(y).d2, g(y).d3)
```

satisfies decode(r(x))=x. This forward construction uses the supplied endpoint
decoders and four projections; it does not require inverse choice, an optimizer,
or a precomputed full-state answer. Conversely a full-state decoder supplies
both endpoint decoders by projection. Thus

```
[r determines qQM and qGR] iff [identity of H factors through r].
```

It follows that r is injective. Conversely any injective r has a left inverse
on its image, extended to a total map by choosing a default state. Hence also

```
[r determines qQM and qGR] iff [r is injective].
```

This quantifies over every record type Y and every deterministic map r, not
only the source's nine generated F24 representatives or its coordinate subsets.
The general converse uses Classical.choice; it asserts existence, not an
algorithmic complexity bound. The adopted forward recovery itself is explicit.

The r-fiber relation is exactly equality on H. Its realized record image has
exactly 16 elements, even when Y is infinite; a finite Y must have cardinality
at least 16. The identity mediator attains this bound. This is uniqueness of
the induced information partition, or equivalence of H with the realized image,
not literal identity of record types or coordinates. The reversible encoding
(d0,d1,d2,d1 XOR d3) determines both endpoints. A single 16-valued symbol can
also do so: "retain all coordinates" means recoverability, not four literal
output fields.

The generic theorem `overlapping_readouts_iff_full_modes` proves the same
full-tuple factorization for arbitrary coordinate types D0,D1,D2,D3 and any
mode map m:X->D0*D1*D2*D3. There is no independence or finiteness hypothesis.
For a coarse mode map it recovers m(x), not all of the underlying x. Injectivity
of the mediator on X follows only when that mode map is itself injective.

## 2. Non-factorization and redundant augmentation

Two explicit split pairs prove the endpoint fork. Holding d0,d1,d2 fixed and
changing d3 leaves qQM equal but changes qGR. Holding d0,d2,d3 fixed and changing
d1 does the converse. These refute every deterministic endpoint decoder,
not merely linear least-squares decoders.

For any h computed solely from qQM, adjoining (qQM,h(qQM)) does not split a
qQM fiber. It cannot determine qGR either. The theorem quantifies over arbitrary
output types and functions h. It does not forbid a genuinely new observation
which is not a function of the old readout.

The generic fiber criterion is proved with a nonempty source carrier. This
condition permits a default outside the source image and avoids an empty-domain /
empty-target extension exception. It is satisfied by the original Boolean
carrier. None of these factorization statements establishes a physical QM/GR
common carrier or an unrestricted quantum-gravity no-go.

## 3. The published conditional-mean pair commutes

Under the original uniform product measure on H, qQM fibers are precisely
{x,flip3(x)}, and qGR fibers are {x,flip1(x)}. Their completions, acting on any
real scalar observable f:H->R, are therefore the literal fiber averages

```
PQM f(x)=[f(x)+f(flip3(x))]/2,
PGR f(x)=[f(x)+f(flip1(x))]/2.
```

The completion carrier is the real observable space R^H. Applying these
operators to the four coordinate observables gives the source's completed
tables, whose entries can be 1/2.

Both flip maps are involutions and commute. Expanding the two averages gives

```
PQM PGR f = PGR PQM f
         = [f(x)+f(flip3 x)+f(flip1 x)+f(flip3 flip1 x)]/4.
```

The last expression is the actual conditional mean visible on (d0,d2).
The code constructs the access fibers and their sums and cardinalities; the
operators are not defined to commute or supplied with a commutation field.
Their idempotence is proved separately. The commutator defect set on every
observable is empty. This extends to every column of the encoded state table.

Non-factorization of qQM and qGR coexists with commuting completions: those
are distinct questions. Also, the common *refinement* retains all four
coordinates, while these sequential averages keep only the shared coordinates.

The independently implemented Fraction checker reconstructs all 16 coordinate
partitions and the 120 unordered distinct pairs, including 55 incomparable
pairs and the original 8+8 directed split-pair counts. It checks all 256 ordered
coordinate-completion pairs against the mean on their coordinate intersection,
and reproduces all 32 published Q2 operator rows exactly. The old normalized
table-distance **squared** is 1/4 for 0/1 encoding and 1/2 for +/-1 encoding.
The commutator is zero in both cases. A recoding-dependent table distance cannot
be used as the claimed nonzero commutator.

## 4. Exact field-mode provenance and its scope

The Q1 source has 54 constructed (psi,V0) records: 26 field samples, 16 history
states, eight seeded fresh states and four paired controls. It declares the
coarse modes

```
d0=normalization sector,
d1=1[total oriented current>=0],
d2=argmax density,
d3=argmax[V0+kappa*(gradient energy+V0*density)].
```

The current audit independently reads the raw JSON inputs and regenerates the
seeded raw fields without executing the imported Q1, Step25 or Step26 routines.
Raw IEEE coefficients are reified as exact rationals. Analytic normalization's
square root cancels in density, current and gradient energy, making all those
quantities rational. The receipt retains every raw field and background as
hexadecimal IEEE values, plus the Python/NumPy versions, so these witnesses do
not depend on regenerating the seeded stream. Argmax uses the declared
lowest-index tie convention.
Every coarse label agrees both for exact kappa=3/10 and the exact rational
reification of its machine value, and agrees with the exported source labels.
This is an exact finite carrier interpretation and a checked label bridge;
it is not a general floating-point error theorem or continuum field result.

The conjugate control has exactly equal density and sourced potential and
opposite current, with different phase modes. The potential-only control has
exactly equal density/current and different geometry mode. The forward witness
therefore changes an external V0 input. The QM audit includes current, not Born
density alone, and d0 is constant. These premises are material.

The source's `1*2*8*3` describes coordinate marginal sizes. Its **realized joint
mode image has 15 elements**, not the 48-point Cartesian product. The table has
14 QM fibers and 10 GR fibers, with 5 and 32 directed raw-record split pairs.
The generic mediator theorem says every mediator determining both endpoints
must determine these four coarse modes. It does not require recovery of all 54
field records or all complex field amplitudes. On this sample its corresponding
minimum realized record count is 15; the 16 count is specific to the full
Boolean carrier.

## 5. A provenance-backed non-commuting alternative

This is an additional construction, not a rescue of the published Boolean
calculation. Give each of the 54 declared records equal weight, and form the
same conditional-mean operation on its actual coarse endpoint fibers. This
empirical record measure is declared; it is not a natural physical measure.

Both endpoint readouts retain d2, so each density sector is invariant under both
averages. At d2=4 there are three mode cells:

```
(d0,d1,d2,d3) = (1,0,4,0), (1,0,4,3), (1,1,4,0),
record multiplicities = 5,1,3.
```

The middle cell is the potential-only perturbed control. Restricting to this
block, QM fibers group the first two cells and GR fibers group the first and
third. The weighted means on a function f of the three cells are

```
PQM f(0)=PQM f(1)=(5f(0)+f(1))/6, PQM f(2)=f(2),
PGR f(0)=PGR f(2)=(5f(0)+3f(2))/8, PGR f(1)=f(1).
```

Both are actual weighted fiber averages with positive masses, and both are
idempotent. On the indicator f=(0,1,0), at cell 0,

```
PQM PGR f=1/6, PGR PQM f=5/48, commutator=1/16.
```

`FieldAccessBlock` proves the fiber-average bridges, positivity, idempotence,
both directed non-factorizations and this nonzero commutator in Lean. Its
full endpoint triples (1,d1,4) and (1,4,d3) give exactly the same means; dropping
constant coordinates is proved to preserve the operators.

The Python checker verifies the 15-cell weighted operators and their direct
54-record uniform versions. The indicator bridge holds at every raw record;
the defect support is exactly three mode cells / nine raw records in this
block. No new nonlinear projection or altered mode dictionary is inserted.
Removing the potential-only perturbed record restores commutation. Thus this
construction depends on that material control and cannot be advertised as
non-commutation of the original fixed-background, full Boolean pair or as a
physical obstruction to quantizing gravity.

This can substantiate a **scoped finite fork with genuine non-commuting
completion routes** on the declared field-record model. It supplies no map
relating its 1/16 commutator to a physical vacuum-energy estimate or Lambda,
no dimensional conversion and no physical common-carrier theorem. A derivation
of the 10^120 discrepancy as a particular physical route defect remains a
separate substantial project and is parked under the user's stopping rule.

## Adversarial self-review and verification

The adopted all-mediator theorem has a direct decoder return. No selected
answer, optimizer or uniqueness assertion is hidden as a hypothesis. For the
Boolean case, both split witnesses, finite cardinalities, actual average
fibers, idempotence and commutation are mechanized. Reversible encodings and
redundant augmentation test the intended information meaning.

The arbitrary-mode version is intentionally weaker than full raw-field
recovery unless the mode map is injective. The exact field bridge and 54-record
operator calculations are Fraction checks, not Lean reification of the raw
complex samples. The three-cell profile and operator calculation are kernel
checked, with their field-data applicability separately verified. The
potential-control ablation challenges the mathematical carrier rather than a
label in a record. No independence, physical meaning or uniqueness of a
physical completion is inferred from the sample.

Reproduce with `lake build` and `lake env lean manifests/check_axioms.lean`
from `lean/`, and `python scripts/de_access_fork_checks.py` in the documented
sbt-de environment. The raw audit is
`lean/manifests/axiom_audit_access_fork_2026-10-02.txt`; source-hashed evidence
is in `results/access_fork_2026-10-02/`. This packet improves original finite
coverage and adopts the user's strengthening, but does not establish the
original paper's physical conclusions as a whole.
