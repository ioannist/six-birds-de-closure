"""Adversarial replay, arithmetic controls, Lean audit and provenance checks."""
import copy
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess

import de_ground_interval_certificate as cert

ROOT = cert.ROOT
BASE = '653ab69'
PACKET = 'results/ground_interval_2026-10-03/'
PRIOR = 'results/ground_jacobian_2026-10-03/verification.json'
MOD = 'SbtCosmo.Derivation.GroundRootCertificate'
OLD_AUDIT = 'lean/manifests/axiom_audit_ground_jacobian_2026-10-03.txt'
NEW_AUDIT = 'lean/manifests/axiom_audit_ground_interval_new_2026-10-03.txt'
COMBINED = 'lean/manifests/axiom_audit_ground_interval_2026-10-03.txt'
MUTABLE = {'README.md', 'lean/README.md', 'lean/lakefile.lean',
           'lean/manifests/check_axioms.lean', 'lean/manifests/coverage_table.md',
           'math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}


def read(p):
    return (ROOT/p).read_text()


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def baseline(p):
    return subprocess.check_output(['git', 'show', BASE+':'+p], cwd=ROOT)


def canonical(p):
    b = (ROOT/p).read_bytes()
    if b'\r\n' in b:
        attrs = subprocess.check_output(['git', 'check-attr', 'text', 'eol', '--', p], cwd=ROOT).decode()
        assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in b
        b = b.replace(b'\r\n', b'\n')
    return b


def closures(raw, names):
    entries = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", raw)
    assert [n for n, _ in entries] == names
    assert not re.search(r'error:|warning:|sorryAx', raw)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for n, a in entries:
        assert {x.strip() for x in a.split(',') if x.strip()} <= allowed, n


class Dual:
    """Independent exact forward differentiation of the nine polynomials."""
    def __init__(self, v, d=None):
        self.v, self.d = F(v), [F(0)]*9 if d is None else d

    def __add__(self, o):
        o = o if isinstance(o, Dual) else Dual(o)
        return Dual(self.v+o.v, [x+y for x, y in zip(self.d, o.d)])

    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.v, [-x for x in self.d])

    def __sub__(self, o):
        return self + -(o if isinstance(o, Dual) else Dual(o))

    def __mul__(self, o):
        o = o if isinstance(o, Dual) else Dual(o)
        return Dual(self.v*o.v, [x*o.v+self.v*y for x, y in zip(self.d, o.d)])

    __rmul__ = __mul__


def contains(interval, value):
    assert F(interval.lo, cert.SCALE) <= value <= F(interval.hi, cert.SCALE)


def controls(data):
    rng = random.Random(261003)
    cases = 0
    for _ in range(100):
        a, b = F(rng.randrange(-10**20, 10**20), rng.randrange(1, 10**10)), F(rng.randrange(-10**20, 10**20), rng.randrange(1, 10**10))
        ia, ib = cert.I.of(a), cert.I.of(b)
        for it, v in [(ia+ib, a+b), (ia-ib, a-b), (ia*ib, a*b), (ia/ib, a/b)]:
            contains(it, v)
            cases += 1
    # Include sign changes and zero-crossing wide interval products/divisions.
    for alo, ahi, blo, bhi in [(-2, 3, -4, 5), (-3, -1, 2, 4), (1, 3, -4, -2)]:
        ia, ib = cert.I(alo*cert.SCALE, ahi*cert.SCALE), cert.I(blo*cert.SCALE, bhi*cert.SCALE)
        for a in [F(alo), F(alo+ahi, 2), F(ahi)]:
            for b in [F(blo), F(blo+bhi, 2), F(bhi)]:
                contains(ia*ib, a*b)
                cases += 1
                if not blo <= 0 <= bhi:
                    contains(ia/ib, a/b)
                    cases += 1
    derivatives = 0
    for w in data['witnesses']:
        xs = [F(int(t), cert.SCALE) for t in w['center']]
        bs = [F.from_float(float.fromhex(t)) for t in w['background_hex']]
        k = F.from_float(float.fromhex(w['coupling_hex']))
        dx = [Dual(x, [F(int(i == j)) for j in range(9)]) for i, x in enumerate(xs)]
        u, e = dx[:8], dx[8]
        fs = []
        for i in range(8):
            grad = F(1, 2)*(u[(i+1) % 8]-u[(i-1) % 8])
            v = bs[i]+k*(grad*grad+bs[i]*u[i]*u[i])
            fs.append((1+v-e)*u[i]-F(1, 2)*(u[(i-1) % 8]+u[(i+1) % 8]))
        fs.append(F(1, 2)*(sum((t*t for t in u), Dual(0))-1))
        ff, df, _, _ = cert.equations(list(map(cert.I.of, bs)), cert.I.of(k), list(map(cert.I.of, xs)))
        for i in range(9):
            contains(ff[i][0], fs[i].v)
            for j in range(9):
                contains(df[i][j], fs[i].d[j])
                derivatives += 1
    rejected = []

    def reject(name, w, whole=False):
        try:
            cert.replay(w) if whole else cert.certify(w)
        except (AssertionError, ZeroDivisionError):
            rejected.append(name)
        else:
            raise AssertionError('false certificate accepted: '+name)

    w = copy.deepcopy(data['witnesses'][0]); w['center'][0] = str(int(w['center'][0])+cert.SCALE//20)
    reject('displaced root', w)
    w = copy.deepcopy(data['witnesses'][0]); w['radius'] = '1'
    reject('inadequate radius', w)
    w = copy.deepcopy(data['witnesses'][0]); w['newton_inverse'] = [['0']*9 for _ in range(9)]
    reject('singular Newton inverse', w)
    w = copy.deepcopy(data['witnesses'][-1]); w['verdict'] = 'stable'
    reject('unstable point relabelled stable', w)
    w = copy.deepcopy(data['witnesses'][-3]); w['verdict'] = 'unstable'; w['unstable_bracket'] = ['-2', '-3/2']
    reject('stable kappa15 relabelled unstable', w)
    w = copy.deepcopy(data); w['witnesses'][0]['coupling_hex'] = (1.).hex()
    reject('changed original coupling', w, True)
    return dict(exact_arithmetic_containment_checks=cases,
                independently_differentiated_coefficients=derivatives,
                rejected_false_certificates=rejected, independent_reviewer=False)


data = json.loads(read(PACKET+'witnesses.json'))
result = cert.replay(data)
assert result == json.loads(read(PACKET+'certificates.json'))
assert result['stable_samples'] == 28 and result['unstable_samples'] == 2
ctrl = controls(data)
assert ctrl['exact_arithmetic_containment_checks'] == 445
assert ctrl['independently_differentiated_coefficients'] == 2430
assert len(ctrl['rejected_false_certificates']) == 6
(ROOT/PACKET/'controls.json').write_text(json.dumps(ctrl, indent=2)+'\n')

prior = json.loads(read(PRIOR))
assert (ROOT/PRIOR).read_bytes() == baseline(PRIOR)
for p, h in prior['source_sha256'].items():
    if p not in MUTABLE:
        assert sha((ROOT/p).read_bytes()) == h and canonical(p) == baseline(p), p
source = read('lean/SbtCosmo/Derivation/GroundRootCertificate.lean')
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', source)
new = [MOD+'.'+n for n in re.findall(r'^theorem (\w+)', source, re.M)]
assert len(new) == 11
old_manifest = baseline('lean/manifests/check_axioms.lean').decode()
old = re.findall(r'^#print axioms (\S+)', old_manifest, re.M)
assert len(old) == 1644
imports = 'import '+MOD+'\n'
assert read('lean/manifests/check_axioms.lean') == old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
assert read('lean/lakefile.lean') == baseline('lean/lakefile.lean').decode()[:-2]+',\n    `'+MOD+']\n'
for suffix, cmd in [('axioms', '#print axioms '), ('statements', '#check ')]:
    assert read('lean/manifests/check_ground_interval_'+suffix+'.lean') == imports+'\n'+''.join(cmd+n+'\n' for n in new)
assert (ROOT/OLD_AUDIT).read_bytes() == baseline(OLD_AUDIT)
oldraw, newraw = read(OLD_AUDIT), read(NEW_AUDIT)
closures(oldraw, old); closures(newraw, new)
header = ('Cumulative audit: immutable 1644-declaration raw prefix plus freshly audited 11-declaration suffix.\n'
          'Baseline: 653ab69; proof-source/toolchain identity checked by de_ground_interval_verify.py.\n'
          'Full 1655-declaration command was not rerun in this packet.\n\n')
combined = header+oldraw+'\n'+newraw
closures(combined, old+new)
(ROOT/COMBINED).write_text(combined)
statements = read(PACKET+'theorem_statements.txt')
assert re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M) == new
assert not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^'+re.escape(MOD)+r'\.(\w+)', statements, re.M))
decls = {}
def flatten(t):
    return ' '.join(t.replace('(', ' ').replace(')', ' ').split())
for i, m in enumerate(starts):
    text = statements[m.start():starts[i+1].start() if i+1 < len(starts) else len(statements)]
    text = re.sub(r'SbtCosmo\.Derivation\.\w+\.', '', text).replace('⇑', '')
    decls[m.group(1)] = flatten(text)
for name, tokens in {
    'residual_hasFDerivAt': ['b : Field', 'κ : ℝ', 'x : Point', 'HasFDerivAt residual b κ residualDerivative b κ x x'],
    'positive_root_return': ['hz : residual b κ x = 0', 'hp : ∀ i : Fin 8 , 0 < x.1 i', 'IsGround sourcePotential b κ x.1 x.1 x.2', 'groundMap b κ x.1 = x.1'],
    'root_half_mixing_derivative': ['HasFDerivAt', 'normalizedRelaxed groundMap b κ 1 / 2', 'normalizedJacobian b κ 1 / 2 x.1'],
    'half_mixing_jacobian_apply': ['hf : groundMap b κ u = u', 'h i - dot u h * u i + jacobian b κ u h i / 2'],
    'certified_positive_root': ['hC : Function.Injective C', 'hr : 0 ≤ r', 'hq : q < 1',
        'hd : ∀ x ∈ Metric.closedBall center r, ‖correctionDerivative b κ C x‖ ≤ ↑q',
        'hy : ‖C residual b κ center ‖ + ↑q * r ≤ r',
        'hp : ∀ x ∈ Metric.closedBall center r, ∀ i : Fin 8 , 0 < x.1 i',
        '∃ x ∈ Metric.closedBall center r, residual b κ x = 0',
        '∀ y ∈ Metric.closedBall center r, residual b κ y = 0 → y = x'],
}.items():
    for token in tokens:
        assert flatten(token) in decls[name], (name, token, decls[name])
build = read(PACKET+'lean_build.txt')
assert 'Build completed successfully (8188 jobs).' in build
assert not re.search(r'error:|warning:|Build failed', build)
version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT/'lean').decode().strip()
assert version == prior['actual_lean_version_checked']
mathlib = prior['mathlib']
libroot = ROOT/'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert sha((libroot/p).read_bytes()) == h
for p in ['Mathlib/Analysis/Calculus/MeanValue.lean', 'Mathlib/Topology/MetricSpace/Contracting.lean',
          'Mathlib/Topology/MetricSpace/Lipschitz.lean', 'Mathlib/Topology/EMetricSpace/Lipschitz.lean']:
    b = (libroot/p).read_bytes()
    assert b == subprocess.check_output(['git', 'show', 'HEAD:'+p], cwd=libroot)
    mathlib['direct_proof_source_sha256'][p] = sha(b)
files = set(prior['source_sha256']) | {PRIOR, NEW_AUDIT, COMBINED,
    'lean/SbtCosmo/Derivation/GroundRootCertificate.lean',
    'lean/manifests/check_ground_interval_axioms.lean', 'lean/manifests/check_ground_interval_statements.lean',
    'math/GROUND_INTERVAL_CERTIFICATES_2026-10-03.md',
    'scripts/de_ground_interval_certificate.py', 'scripts/de_ground_interval_verify.py'}
files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.name != 'verification.json')
assert len(files) == 532, len(files)
v = dict(baseline_commit=BASE,
         scope='Exact computational positive-root and half-mixing spectral certificates for all30 original sample arrays; conditional Lean a posteriori criterion',
         axiom_audit=dict(declarations_cumulative=1655, declarations_preserved=1644,
                         declarations_fresh=11, new_local_theorems=new,
                         axioms=['Classical.choice', 'Quot.sound', 'propext'],
                         full_cumulative_command_rerun=False, preserved_raw_prefix=OLD_AUDIT,
                         preserved_prefix_sha256=sha(oldraw.encode()), fresh_suffix_receipt=NEW_AUDIT,
                         combined_receipt=COMBINED, success=True),
         lean_build=dict(command='lake build', jobs=8188, success=True, warnings_as_errors=True,
                         receipt_trailing_whitespace_normalized=True, diagnostic_content_removed=False),
         statement_check=dict(declarations=11, success=True),
         mathlib=mathlib, actual_lean_version_checked=version,
         concrete_certificates=dict(root_count=30, stable_count=28, unstable_count=2,
                                    exact_integer_replay=True, independently_differentiated_polynomials=True,
                                    lean_kernel_checked=False, input_bridge='original IEEE arrays reified as exact dyadics'),
         original_return=dict(original_sourcing_and_half_mixing=True,
                              positive_real_representative_only=True,
                              continuous_nonlinear_branch_identification=False,
                              global_uniqueness=False, frozen_complex_run=False,
                              nonlinear_orbit_convergence_mechanized=False,
                              physical_Lambda_bridge=False, no_in_layer_selector_impossibility=False),
         python_test_suite_rerun=False, original_runtime_edited=False, paper_edited=False,
         review='adversarial self-review, not independent review', goal_complete=False,
         next_construction='Mechanize concrete interval bounds and nonlinear local dynamical return; connect sample points along a rigorously continued branch if needed',
         source_sha256={p: sha((ROOT/p).read_bytes()) for p in sorted(files)},
         git_blob_sha256={p: sha(canonical(p)) for p in sorted(files)})
(ROOT/PACKET/'verification.json').write_text(json.dumps(v, indent=2)+'\n')
print('1655 cumulative standard-only closures; 30 exact root/spectral certificates; 532 fingerprints; false controls rejected')
