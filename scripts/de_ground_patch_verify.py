"""Verify finite branch assembly, fresh Lean receipts and immutable provenance.

Numerical certificates are protected historical evidence in this analytic-only
packet. This script does not claim to freshly replay their exact arithmetic.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = 'a840892'
PACKET = 'results/ground_patch_2026-10-04/'
PRIOR = 'results/ground_branch_2026-10-03/verification.json'
MODS = ['GroundParameterPatch', 'GroundParameterPatchReturn']
PREFIX = 'SbtCosmo.Derivation.'
OLD_AUDIT = 'lean/manifests/axiom_audit_ground_branch_2026-10-03.txt'
NEW_AUDIT = 'lean/manifests/axiom_audit_ground_patch_new_2026-10-04.txt'
COMBINED = 'lean/manifests/axiom_audit_ground_patch_2026-10-04.txt'
MUTABLE = {'README.md', 'lean/README.md', 'lean/lakefile.lean',
           'lean/manifests/check_axioms.lean', 'lean/manifests/coverage_table.md',
           'math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}


def read(p):
    return (ROOT / p).read_text()


def sha(b):
    return hashlib.sha256(b).hexdigest()


def baseline(p):
    return subprocess.check_output(['git', 'show', BASE + ':' + p], cwd=ROOT)


def canonical(p):
    b = (ROOT / p).read_bytes()
    if b'\r\n' in b:
        attrs = subprocess.check_output(['git', 'check-attr', 'text', 'eol', '--', p], cwd=ROOT).decode()
        assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in b
        b = b.replace(b'\r\n', b'\n')
    return b


def closures(raw, names):
    entries = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", raw)
    assert [n for n, _ in entries] == names
    assert not re.search(r'error:|warning:|sorryAx', raw)
    for n, a in entries:
        assert {x.strip() for x in a.split(',') if x.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, n


def flatten(t):
    t = ' '.join(t.replace('(', ' ').replace(')', ' ').split())
    t = re.sub(r'\s+,', ',', t)
    return t.replace('| ', '|').replace(' |', '|')


prior = json.loads(read(PRIOR))
assert (ROOT / PRIOR).read_bytes() == baseline(PRIOR)
assert len(prior['source_sha256']) == 583
for p, h in prior['source_sha256'].items():
    if p not in MUTABLE:
        assert sha((ROOT / p).read_bytes()) == h and canonical(p) == baseline(p), p
new = []
for mod in MODS:
    source = read('lean/SbtCosmo/Derivation/' + mod + '.lean')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', source)
    new += [PREFIX + mod + '.' + n for n in re.findall(r'^theorem ([\w.]+)', source, re.M)]
assert len(new) == 17
old_manifest = baseline('lean/manifests/check_axioms.lean').decode()
old = re.findall(r'^#print axioms (\S+)', old_manifest, re.M)
assert len(old) == 1813
imports = ''.join('import ' + PREFIX + mod + '\n' for mod in MODS)
assert read('lean/manifests/check_axioms.lean') == old_manifest + '\n' + imports + '\n' + ''.join('#print axioms ' + n + '\n' for n in new)
assert read('lean/lakefile.lean') == baseline('lean/lakefile.lean').decode()[:-2] + ',\n    ' + ', '.join('`' + PREFIX + mod for mod in MODS) + ']\n'
for suffix, cmd in [('axioms', '#print axioms '), ('statements', '#check ')]:
    assert read('lean/manifests/check_ground_patch_' + suffix + '.lean') == imports + '\n' + ''.join(cmd + n + '\n' for n in new)
assert (ROOT / OLD_AUDIT).read_bytes() == baseline(OLD_AUDIT)
oldraw, newraw = read(OLD_AUDIT), read(NEW_AUDIT)
closures(oldraw, old)
closures(newraw, new)
header = ('Cumulative audit: immutable 1813-declaration raw prefix plus freshly audited 17-declaration suffix.\n'
          'Baseline: a840892; proof-source/toolchain identity checked by de_ground_patch_verify.py.\n'
          'Full 1830-declaration command was not rerun in this packet.\n\n')
combined = header + oldraw + '\n' + newraw
closures(combined, old + new)
(ROOT / COMBINED).write_text(combined)
statements = read(PACKET + 'theorem_statements.txt')
assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)] == new
assert not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^' + re.escape(PREFIX) + r'(\w+)\.([\w.]+)', statements, re.M))
decls = {}
for i, m in enumerate(starts):
    t = statements[m.start():starts[i + 1].start() if i + 1 < len(starts) else len(statements)]
    t = re.sub(r'SbtCosmo\.Derivation\.\w+\.', '', t).replace('⇑', '')
    decls[m.group(1) + '.' + m.group(2).rstrip('.')] = flatten(t)


def require(name, *tokens):
    for token in tokens:
        assert flatten(token) in decls[name], (name, token, decls[name])


P, R = [m + '.' for m in MODS]
require(P + 'TubeCover.tube_root_eq', 'k ∈ v.tube i .interval', 'k ∈ v.tube j .interval',
        'v.tube i .root k = v.tube j .root k')
require(P + 'TubeCover.root_eq', 'v.root k = v.tube i .root k')
require(P + 'TubeCover.root_spec', 'k ∈ v.domain', 'residual b k v.root k = 0',
        '0 < v.root k .1 i', 'IsGround', 'groundMap b k v.root k .1 = v.root k .1')
require(P + 'TubeCover.sample_root_return', 'residual b k x = 0', 'x = v.root k')
require(P + 'TubeCover.root_continuous_on', '[Finite ι]', 'ContinuousOn v.root v.domain')
require(P + 'TubeCover.root_implicit_germ', 'ContDiffAt ℝ ↑⊤ g k', 'g k = v.root k',
        'v.root =ᶠ[nhdsWithin k v.domain] g')
require(P + 'TubeCover.root_smooth_on', 'ContDiffOn ℝ ↑⊤ v.root v.domain')
require(P + 'TubeCover.groundPair_return', 'normSq v.root k .1 = 1',
        'groundPair sourcePotential b k v.root k .1 = v.root k')
require(R + 'closedBall_containment', 'dist x y + r ≤ s', 'Metric.closedBall x r ⊆ Metric.closedBall y s')
require(R + 'certified_sample_return', 'dist a.center v.tube i .center + a.radius ≤ v.tube i .radius',
        'a.root k = v.root k')
require(R + 'field_fixed', 'normSq field v k = 1', 'groundMap b k field v k = field v k')
require(R + 'native_fixed_legal', '0 ≤ τ', 'τ < 1', 'nativeUpdate', 'ActivePhase', 'NativeLegal')
require(R + 'minus_one_contact', 'Set.Icc a c ⊆ v.domain',
        'crossingDet b, a, field v a * crossingDet b, c, field v c < 0',
        '∃ k ∈ Set.Ioo a c, ModeContact b field v k τ k')
require(R + 'two_distinct_contacts', '∃ k₁ ∈ Set.Ioo a d, ∃ k₂ ∈ Set.Ioo d c, k₁ < k₂',
        'ModeContact b field v k₁ τ k₁ ∧ ModeContact b field v k₂ τ k₂')
patch_source = flatten(read('lean/SbtCosmo/Derivation/GroundParameterPatch.lean'))
for token in ['closed : ∀ i, IsClosed tube i .interval',
              'overlap : ∀ i j k, k ∈ tube i .interval → k ∈ tube j .interval →',
              '∃ a : TubeCertificate b, k ∈ a.interval ∧',
              'closedBall a.center a.radius ⊆ closedBall tube i .center tube i .radius ∧',
              'closedBall a.center a.radius ⊆ closedBall tube j .center tube j .radius']:
    assert flatten(token) in patch_source, token
assert 'ContinuousOn' not in patch_source.split('structure TubeCover', 1)[1].split('variable', 1)[0]
return_source = flatten(read('lean/SbtCosmo/Derivation/GroundParameterPatchReturn.lean'))
contact = return_source.split('def ModeContact', 1)[1].split('theorem', 1)[0]
for token in ['∃ h : Field, h ≠ 0', 'dot u h = 0', 'normalizedJacobian b k 1/2 u h = -h',
              'fullDerivative b k 1/2 u h, 0 = - h, 0', 'HasFDerivAt nativePairMap τ b k 1/2']:
    assert flatten(token) in contact, token
build = read(PACKET + 'lean_build.txt')
assert 'Build completed successfully (8202 jobs).' in build
assert not re.search(r'error:|warning:|Build failed', build)
version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT / 'lean').decode().strip()
assert version == prior['actual_lean_version_checked']
mathlib = prior['mathlib']
libroot = ROOT / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert sha((libroot / p).read_bytes()) == h
p = 'Mathlib/Topology/LocallyFinite.lean'
b = (libroot / p).read_bytes()
assert b == subprocess.check_output(['git', 'show', 'HEAD:' + p], cwd=libroot)
mathlib['direct_proof_source_sha256'][p] = sha(b)
files = set(prior['source_sha256']) | {PRIOR, NEW_AUDIT, COMBINED,
    'lean/manifests/check_ground_patch_axioms.lean', 'lean/manifests/check_ground_patch_statements.lean',
    'math/GROUND_FINITE_PATCH_2026-10-04.md', 'scripts/de_ground_patch_verify.py'}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT / PACKET).iterdir() if p.name != 'verification.json')
assert len(files) == 595, len(files)
v = dict(baseline_commit=BASE, scope='Finite quantitative actual branch assembly and native/mode returns',
    axiom_audit=dict(declarations_cumulative=1830, declarations_preserved=1813, declarations_fresh=17,
        new_local_theorems=new, axioms=['Classical.choice', 'Quot.sound', 'propext'],
        full_cumulative_command_rerun=False, preserved_raw_prefix=OLD_AUDIT,
        preserved_prefix_sha256=sha(oldraw.encode()), fresh_suffix_receipt=NEW_AUDIT,
        combined_receipt=COMBINED, success=True),
    lean_build=dict(command='lake build', jobs=8202, success=True, warnings_as_errors=True,
        receipt_trailing_whitespace_normalized=True, diagnostic_content_removed=False),
    statement_check=dict(declarations=17, success=True), mathlib=mathlib, actual_lean_version_checked=version,
    original_return=dict(finite_global_root_constructed=True, overlap_identity_earned=True,
        global_continuity_and_C_infinity_germs_earned=True, full_ground_energy_pair_return=True,
        quantitative_sample_root_identity=True, native_fixed_phase_normalization_legality=True,
        two_distinct_actual_mode_contacts_without_supplied_continuous_branch=True,
        concrete_286_tube_Lean_cover_instantiated=False, concrete_kernel_numeric_sign_norm_proofs=False,
        inherited_mathematical_branch_interval=['0', '30'], inherited_minus_one_contacts=[['79/5', '159/10'], ['159/10', '20']],
        global_root_uniqueness=False, first_unique_transverse_contact=False, nonlinear_escape=False,
        frozen_complex_initialization_basin=False, all_interval_stability=False),
    exact_numeric_replay_fresh=False, exact_numeric_evidence_immutable_from_baseline=PRIOR,
    python_test_suite_rerun=False, paper_edited=False, original_runtime_edited=False,
    review='adversarial self-review, not independent review', goal_complete=False,
    next_construction='Concrete kernel tube/coverage/norm/sign certificates or original-init basin bounds',
    source_sha256={p: sha((ROOT / p).read_bytes()) for p in sorted(files)},
    git_blob_sha256={p: sha(canonical(p)) for p in sorted(files)})
(ROOT / PACKET / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print('1830 cumulative standard-only closures; 17 fresh statements; finite smooth assembly; 595 fingerprints')
