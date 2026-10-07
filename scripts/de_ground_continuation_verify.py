"""Check the original full continuum kernel packet and immutable provenance.

Numeric Python calculations supply data only; all new comparisons have fresh
Lean-kernel proof receipts. Earlier sample/sign certificates remain historical.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = 'fb483ec'
PACKET = 'results/ground_continuation_2026-10-04/'
PRIOR = 'results/ground_kernel_2026-10-04/verification.json'
PREFIX = 'SbtCosmo.Derivation.'
LEAVES = ['GroundContinuation.' + p.stem for p in sorted(
    (ROOT / 'lean/SbtCosmo/Derivation/GroundContinuation').glob('*.lean'))]
MODS = ['GroundKernelChain', 'GroundKernelChainCoverage', *LEAVES,
        'GroundOriginalContinuation']
ROOTS = ['GroundKernelChain', 'GroundKernelChainCoverage', 'GroundOriginalContinuation']
OLD_AUDIT = 'lean/manifests/axiom_audit_ground_kernel_2026-10-04.txt'
NEW_AUDIT = 'lean/manifests/axiom_audit_ground_continuation_new_2026-10-04.txt'
COMBINED = 'lean/manifests/axiom_audit_ground_continuation_2026-10-04.txt'
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
    return t.replace('| ', '|').replace(' |', '|').replace('‖ ', '‖').replace(' ‖', '‖')


def sourcepath(mod):
    return 'lean/' + (PREFIX + mod).replace('.', '/') + '.lean'


prior = json.loads(read(PRIOR))
assert (ROOT / PRIOR).read_bytes() == baseline(PRIOR)
assert len(prior['source_sha256']) == 611
for p, h in prior['source_sha256'].items():
    if p not in MUTABLE:
        assert sha((ROOT / p).read_bytes()) == h and canonical(p) == baseline(p), p
assert len(LEAVES) == 572 and len(MODS) == 575
new = []
for mod in MODS:
    source = read(sourcepath(mod))
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', source), mod
    new += [PREFIX + mod + '.' + n for n in re.findall(r'^theorem ([\w.]+)', source, re.M)]
assert len(new) == 589 and len(set(new)) == 589
old_manifest = baseline('lean/manifests/check_axioms.lean').decode()
old = re.findall(r'^#print axioms (\S+)', old_manifest, re.M)
assert len(old) == 1870
imports = ''.join('import ' + PREFIX + mod + '\n' for mod in MODS)
assert read('lean/manifests/check_axioms.lean') == old_manifest + '\n' + imports + '\n' + ''.join('#print axioms ' + n + '\n' for n in new)
assert read('lean/lakefile.lean') == baseline('lean/lakefile.lean').decode()[:-2] + ',\n    ' + ', '.join('`' + PREFIX + mod for mod in ROOTS) + ']\n'
for suffix, cmd in [('axioms', '#print axioms '), ('statements', '#check ')]:
    assert read('lean/manifests/check_ground_continuation_' + suffix + '.lean') == imports + '\n' + ''.join(cmd + n + '\n' for n in new)
assert (ROOT / OLD_AUDIT).read_bytes() == baseline(OLD_AUDIT)
oldraw, newraw = read(OLD_AUDIT), read(NEW_AUDIT)
closures(oldraw, old)
closures(newraw, new)
header = ('Cumulative audit: immutable 1870-declaration raw prefix plus freshly audited 589-declaration suffix.\n'
          'Baseline: fb483ec; proof-source/toolchain identity checked by de_ground_continuation_verify.py.\n'
          'Full 2459-declaration command was not rerun in this packet.\n\n')
combined = header + oldraw + '\n' + newraw
closures(combined, old + new)
(ROOT / COMBINED).write_text(combined)
statements = read(PACKET + 'theorem_statements.txt')
assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)] == new
assert not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo[\w.]*', statements, re.M))
decls = {}
for i, m in enumerate(starts):
    t = statements[m.start():starts[i + 1].start() if i + 1 < len(starts) else len(statements)]
    name = m.group().rstrip('.')
    # Retain module names to distinguish records and actual mathematical maps.
    decls[name] = flatten(t.replace(PREFIX, '').replace('⇑', ''))


def require(name, *tokens):
    for token in tokens:
        assert flatten(token) in decls[PREFIX + name], (name, token, decls[PREFIX + name])


for mod in LEAVES:
    require(mod + '.arithmetic', 'GroundKernelTube.Arithmetic',
            'GroundOriginalFirstTube.originalBackground', *(mod + '.' + k for k in ['a', 'c', 'z', 'r', 'q', 'y', 'C']))
    assert '→' not in decls[PREFIX + mod + '.arithmetic']
require('GroundKernelChain.Data.ball_subset', 'd e : GroundKernelChain.Data β',
        'h : ∀ j : Fin 9, |d.z j - e.z j| + d.r ≤ e.r',
        'Metric.closedBall d.toTube.center d.toTube.radius ⊆ Metric.closedBall e.toTube.center e.toTube.radius')
require('GroundKernelChain.Chain.ordered_overlap', 's : GroundKernelChain.Chain β n',
        'i < j', '∃ a,', 'k ∈ a.interval',
        'Metric.closedBall a.center a.radius ⊆')
require('GroundKernelChainCoverage.finite_interval_union', 'hm : Monotone edge',
        '⋃ i, Set.Icc edge i.castSucc edge i.succ', 'Set.Icc edge 0 edge Fin.last n + 1')
require('GroundKernelChainCoverage.chain_whole_branch_smooth', 's : GroundKernelChain.Chain β n',
        'ContDiffOn ℝ ↑⊤ s.cover.root')
O = 'GroundOriginalContinuation.'
require(O + 'increasing', 'i : Fin 286', O + 'edges i.castSucc <', O + 'edges i.succ')
require(O + 'piece_bounds', 'i : Fin 286', O + 'pieces i .a =', O + 'pieces i .c =')
require(O + 'anchor_bounds', 'i : Fin 287', O + 'anchors i .a =', O + 'anchors i .c =')
require(O + 'containment', 'i : Fin 286', 'j : Fin 9', O + 'anchors i.castSucc', O + 'anchors i.succ')
require(O + 'domain_eq', O + 'cover.domain = Set.Icc 0 30')
require(O + 'whole_smooth', 'ContDiffOn ℝ ↑⊤ ' + O + 'branch Set.Icc 0 30')
require(O + 'whole_ground', 'κ : ℝ', 'hk : κ ∈ Set.Icc 0 30',
        'GroundRootCertificate.residual', O + 'branch κ = 0', '∀ i : Fin 8, 0 <',
        'GroundState.normSq', '= 1', 'GroundBorder.groundPair', 'GroundSourceJacobian.groundMap')
require(O + 'whole_native_fixed', 'κ m : ℝ', 'hk : κ ∈ Set.Icc 0 30',
        'GroundNativeIteration.nativeUpdate GroundNativeControls.originalTolerance',
        'GroundState.realEmbed', 'GroundNativeIteration.ActivePhase', 'GroundNativeIteration.NativeLegal')
# Inspect the actual closed constructors, not merely theorem catalog counts.
import de_ground_continuation_generate as gen
import de_ground_continuation_family as family
ds = gen.proposals()
assert len(ds) == 572
for name, d in ds.items():
    kind = 'Tube' if name.startswith('Tube') else 'Anchor'
    i = int(name[len(kind):])
    source = read(sourcepath('GroundContinuation.' + name))
    assert source == gen.render_leaf(kind, i, d), name
    assert source.count('decide +kernel') == 8, name
assert read(sourcepath('GroundOriginalContinuation')) == family.render()
chain_source = flatten(read(sourcepath('GroundKernelChain')))
for token in ['arithmetic : Arithmetic β a c z r q y C',
              'increasing : ∀ i : Fin (n+1), edge i.castSucc < edge i.succ',
              'anchor_a : ∀ i, (anchor i).a = edge i', 'anchor_c : ∀ i, (anchor i).c = edge i',
              'left_inside : ∀ i j,', 'right_inside : ∀ i j,',
              '∃ a : TubeCertificate (background β), k ∈ a.interval ∧']:
    assert flatten(token) in chain_source, token
assembly = read(sourcepath('GroundOriginalContinuation'))
assert assembly.count('decide +kernel') == 6
assert re.search(r'theorem whole_ground \(κ : ℝ\) \(hk : κ ∈ Set.Icc \(0 : ℝ\) 30\) :', assembly)
assert re.search(r'theorem whole_native_fixed \(κ m : ℝ\) \(hk : κ ∈ Set.Icc \(0 : ℝ\) 30\) :', assembly)
status = json.loads(read(PACKET + 'leaf_build_status.json'))
assert status['all_success'] and status['successful_targets'] == status['total_targets'] == 572
assert status['batch_size'] == 24 and len(status['terminal_batches']) == 24
targets = [PREFIX + mod for mod in LEAVES]
assert [t for row in status['terminal_batches'] for t in row['targets']] == targets
for i, row in enumerate(status['terminal_batches']):
    assert row['targets'] == targets[24*i:24*(i+1)]
    assert row['command'] == ['lake', 'build', *row['targets']]
    assert row['exit_code'] == 0 and row['elapsed_seconds'] > 0
leaf_log = read(PACKET + 'leaf_build.txt')
assert [json.loads(t) for t in re.findall(r'^Batch targets: (.*)$', leaf_log, re.M)] == [r['targets'] for r in status['terminal_batches']]
assert leaf_log.count('Build completed successfully') == 24
assert not re.search(r'error:|warning:|Build failed', leaf_log)
build = read(PACKET + 'lean_build.txt')
assert 'Build completed successfully (8782 jobs).' in build
assert not re.search(r'error:|warning:|Build failed', build)
version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT / 'lean').decode().strip()
assert version == prior['actual_lean_version_checked']
mathlib = dict(prior['mathlib'])
mathlib['direct_proof_source_sha256'] = dict(mathlib['direct_proof_source_sha256'])
libroot = ROOT / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert sha((libroot / p).read_bytes()) == h
extra = 'Mathlib/Order/Fin/Basic.lean'
mathlib['direct_proof_source_sha256'][extra] = sha((libroot / extra).read_bytes())
files = set(prior['source_sha256']) | {PRIOR, NEW_AUDIT, COMBINED,
    'lean/manifests/check_ground_continuation_axioms.lean', 'lean/manifests/check_ground_continuation_statements.lean',
    'math/GROUND_KERNEL_CONTINUATION_2026-10-04.md', 'scripts/de_ground_continuation_verify.py',
    'scripts/de_ground_continuation_generate.py', 'scripts/de_ground_continuation_family.py',
    'scripts/de_ground_continuation_build.py'}
files.update(sourcepath(m) for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT / PACKET).iterdir() if p.name != 'verification.json')
assert len(files) == 1201, len(files)
v = dict(baseline_commit=BASE, scope='Original full positive coupling branch instantiated in the Lean kernel on [0,30]',
    axiom_audit=dict(declarations_cumulative=2459, declarations_preserved=1870, declarations_fresh=589,
        new_local_theorems=new, axioms=['Classical.choice', 'Quot.sound', 'propext'],
        full_cumulative_command_rerun=False, preserved_raw_prefix=OLD_AUDIT,
        preserved_prefix_sha256=sha(oldraw.encode()), fresh_suffix_receipt=NEW_AUDIT,
        combined_receipt=COMBINED, success=True),
    lean_build=dict(command='lake build', jobs=8782, success=True, warnings_as_errors=True,
        receipt_trailing_whitespace_normalized=True, diagnostic_content_removed=False),
    concrete_leaf_build=dict(targets=572, terminal_batches=24, batch_size=24, success=True,
        status_receipt=PACKET+'leaf_build_status.json', raw_receipt=PACKET+'leaf_build.txt'),
    statement_check=dict(declarations=589, success=True), mathlib=mathlib, actual_lean_version_checked=version,
    original_return=dict(concrete_original_kernel_uniform_tubes=286, concrete_kernel_endpoint_anchors=287,
        concrete_uniform_radius='1/256', concrete_anchor_radius='1/4294967296',
        whole_286_tube_Lean_cover_instantiated=True, whole_real_coupling_interval=['0', '30'],
        finite_interval_coverage_and_actual_common_root_overlaps_earned=True,
        concrete_arithmetic_theorems_have_no_hypotheses=True,
        whole_actual_positive_unit_ground_energy_branch_C_infinity=True,
        whole_actual_legal_native_fixed_branch_exact_original_tolerance=True,
        sample_roots_and_identities_kernel_instantiated=False, determinant_signs_kernel_instantiated=False,
        frozen_initialization_basin=False, nonlinear_escape=False, all_interval_stability=False,
        IEEE_per_operation_emulation=False, JSON_or_IEEE_parsing_kernel_proved=False),
    exact_numeric_python_replay_fresh=False, rational_data_proposals_regenerated=True,
    prior_numeric_evidence_immutable_from_baseline=PRIOR,
    python_test_suite_rerun=False, paper_edited=False, original_runtime_edited=False,
    review='adversarial self-review, not independent review', goal_complete=False,
    next_construction='Concrete sample identity/spectral signs and feasible nonlinear instability/basin estimates',
    source_sha256={p: sha((ROOT / p).read_bytes()) for p in sorted(files)},
    git_blob_sha256={p: sha(canonical(p)) for p in sorted(files)})
(ROOT / PACKET / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print('2459 cumulative standard-only closures;589 fresh statements;full [0,30] kernel branch;1201 fingerprints')
