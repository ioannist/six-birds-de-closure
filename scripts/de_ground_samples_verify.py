"""Audit concrete original coupling thin roots and actual derivative enclosures.

Prior numerical verdicts are protected historical evidence. New numeric proofs
are Lean-kernel reductions returned to actual roots and selector derivatives.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = '82a6077'
PRIOR = 'results/ground_escape_2026-10-04/verification.json'
PACKET = 'results/ground_samples_2026-10-04/'
PREFIX = 'SbtCosmo.Derivation.'
MODS = ['GroundBorderResponse', *[f'GroundSamples.Point{i:03d}' for i in range(14)],
        'GroundOriginalSamples', *[f'GroundResponses.Point{i:03d}' for i in range(14)],
        'GroundOriginalResponses', 'GroundResponseControls']
ROOTS = ['GroundBorderResponse', 'GroundOriginalSamples', 'GroundOriginalResponses', 'GroundResponseControls']
OLD_AUDIT = 'lean/manifests/axiom_audit_ground_escape_2026-10-04.txt'
NEW_AUDIT = 'lean/manifests/axiom_audit_ground_samples_new_2026-10-04.txt'
COMBINED = 'lean/manifests/axiom_audit_ground_samples_2026-10-04.txt'
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
    return t.replace('| ', '|').replace(' |', '|').replace('‖ ', '‖').replace(' ‖', '‖').replace('↑ ', '↑')


def sourcepath(mod):
    return 'lean/' + (PREFIX + mod).replace('.', '/') + '.lean'


prior = json.loads(read(PRIOR))
assert (ROOT / PRIOR).read_bytes() == baseline(PRIOR)
assert len(prior['source_sha256']) == 1212
for p, h in prior['source_sha256'].items():
    if p not in MUTABLE:
        assert sha((ROOT / p).read_bytes()) == h and canonical(p) == baseline(p), p
assert len(MODS) == 32
new = []
for mod in MODS:
    source = read(sourcepath(mod))
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', source), mod
    new += [PREFIX + mod + '.' + n for n in re.findall(r'^theorem ([\w.]+)', source, re.M)]
assert len(new) == 57 and len(set(new)) == 57
old_manifest = baseline('lean/manifests/check_axioms.lean').decode()
old = re.findall(r'^#print axioms (\S+)', old_manifest, re.M)
assert len(old) == 2477
imports = ''.join('import ' + PREFIX + mod + '\n' for mod in MODS)
assert read('lean/manifests/check_axioms.lean') == old_manifest + '\n' + imports + '\n' + ''.join('#print axioms ' + n + '\n' for n in new)
assert read('lean/lakefile.lean') == baseline('lean/lakefile.lean').decode()[:-2] + ',\n    ' + ', '.join('`' + PREFIX + mod for mod in ROOTS) + ']\n'
for suffix, cmd in [('axioms', '#print axioms '), ('statements', '#check ')]:
    assert read('lean/manifests/check_ground_samples_' + suffix + '.lean') == imports + '\n' + ''.join(cmd + n + '\n' for n in new)
assert (ROOT / OLD_AUDIT).read_bytes() == baseline(OLD_AUDIT)
oldraw, newraw = read(OLD_AUDIT), read(NEW_AUDIT)
closures(oldraw, old)
closures(newraw, new)
header = ('Cumulative audit: immutable 2477-declaration raw prefix plus freshly audited 57-declaration suffix.\n'
          'Baseline: 82a6077; proof-source/toolchain identity checked by de_ground_samples_verify.py.\n'
          'Full 2534-declaration command was not rerun in this packet.\n\n')
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
    decls[m.group().rstrip('.')] = flatten(t.replace(PREFIX, '').replace('⇑', ''))


def require(name, *tokens):
    for token in tokens:
        assert flatten(token) in decls[PREFIX + name], (name, token, decls[PREFIX + name])


for i in range(14):
    name = f'Point{i:03d}'
    require('GroundSamples.' + name + '.arithmetic', 'GroundKernelTube.Arithmetic',
            'GroundOriginalFirstTube.originalBackground', *['GroundSamples.' + name + '.' + k for k in ['a', 'c', 'z', 'r', 'q', 'y', 'C']])
    require('GroundResponses.' + name + '.arithmetic', 'GroundBorderResponse.Arithmetic',
            'GroundOriginalFirstTube.originalBackground', *['GroundSamples.' + name + '.' + k for k in ['a', 'z', 'r']],
            *['GroundResponses.' + name + '.' + k for k in ['C', 'q', 'y', 'error']])
    assert '→' not in decls[PREFIX + 'GroundSamples.' + name + '.arithmetic']
    assert '→' not in decls[PREFIX + 'GroundResponses.' + name + '.arithmetic']
require('GroundBorderResponse.linear_response_error_mul', 'hy : L y = r', '0 ≤ q',
        '‖ContinuousLinearMap.id ℝ E - C.comp L‖ ≤ q', '1 - q * ‖y - C r‖ ≤ q * ‖C r‖')
require('GroundBorderResponse.borderExpr_return', 'Expr.eval', 'GroundBorderResponse.borderOperator', 'GroundPointCoordinates.column')
require('GroundBorderResponse.rhsExpr_return', 'Expr.eval', 'GroundBorderResponse.rhs')
require('GroundBorderResponse.response_equation', 'GroundBorder.groundPair',
        'GroundBorderResponse.borderOperator b κ x GroundBorderResponse.response b κ x j = GroundBorderResponse.rhs b κ x j')
require('GroundBorderResponse.response_field', 'GroundSourceJacobian.jacobian b κ x.1', 'GroundLocalDynamics.column j')
require('GroundBorderResponse.response_error', 'hbudget : q * y ≤ e * 1 - q',
        'GroundBorder.groundPair', '‖GroundBorderResponse.response', '≤ ↑e')
require('GroundBorderResponse.halfInterval_sound', 'GroundBorderResponse.Arithmetic',
        'GroundBorder.groundPair', 'GroundSourceJacobian.groundMap',
        'GroundNormalizedJacobian.normalizedJacobian', 'GroundLocalDynamics.column j')
require('GroundOriginalSamples.root_eq_branch', 'i : Fin 14', 'GroundOriginalSamples.points i .toTube.root',
        '= GroundOriginalContinuation.branch')
require('GroundOriginalSamples.branch_in_sample_ball', 'i : Fin 14', 'GroundOriginalContinuation.branch',
        'Metric.closedBall GroundKernelTube.center GroundOriginalSamples.points i .z')
require('GroundOriginalSamples.sample_ground_return', 'i : Fin 14', 'GroundRootCertificate.residual',
        'GroundState.normSq', 'GroundBorder.groundPair', 'GroundSourceJacobian.groundMap')
require('GroundOriginalResponses.actual_response_error', 'i : Fin 14', 'j : Fin 8',
        'GroundOriginalContinuation.branch', 'GroundBorderResponse.response', 'GroundBorderResponse.rhs',
        '≤ ↑GroundOriginalResponses.certificates i .error j')
require('GroundOriginalResponses.actual_half_entries', 'i : Fin 14', 'a j : Fin 8',
        'GroundOriginalResponses.enclosures i a j .Contains', 'GroundNormalizedJacobian.normalizedJacobian',
        'GroundOriginalContinuation.branch', 'GroundLocalDynamics.column j')
require('GroundResponseControls.zero_border_preconditioner_rejected', '¬GroundBorderResponse.Arithmetic',
        'GroundSamples.Point010', 'fun x x_1 => 0')
require('GroundResponseControls.zero_error_budget_rejected', '¬GroundBorderResponse.Arithmetic',
        'GroundResponses.Point010.C', 'fun x => 0')
# Constructors/inputs have exact required shapes; numerical generators only
# propose data. Regeneration below is read-only and supplies no proof oracle.
src = flatten(read(sourcepath('GroundBorderResponse')))
for token in ['budget : ∀ j, q*y j ≤ e j*(1-q)', 'defect_rows : ∀ i,', 'rhs_rows : ∀ j i,',
              'error_nonneg : ∀ j, 0 ≤ e j', 'pairDerivative (sourcePotential b κ x.1)',
              '((halfNominalExpr C i j).enclose (box β a a z r)).add ⟨-(e j)/2, (e j)/2⟩']:
    assert flatten(token) in src, token
import de_ground_samples_generate as sg
import de_ground_samples_family as sf
import de_ground_response_generate as rg
import de_ground_response_family as rf
roots, responses = sg.proposals(), rg.proposals()
assert len(roots) == len(responses) == 14
assert all(d['r'].denominator == 2**32 and d['r'].numerator == 1 for d in roots)
assert roots[10]['a'] == 20 and roots[11]['a'] == 30 and roots[12]['a'] == sg.F(79, 5) and roots[13]['a'] == sg.F(159, 10)
assert responses[0]['y'] == responses[0]['error'] == [0]*8
assert max(max(d['error']) for d in responses) < sg.F('0.00000002406')
for i, (d, e) in enumerate(zip(roots, responses)):
    root_source = read(sourcepath(f'GroundSamples.Point{i:03d}'))
    resp_source = read(sourcepath(f'GroundResponses.Point{i:03d}'))
    assert root_source == sg.render(i, d) and root_source.count('decide +kernel') == 8
    assert resp_source == rg.render(i, e) and resp_source.count('decide +kernel') == 7
assert read(sourcepath('GroundOriginalSamples')) == sf.render()
assert read(sourcepath('GroundOriginalResponses')) == rf.render()
assert read(sourcepath('GroundOriginalSamples')).count('decide +kernel') == 3
assert 'Fin.cases' in read(sourcepath('GroundOriginalResponses'))
assert read(sourcepath('GroundResponseControls')).count('decide +kernel') == 2
for receipt, ns in [('leaf_build.txt', 'GroundSamples'), ('response_build.txt', 'GroundResponses')]:
    raw = read(PACKET + receipt)
    command = json.loads(raw.splitlines()[0].removeprefix('Command: '))
    assert command == ['lake', 'build', *[PREFIX+ns+f'.Point{i:03d}' for i in range(14)]]
    assert 'Build completed successfully' in raw and raw.endswith('Terminal exit code: 0\n')
    assert not re.search(r'error:|warning:|Build failed', raw)
build = read(PACKET + 'lean_build.txt')
assert 'Build completed successfully (8815 jobs).' in build
assert not re.search(r'error:|warning:|Build failed', build)
version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT / 'lean').decode().strip()
assert version == prior['actual_lean_version_checked']
mathlib = prior['mathlib']
libroot = ROOT / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert sha((libroot / p).read_bytes()) == h
files = set(prior['source_sha256']) | {PRIOR, NEW_AUDIT, COMBINED,
    'lean/manifests/check_ground_samples_axioms.lean', 'lean/manifests/check_ground_samples_statements.lean',
    'math/GROUND_KERNEL_SAMPLES_2026-10-04.md', 'scripts/de_ground_samples_verify.py',
    'scripts/de_ground_samples_generate.py', 'scripts/de_ground_samples_family.py',
    'scripts/de_ground_response_generate.py', 'scripts/de_ground_response_family.py'}
files.update(sourcepath(m) for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT / PACKET).iterdir() if p.name != 'verification.json')
assert len(files) == 1260, len(files)
v = dict(baseline_commit=BASE, scope='Original coupling sample/probe root identities and actual normalized derivative entry enclosures in the Lean kernel',
    axiom_audit=dict(declarations_cumulative=2534, declarations_preserved=2477, declarations_fresh=57,
        new_local_theorems=new, axioms=['Classical.choice', 'Quot.sound', 'propext'],
        full_cumulative_command_rerun=False, preserved_raw_prefix=OLD_AUDIT,
        preserved_prefix_sha256=sha(oldraw.encode()), fresh_suffix_receipt=NEW_AUDIT,
        combined_receipt=COMBINED, success=True),
    lean_build=dict(command='lake build', jobs=8815, success=True, warnings_as_errors=True,
        receipt_trailing_whitespace_normalized=True, diagnostic_content_removed=False),
    statement_check=dict(declarations=57, success=True), mathlib=mathlib, actual_lean_version_checked=version,
    original_return=dict(original_coupling_sample_kernel_roots=12, crossing_probe_kernel_roots=2,
        all_12_coupling_sample_and_2_probe_branch_identities_kernel_proved=True,
        all_30_original_sample_kernel_instances=False, original_background_offset_kernel_roots=0,
        thin_radius='1/4294967296', actual_border_expression_return=True,
        actual_selector_response_equation_and_field_derivative_return=True,
        actual_near_inverse_response_error_loss_earned=True,
        original_root_box_response_arithmetic_kernel_instances=14,
        actual_normalized_half_mixing_derivative_entry_kernel_enclosures=14,
        concrete_numeric_arithmetic_theorems_have_no_hypotheses=True,
        lawful_zero_coupling_response_budgets=True,
        false_certificate_controls=['zero_border_preconditioner_at20', 'zero_response_error_budget_at20'],
        basis_inverse_and_coordinate_norm_kernel_instantiated=False,
        determinant_signs_kernel_instantiated=False, numerical_native_attraction_and_escape_kernel_instantiated=False,
        frozen_initialization_basin=False, all_interval_stability=False,
        IEEE_per_operation_emulation=False, JSON_or_IEEE_parsing_kernel_proved=False),
    exact_numeric_python_replay_fresh=False, rational_data_proposals_regenerated=True,
    prior_numeric_evidence_immutable_from_baseline=PRIOR,
    python_test_suite_rerun=False, paper_edited=False, original_runtime_edited=False,
    review='adversarial self-review, not independent review', goal_complete=False,
    next_construction='Exact basis inverses, actual transformed row norms and determinant signs; frozen-init basin estimates',
    source_sha256={p: sha((ROOT / p).read_bytes()) for p in sorted(files)},
    git_blob_sha256={p: sha(canonical(p)) for p in sorted(files)})
(ROOT / PACKET / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print('2534 cumulative standard-only closures;57 fresh statements;14 original thin identities and actual derivative matrices;1260 fingerprints')
