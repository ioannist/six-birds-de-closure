"""Verify concrete original kernel tube, fresh Lean receipts and provenance.

The first concrete tube is checked by fresh Lean build and declaration receipts.
Prior Python numeric certificates are protected historical evidence; their
arithmetic is not claimed freshly replayed by this script.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = '8df8d41'
PACKET = 'results/ground_kernel_2026-10-04/'
PRIOR = 'results/ground_patch_2026-10-04/verification.json'
MODS = ['GroundRationalInterval', 'GroundPointCoordinates', 'GroundResidualEnclosure', 'GroundKernelTube', 'GroundOriginalFirstTube']
PREFIX = 'SbtCosmo.Derivation.'
OLD_AUDIT = 'lean/manifests/axiom_audit_ground_patch_2026-10-04.txt'
NEW_AUDIT = 'lean/manifests/axiom_audit_ground_kernel_new_2026-10-04.txt'
COMBINED = 'lean/manifests/axiom_audit_ground_kernel_2026-10-04.txt'
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


prior = json.loads(read(PRIOR))
assert (ROOT / PRIOR).read_bytes() == baseline(PRIOR)
assert len(prior['source_sha256']) == 595
for p, h in prior['source_sha256'].items():
    if p not in MUTABLE:
        assert sha((ROOT / p).read_bytes()) == h and canonical(p) == baseline(p), p
new = []
for mod in MODS:
    source = read('lean/SbtCosmo/Derivation/' + mod + '.lean')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', source)
    new += [PREFIX + mod + '.' + n for n in re.findall(r'^theorem ([\w.]+)', source, re.M)]
assert len(new) == 40
old_manifest = baseline('lean/manifests/check_axioms.lean').decode()
old = re.findall(r'^#print axioms (\S+)', old_manifest, re.M)
assert len(old) == 1830
imports = ''.join('import ' + PREFIX + mod + '\n' for mod in MODS)
assert read('lean/manifests/check_axioms.lean') == old_manifest + '\n' + imports + '\n' + ''.join('#print axioms ' + n + '\n' for n in new)
assert read('lean/lakefile.lean') == baseline('lean/lakefile.lean').decode()[:-2] + ',\n    ' + ', '.join('`' + PREFIX + mod for mod in MODS) + ']\n'
for suffix, cmd in [('axioms', '#print axioms '), ('statements', '#check ')]:
    assert read('lean/manifests/check_ground_kernel_' + suffix + '.lean') == imports + '\n' + ''.join(cmd + n + '\n' for n in new)
assert (ROOT / OLD_AUDIT).read_bytes() == baseline(OLD_AUDIT)
oldraw, newraw = read(OLD_AUDIT), read(NEW_AUDIT)
closures(oldraw, old)
closures(newraw, new)
header = ('Cumulative audit: immutable 1830-declaration raw prefix plus freshly audited 40-declaration suffix.\n'
          'Baseline: 8df8d41; proof-source/toolchain identity checked by de_ground_kernel_verify.py.\n'
          'Full 1870-declaration command was not rerun in this packet.\n\n')
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


I, P, R, K, O = [m + '.' for m in MODS]
require(I + 'Interval.mul_sound', 'a.Contains x', 'b.Contains y', 'a.mul b .Contains x * y')
require(I + 'Expr.enclose_sound', '∀ i : V, B i .Contains σ i', 'Expr.enclose B e .Contains Expr.eval σ e')
require(P + 'coord_fromCoord', 'coord fromCoord v = v')
require(P + 'fromCoord_coord', 'fromCoord coord x = x')
require(P + 'operator_norm_le_rows', 'q : ℝ', '0 ≤ q', '∑ j, |coord L column j i|', '‖L‖ ≤ q')
require(R + 'residualExpr_return', 'Expr.eval valuation b κ x residualExpr j = coord residual b κ x j')
require(R + 'derivativeExpr_return', 'Expr.eval valuation b κ x derivativeExpr j i', 'coord residualDerivative b κ x column j i')
require(R + 'defectExpr_return', 'correctionDerivative b κ preconditioner C x column j')
require(R + 'defect_norm_bound', 'q : ℚ', 'hrows : ∀ i : Fin 9', '‖correctionDerivative b κ preconditioner C x‖ ≤ ↑q')
require(R + 'corrected_residual_norm_bound', 'hbound : ∀ i : Fin 9', '‖preconditioner C residual b κ x‖ ≤ ↑y')
require(K + 'box_sound', 'κ ∈ Set.Icc ↑a ↑c', 'x ∈ Metric.closedBall center z ↑r',
        'v : Variable', 'box β a c z r v .Contains valuation background β κ x v')
require(K + 'certified_actual_root', 'h : Arithmetic β a c z r q y C', 'residual background β κ x = 0',
        'groundMap background β κ x.1 = x.1', 'residual background β κ t = 0 → t = x')
require(O + 'arithmetic', 'Arithmetic originalBackground 0 15 / 128 originalCenter 1 / 256 1 / 10 3 / 1000 originalPreconditioner')
require(O + 'original_positive_root', 'κ ∈ Set.Icc 0 15 / 128',
        '∃ x ∈ Metric.closedBall center originalCenter 1 / 256', 'residual background originalBackground κ x = 0',
        'IsGround sourcePotential background originalBackground κ x.1 x.1 x.2',
        'groundMap background originalBackground κ x.1 = x.1',
        'residual background originalBackground κ t = 0 → t = x')
require(O + 'original_smooth_branch', 'ContDiffOn ℝ ↑⊤ originalTube.root Set.Icc 0 15 / 128')
require(O + 'zero_preconditioner_rejected', '¬Arithmetic originalBackground 0 15 / 128 originalCenter 1 / 256 1 / 10 3 / 1000 fun x x_1 => 0')
require(O + 'false_residual_budget_rejected', '¬Arithmetic originalBackground 0 15 / 128 originalCenter 1 / 256 1 / 10 1 originalPreconditioner')
# Concrete numeric theorem has no supplied proof premises; the data generator is
# checked by exact source regeneration, but its output is not a theorem premise.
import de_ground_kernel_tube_generate as gen
assert read('lean/SbtCosmo/Derivation/GroundOriginalFirstTube.lean') == gen.render()
arithmetic_source = read('lean/SbtCosmo/Derivation/GroundOriginalFirstTube.lean').split('theorem arithmetic', 1)[1].split('def originalTube', 1)[0]
assert arithmetic_source.count('decide +kernel') == 8
kernel_source = flatten(read('lean/SbtCosmo/Derivation/GroundKernelTube.lean'))
for token in ['strict_invariance : y + q*r < r',
              'positive : ∀ i : Fin 8, 0 < z i.castSucc - r',
              'defect_rows : ∀ i : Fin 9,', 'residual_rows : ∀ i : Fin 9,',
              'r q y : ℚ']:
    assert flatten(token) in kernel_source, token
build = read(PACKET + 'lean_build.txt')
assert 'Build completed successfully (8207 jobs).' in build
assert not re.search(r'error:|warning:|Build failed', build)
version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT / 'lean').decode().strip()
assert version == prior['actual_lean_version_checked']
mathlib = prior['mathlib']
libroot = ROOT / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert sha((libroot / p).read_bytes()) == h
files = set(prior['source_sha256']) | {PRIOR, NEW_AUDIT, COMBINED,
    'lean/manifests/check_ground_kernel_axioms.lean', 'lean/manifests/check_ground_kernel_statements.lean',
    'math/GROUND_KERNEL_TUBE_2026-10-04.md', 'scripts/de_ground_kernel_verify.py', 'scripts/de_ground_kernel_tube_generate.py'}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT / PACKET).iterdir() if p.name != 'verification.json')
assert len(files) == 611, len(files)
v = dict(baseline_commit=BASE, scope='First actual original uniform Newton tube fully instantiated inside Lean',
    axiom_audit=dict(declarations_cumulative=1870, declarations_preserved=1830, declarations_fresh=40,
        new_local_theorems=new, axioms=['Classical.choice', 'Quot.sound', 'propext'],
        full_cumulative_command_rerun=False, preserved_raw_prefix=OLD_AUDIT,
        preserved_prefix_sha256=sha(oldraw.encode()), fresh_suffix_receipt=NEW_AUDIT,
        combined_receipt=COMBINED, success=True),
    lean_build=dict(command='lake build', jobs=8207, success=True, warnings_as_errors=True,
        receipt_trailing_whitespace_normalized=True, diagnostic_content_removed=False),
    statement_check=dict(declarations=40, success=True), mathlib=mathlib, actual_lean_version_checked=version,
    original_return=dict(signed_rational_interval_arithmetic_soundness=True,
        actual_nine_coordinate_product_sup_operator_norm_bridge=True,
        polynomial_expression_return_to_actual_residual_and_earned_derivative=True,
        actual_defect_and_center_residual_norms_derived_from_rational_enclosures=True,
        concrete_original_kernel_uniform_tubes=1, concrete_kernel_tube_interval=['0', '15/128'],
        concrete_defect_bound='1/10', concrete_center_residual_bound='3/1000', concrete_radius='1/256',
        concrete_actual_positive_root_and_smooth_branch=True,
        first_tube_arithmetic_theorem_has_no_hypotheses=True,
        kernel_false_certificate_controls=['zero_preconditioner', 'impossible_residual_budget'],
        whole_286_tube_Lean_cover_instantiated=False, all_anchors_sample_roots_kernel_instantiated=False,
        determinant_signs_kernel_instantiated=False, frozen_initialization_basin=False,
        nonlinear_escape=False, all_interval_stability=False,
        IEEE_per_operation_emulation=False, JSON_or_IEEE_parsing_kernel_proved=False),
    exact_numeric_python_replay_fresh=False, prior_numeric_evidence_immutable_from_baseline=PRIOR,
    python_test_suite_rerun=False, paper_edited=False, original_runtime_edited=False,
    review='adversarial self-review, not independent review', goal_complete=False,
    next_construction='Extend actual kernel tube/anchor/sample/sign certificates; original-init basin bounds',
    source_sha256={p: sha((ROOT / p).read_bytes()) for p in sorted(files)},
    git_blob_sha256={p: sha(canonical(p)) for p in sorted(files)})
(ROOT / PACKET / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print('1870 cumulative standard-only closures;40 fresh statements;first original tube kernel-certified;611 fingerprints')
