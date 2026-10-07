"""Verify constructed differentiable conic/Schur matrix price and PSD trace return."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = 'ac531fe'
packet = 'results/matrix_closure_price_2026-10-03/'
mods = ['ConeClosurePrice', 'MatrixPriceRepresentation', 'MatrixClosurePrice', 'MatrixClosurePriceExamples']

def read(p):
    return (root / p).read_text()

def digest(b):
    return hashlib.sha256(b).hexdigest()

def git_blob(ref, p):
    return subprocess.check_output(['git', 'show', ref + ':' + p], cwd=root)

def closure_gate(raw, names):
    entries = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", raw)
    assert [n for n, _ in entries] == names
    assert not re.search(r'error:|warning:|sorryAx', raw)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    actual = set()
    for name, axioms in entries:
        axs = {a.strip() for a in axioms.split(',') if a.strip()}
        assert axs <= allowed, (name, axs)
        actual.update(axs)
    assert actual == allowed
    return actual

new = []
for mod in mods:
    src = read('lean/SbtCosmo/Derivation/' + mod + '.lean')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', src)
    new += ['SbtCosmo.Derivation.' + mod + '.' + n for n in re.findall(r'^theorem (\w+)', src, re.M)]
assert len(new) == 32
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 953 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_matrix_closure_price_axioms.lean'), re.M) == new
prior_path = 'results/extended_closure_price_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_extended_closure_price_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_matrix_closure_price_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_matrix_closure_price_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 953-declaration raw prefix plus freshly audited 32-declaration suffix.\n'
          'Baseline: ac531fe; earlier proof-source/toolchain identity checked by de_matrix_closure_price_verify.py.\n'
          'Full 985-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_matrix_closure_price_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(ConeClosurePrice|MatrixPriceRepresentation|MatrixClosurePrice|MatrixClosurePriceExamples)\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
generic = decls['ConeClosurePrice.price_certificate']
for token in ['HasFDerivAt', 'ConeClosurePrice.value A J energy positive', 'ConeLaws positive',
              'ConvexOn ℝ A J', 'PrimalOptimum A J energy positive B star', 'Nonempty', 'BddBelow',
              'DualCertificate A J energy positive B (-d) star']:
    assert token in generic, token
assert '(hactive :' not in generic and '(hdual :' not in generic
assert '(H : F) : positive H → d H ≤ 0' in decls['ConeClosurePrice.derivative_nonpositive_on_cone']
representation = decls['MatrixPriceRepresentation.trace_representation']
assert 'Symmetric n' in representation and ').trace = p M' in representation
assert 'hpositive' in decls['MatrixPriceRepresentation.price_matrix_positive']
assert 'PosSemidef' in decls['MatrixPriceRepresentation.price_matrix_positive']
assert 'priceMatrix p ≠ 0' in decls['MatrixPriceRepresentation.price_matrix_nonzero']
loewner = decls['MatrixClosurePrice.residual_loewner_convex']
assert 'positive' in loewner and 'residual L' in loewner
matrix = decls['MatrixClosurePrice.matrix_price']
for token in ['(D : E →ᵃ[ℝ]', 'Symmetric m', 'HasFDerivAt', 'ConeClosurePrice.value',
              '(hs : ∃ H,', '.positive H ∧ d H < 0', 'P.PosSemidef ∧ P ≠ 0',
              '∀ (H :', ').trace = -d H', 'sInf', 'Nonempty', 'BddBelow']:
    assert token in matrix, token
assert '(he :' not in matrix and '(hactive :' not in matrix and '(hdual :' not in matrix
example = decls['MatrixClosurePriceExamples.actual_matrix_price']
assert '(h' not in example and 'P.PosSemidef ∧ P ≠ 0' in example
assert 'HasFDerivAt' in decls['MatrixClosurePriceExamples.actual_value_derivative']
assert '(-SbtCosmo.Derivation.MatrixClosurePriceExamples.coordinate)' in decls['MatrixClosurePriceExamples.actual_value_derivative']
assert 'ConeClosurePrice.value' in decls['MatrixClosurePriceExamples.value_return']
control = decls['MatrixClosurePriceExamples.partial_slack_control']
assert 'P.PosSemidef ∧ S.PosSemidef ∧ P ≠ 0 ∧ S ≠ 0 ∧ (P * S).trace = 0' in control

build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8114 jobs).' in build and not re.search(r'error:|warning:', build)
review = read(packet + 'self_review.txt')
assert 'Adversarial self-review, not independent review' in review

# Freeze all earlier proofs/evidence. Only cumulative metadata can grow.
mutable = {'README.md', 'lean/README.md', 'lean/lakefile.lean', 'lean/manifests/check_axioms.lean',
           'lean/manifests/coverage_table.md', 'math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}
for p, h in prior['source_sha256'].items():
    if p not in mutable:
        assert digest((root / p).read_bytes()) == h, p
        assert digest(git_blob(baseline, p)) == prior['git_blob_sha256'][p], p
for ref, paths in [('6a71e6c', ['paper', 'external']), (baseline, ['sbt_cosmo', 'tests', 'results/DE_window', 'results/DE_dual'])]:
    assert subprocess.check_output(['git', 'diff', '--name-only', ref, '--', *paths], cwd=root) == b''
tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', baseline], cwd=root).decode().splitlines()
protected = [p for p in tracked if p not in mutable and p.startswith(('scripts/', 'lean/', 'results/', 'math/'))]
assert subprocess.check_output(['git', 'diff', '--name-only', baseline, '--', *protected], cwd=root) == b''
old_config = git_blob(baseline, 'lean/lakefile.lean').decode()
expected_config = old_config.replace('`SbtCosmo.Derivation.ExtendedClosurePriceExamples]',
    '`SbtCosmo.Derivation.ExtendedClosurePriceExamples, `SbtCosmo.Derivation.ConeClosurePrice, `SbtCosmo.Derivation.MatrixPriceRepresentation, `SbtCosmo.Derivation.MatrixClosurePrice, `SbtCosmo.Derivation.MatrixClosurePriceExamples]')
assert read('lean/lakefile.lean') == expected_config

lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root / 'lean/.lake/packages/mathlib').decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((root / 'lean/.lake/packages/mathlib' / p).read_bytes()) == h
for path in ['Mathlib/Data/Matrix/Basis.lean', 'Mathlib/Analysis/Calculus/LineDeriv/Basic.lean',
             'Mathlib/Analysis/Matrix/Normed.lean', 'Mathlib/LinearAlgebra/Matrix/PosDef.lean']:
    source = (root / 'lean/.lake/packages/mathlib' / path).read_bytes()
    assert source == subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=root / 'lean/.lake/packages/mathlib')
    mathlib['direct_proof_source_sha256'][path] = digest(source)
files = set(prior['source_sha256']) | {prior_path}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_matrix_closure_price_verify.py', 'math/MATRIX_CLOSURE_PRICE_LEAN_2026-10-03.md',
              'lean/manifests/check_matrix_closure_price_statements.lean',
              'lean/manifests/check_matrix_closure_price_axioms.lean', new_path, combined_path])
files.update(str(p.relative_to(root)) for p in (root / packet).iterdir() if p.name != 'verification.json')
hashes = {p: digest((root / p).read_bytes()) for p in sorted(files)}
git_hashes, normalized = {}, []
for p in sorted(files):
    blob = (root / p).read_bytes()
    if b'\r\n' in blob:
        attrs = subprocess.check_output(['git', 'check-attr', 'text', 'eol', '--', p], cwd=root).decode()
        assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in blob, p
        blob = blob.replace(b'\r\n', b'\n')
        normalized.append(p)
    git_hashes[p] = digest(blob)
v = {
    'baseline_commit': baseline,
    'scope': 'Construct differentiable-value conic/Schur matrix price, exact PSD trace representation and complementarity',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8114, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_matrix_closure_price_axioms.lean',
                    'success': True, 'declarations_cumulative': 985, 'declarations_fresh': 32,
                    'declarations_preserved': 953, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_matrix_closure_price_statements.lean',
                        'success': True, 'declarations': 32, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'budget_space': 'actual real symmetric matrices, elementwise norm topology',
        'value': 'actual nonempty bounded-below conic feasible-cost real infimum near budget B',
        'derivative': 'actual Frechet derivative on symmetric budget space, explicitly supplied',
        'primal_optimum_supplied': True, 'dual_or_complementarity_supplied': False,
        'constructed_price': 'minus actual value derivative, cone positivity derived',
        'trace_representation': 'explicit symmetrized matrix-unit coordinates, exact on all symmetric budgets',
        'matrix_PSD_derived': 'positivity tested on actual rank-one PSD directions',
        'nonzero_price': 'strict negative actual derivative in at least one PSD direction',
        'complementarity_derived': True, 'full_matrix_activity_assumed': False,
        'actual_primal_dual_infimum_equality': True, 'dual_finite_guards_derived': True,
        'actual_schur_residual': 'constructed singular-support generalized inverse, exact blind Gram',
        'Loewner_convexity_earned': 'fixed native L, affine dissolving D; exact matrix Gram mixing identity',
        'complete_example': 'one-by-one actual Schur budget; exact scalar return constructs actual value derivative and PSD matrix price',
        'partial_slack_control': 'P=diag(1,0), S=diag(0,1), both nonzero PSD, trace(P*S)=0',
        'general_nonsmooth_Slater_duality_mechanized': False,
        'matrix_extended_objective_reduction_mechanized': False,
        'split_subdifferentials_or_normal_cone_mechanized': False, 'physical_Lambda_bridge': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review',
    'next_construction': 'General nonsmooth Slater duality, qualified split stationarity or matrix extended-objective return; physical identification remains parked',
    'goal_complete': False,
    'source_sha256': hashes, 'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'985 ordered cumulative standard-only closures (953 immutable + 32 fresh), 32 conic/matrix/Loewner/control statements; {len(hashes)} fingerprints.')
