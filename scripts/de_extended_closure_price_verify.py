"""Verify exact extended-objective reduction, actual Schur return and infinity control."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = 'accb5e8'
packet = 'results/extended_closure_price_2026-10-03/'
mods = ['ExtendedClosurePrice', 'ExtendedSchurClosurePrice', 'ExtendedClosurePriceExamples']

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
assert len(new) == 24
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 929 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_extended_closure_price_axioms.lean'), re.M) == new
prior_path = 'results/convex_closure_price_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_convex_closure_price_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_extended_closure_price_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_extended_closure_price_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 929-declaration raw prefix plus freshly audited 24-declaration suffix.\n'
          'Baseline: accb5e8; earlier proof-source/toolchain identity checked by de_extended_closure_price_verify.py.\n'
          'Full 953-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_extended_closure_price_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(ExtendedClosurePrice|ExtendedSchurClosurePrice|ExtendedClosurePriceExamples)\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
generic = decls['ExtendedClosurePrice.positive_price_certificate']
for token in ['{J : E → EReal}', 'Convex ℝ (SbtCosmo.Derivation.ExtendedClosurePrice.epigraph A J)',
              '(hbottom : ∀ x ∈ A, J x ≠ ⊥)', '(hfinite : ∀ T ∈ Set.Ioo lo hi,',
              '≠ ⊤', '≠ ⊥', 'HasDerivAt', '.toReal', '(hs : d < 0)',
              'price = -d ∧ 0 < price ∧ energy star = B', 'DualCertificate A J energy B price star',
              'dualValue A J energy B price =']:
    assert token in generic, token
assert '(hactive :' not in generic and '(hdual :' not in generic
domain = decls['ExtendedClosurePrice.value_domain_return']
assert 'EReal' in domain and 'Nonempty' in domain and 'BddBelow' in domain
assert 'budgetValue' in domain and 'finiteDomain A J' in domain
assert 'ConvexOn ℝ' in decls['ExtendedClosurePrice.epigraph_objective_convex']
weak = decls['ExtendedClosurePrice.weak_duality']
assert '(hq : 0 ≤ q)' in weak and 'BddBelow' not in weak
assert '≠ ⊤' in decls['ExtendedClosurePrice.certificate_dual_finite']
assert '≠ ⊥' in decls['ExtendedClosurePrice.certificate_dual_finite']
schur = decls['ExtendedSchurClosurePrice.positive_schur_price']
assert '(hW : W.PosSemidef)' in schur and '(D : E →ᵃ[ℝ]' in schur
assert '(he :' not in schur and '(hactive :' not in schur
assert 'EReal' in schur and 'SchurClosurePrice.schurEnergy' in schur
example = decls['ExtendedClosurePriceExamples.actual_positive_certificate']
assert '(h' not in example and 'DualCertificate Set.univ' in example and '1 1 1' in example
assert 'HasDerivAt' in decls['ExtendedClosurePriceExamples.actual_value_derivative']
assert '(-1) 1' in decls['ExtendedClosurePriceExamples.actual_value_derivative']
control = decls['ExtendedClosurePriceExamples.unrestricted_toReal_false_value']
assert 'budgetValue Set.univ' in control and '= 0 ∧' in control and '= 1 ∧' in control and '= ⊤' in control

build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8110 jobs).' in build and not re.search(r'error:|warning:', build)
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
expected_config = old_config.replace('`SbtCosmo.Derivation.SchurClosurePriceExamples]',
    '`SbtCosmo.Derivation.SchurClosurePriceExamples, `SbtCosmo.Derivation.ExtendedClosurePrice, `SbtCosmo.Derivation.ExtendedSchurClosurePrice, `SbtCosmo.Derivation.ExtendedClosurePriceExamples]')
assert read('lean/lakefile.lean') == expected_config

lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root / 'lean/.lake/packages/mathlib').decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((root / 'lean/.lake/packages/mathlib' / p).read_bytes()) == h
for path in ['Mathlib/Data/EReal/Basic.lean', 'Mathlib/Data/EReal/Operations.lean',
             'Mathlib/Order/CompleteLattice/Basic.lean']:
    source = (root / 'lean/.lake/packages/mathlib' / path).read_bytes()
    assert source == subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=root / 'lean/.lake/packages/mathlib')
    mathlib['direct_proof_source_sha256'][path] = digest(source)
files = set(prior['source_sha256']) | {prior_path}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_extended_closure_price_verify.py', 'math/EXTENDED_CLOSURE_PRICE_LEAN_2026-10-03.md',
              'lean/manifests/check_extended_closure_price_statements.lean',
              'lean/manifests/check_extended_closure_price_axioms.lean', new_path, combined_path])
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
    'scope': 'Exact extended-real objective-domain reduction and actual scalar Schur price',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8110, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_extended_closure_price_axioms.lean',
                    'success': True, 'declarations_cumulative': 953, 'declarations_fresh': 24,
                    'declarations_preserved': 929, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_extended_closure_price_statements.lean',
                        'success': True, 'declarations': 24, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'objective': 'EReal-valued, nowhere minus infinity on A; convex real epigraph',
        'domain': 'A intersect {J not plus infinity}; its convexity and real objective convexity derived',
        'primal_value': 'actual complete-lattice infimum, exactly equal to coe of restricted finite real infimum',
        'local_finiteness': 'actual EReal value neither top nor bottom; finite-cost guards derived',
        'derivative': 'of toReal of actual EReal value, on its proved finite neighborhood',
        'primal_optimum_supplied': True, 'certificate_or_activity_supplied': False,
        'constructed_price': '-actual value derivative > 0', 'activity_derived': True,
        'global_extended_lagrangian_minimum': True, 'actual_extended_primal_dual_equality': True,
        'certificate_dual_finiteness_derived': True,
        'competing_dual_weak_bound': 'nonnegative price, complete-lattice infimum; minus infinity safely allowed',
        'actual_schur_energy_convexity_earned': 'fixed native L, PSD W, affine dissolving D; singular ranks allowed',
        'complete_example': 'Schur e=x^2, J=(x-2)^2 for x>=0 and plus infinity otherwise; price1 at B1',
        'false_conversion_control': 'unrestricted toReal value0 via forbidden x=-1; actual extended value1',
        'split_subdifferentials_or_normal_cone_mechanized': False,
        'matrix_Loewner_dual_mechanized': False, 'physical_Lambda_bridge': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review',
    'next_construction': 'Qualified split subdifferential/normal-cone or matrix Loewner return; physical identification remains parked',
    'goal_complete': False,
    'source_sha256': hashes, 'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'953 ordered cumulative standard-only closures (929 immutable + 24 fresh), 24 extended-infimum/Schur/control statements; {len(hashes)} fingerprints.')
