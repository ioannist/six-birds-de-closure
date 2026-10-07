"""Verify one canonical scalar price, full nonsmooth qualified stationarity and actual Schur return."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
baseline = 'c61cf67'
packet = 'results/scalar_stationarity_2026-10-03/'
mods = ['ScalarPriceStationarity', 'ScalarSchurStationarity', 'ScalarStationarityExamples']


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
assert len(new) == 19
old_names = re.findall(r'^#print axioms (\S+)', git_blob(baseline, 'lean/manifests/check_axioms.lean').decode(), re.M)
all_names = re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_axioms.lean'), re.M)
assert len(old_names) == 1111 and all_names == old_names + new
assert re.findall(r'^#print axioms (\S+)', read('lean/manifests/check_scalar_stationarity_axioms.lean'), re.M) == new
prior_path = 'results/schur_differential_2026-10-03/verification.json'
assert (root / prior_path).read_bytes() == git_blob(baseline, prior_path)
prior = json.loads(read(prior_path))
old_path = 'lean/manifests/axiom_audit_schur_differential_2026-10-03.txt'
old_raw = read(old_path)
assert (root / old_path).read_bytes() == git_blob(baseline, old_path)
assert digest((root / old_path).read_bytes()) == prior['source_sha256'][old_path]
closure_gate(old_raw, old_names)
new_path = 'lean/manifests/axiom_audit_scalar_stationarity_new_2026-10-03.txt'
new_raw = read(new_path)
actual = closure_gate(new_raw, new)
combined_path = 'lean/manifests/axiom_audit_scalar_stationarity_2026-10-03.txt'
header = ('Cumulative audit: exact immutable earlier 1111-declaration raw prefix plus freshly audited 19-declaration suffix.\n'
          'Baseline: c61cf67; earlier proof-source/toolchain identity checked by de_scalar_stationarity_verify.py.\n'
          'Full 1130-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closure_gate(combined, all_names)
(root / combined_path).write_text(combined)

checks = re.findall(r'^#check (\S+)', read('lean/manifests/check_scalar_stationarity_statements.lean'), re.M)
statements = read(packet + 'theorem_statements.txt')
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert new == checks == printed and not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(' + '|'.join(mods) + r')\.(\w+)', statements, re.M))
decls = {m.group(1)+'.'+m.group(2): ' '.join(statements[m.start():starts[i+1].start() if i+1<len(starts) else len(statements)].split()) for i,m in enumerate(starts)}
for name, d in decls.items():
    d = d.replace('SbtCosmo.Derivation.', '')
    for group in ['ConvexSubgradient', 'ExtendedClosurePrice', 'SchurClosurePrice', 'SchurDifferential', 'ScalarStationarityExamples']:
        d = d.replace(group + '.', '')
    decls[name] = d


def require(name, *tokens):
    d = decls[name]
    for token in tokens:
        assert token in d, (name, token)
    return d


require('ScalarPriceStationarity.certificate_real_domain_return', '(hc : DualCertificate A J energy B p star)',
        'ConvexClosurePrice.DualCertificate (finiteDomain A J) (realObjective J)')
require('ScalarPriceStationarity.certificate_price_identification', 'HasDerivAt', '(value A J energy T).toReal', ': p = -d')
require('ScalarPriceStationarity.certificate_price_unique', '{star other : E}', 'B p star', 'B q other', ': p = q')
require('ScalarPriceStationarity.certificate_stationarity', '(hc : DualCertificate', '(hp : 0 < p)',
        'RealSubgradient energy star r', 'q + p • r + η = 0')
for name in ['positive_price_stationarity', 'positive_price_smooth_stationarity']:
    d = require('ScalarPriceStationarity.'+name, '{J : E → EReal}', '{energy : E → ℝ}',
                'FiniteDimensional ℝ E', 'epigraph Set.univ J', 'ConvexOn ℝ Set.univ energy',
                'intrinsicInterior ℝ (finiteDomain Set.univ J)', 'intrinsicInterior ℝ A',
                'PrimalOptimum A J energy B star', '(value A J energy T).toReal', 'HasDerivAt',
                'p = -d', '0 < p', 'energy star = B', 'DualCertificate A J energy B p star',
                'dualValue A J energy B p = value A J energy B',
                'Subgradient J star q', 'NormalCone A star η')
    for forbidden in ['(hc :', '(hdual :', '(hstationarity :', '(hsub :', '(hq :', '(hr :', '(hη :', '(hactive :', '(hslater :']:
        assert forbidden not in d, (name, forbidden)
full = require('ScalarPriceStationarity.positive_price_stationarity',
               'RealSubgradient energy star r', 'q + p • r + η = 0')
assert 'HasFDerivAt' not in full and 'Differentiable' not in full
require('ScalarPriceStationarity.positive_price_smooth_stationarity', '(hk : HasFDerivAt energy k star)', 'q + p • k + η = 0')
require('ScalarSchurStationarity.hasFDerivAt_energy', 'HasFDerivAt', 'schurEnergy W L (D z)', '(pricePullback L D x W) x')
require('ScalarSchurStationarity.scaled_adjoint', 'p • pricePullback L D x W =', 'traceAdjoint', 'fderiv ℝ', 'Support.residual L (D z)', '(p • W)')
d = require('ScalarSchurStationarity.positive_price_stationarity', '(hW : W.PosSemidef)',
            '(D : E →ᵃ[ℝ]', '{J : E → EReal}', 'p = -d', '0 < p', 'schurEnergy W L (D star) = B',
            'Subgradient J star q', 'NormalCone A star η', 'traceAdjoint', 'fderiv ℝ',
            'Support.residual L (D x)', '(p • W)', '∀ (h : E),', '2 * p *', 'D.linear h', 'complement L')
for forbidden in ['HasFDerivAt', 'ConvexOn', '(hc :', '(hstationarity :', '(hsub :', '(hJac :', '(hAdj :']:
    assert forbidden not in d, forbidden
require('ScalarStationarityExamples.constructed_extended_schur_stationarity', 'ExtendedClosurePriceExamples.objective',
        'traceAdjoint', 'fderiv ℝ', 'Support.residual 0', 'SchurClosurePriceExamples.energy 1 1 1', 'dualValue')
require('ScalarStationarityExamples.extended_price_unique', '(hc : DualCertificate', 'p = 1')
require('ScalarStationarityExamples.kink_actual_value', 'value Set.univ kinkObjective kinkEnergy B = ↑(-B)')
require('ScalarStationarityExamples.kink_actual_derivative', 'HasDerivAt', 'value Set.univ kinkObjective kinkEnergy T', '(-1) B')
require('ScalarStationarityExamples.kink_energy_not_differentiable', '¬DifferentiableAt ℝ kinkEnergy (0, 0)')
require('ScalarStationarityExamples.constructed_nonsmooth_energy_stationarity',
        'Subgradient kinkObjective (0, 0) q', 'RealSubgradient kinkEnergy (0, 0) r',
        'NormalCone Set.univ (0, 0) η', 'q + r + η = 0', 'DualCertificate', 'kinkEnergy 0 1 (0, 0)', 'dualValue')
for name in ['extended_relative_interior', 'constructed_extended_schur_stationarity', 'kink_energy_convex',
             'kink_objective_convex', 'kink_actual_value', 'kink_actual_derivative',
             'kink_energy_not_differentiable', 'constructed_nonsmooth_energy_stationarity']:
    assert '(h' not in decls['ScalarStationarityExamples.'+name], name
source = read('lean/SbtCosmo/Derivation/ScalarPriceStationarity.lean')
for token in ['finite_value_domain_return', 'certificate_real_domain_return hbottom hc',
              'ConvexSumSplit.split_extended', 'RelativeSumSplit.split_subgradient',
              'p⁻¹ • k', 'positive_price_certificate', 'certificate_stationarity hbottom', 'smooth_real_subgradient_eq hr hk']:
    assert token in source
source = read('lean/SbtCosmo/Derivation/ScalarSchurStationarity.lean')
for token in ['hasFDerivAt_trace_gap', 'pricePullback_eq_adjoint_fderiv', 'map_smul',
              'ScalarPriceStationarity.positive_price_smooth_stationarity',
              'affine_schur_energy_convex hW L D convex_univ', 'hasFDerivAt_energy W L D star', 'pricePullback_psd hW']:
    assert token in source
source = read('lean/SbtCosmo/Derivation/ScalarStationarityExamples.lean')
for token in ['ExtendedClosurePriceExamples.actual_value_derivative', 'kink_actual_derivative 0',
              'ScalarPriceStationarity.positive_price_stationarity', 'not_differentiableAt_abs_zero', 'h.comp 0 hp']:
    assert token in source
build = read(packet + 'lean_build.txt')
assert 'Build completed successfully (8140 jobs).' in build and not re.search(r'error:|warning:', build)
assert 'Adversarial self-review, not independent review' in read(packet + 'self_review.txt')

# Prior source and evidence stay immutable; only these cumulative metadata may grow.
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
expected_config = old_config.replace('`SbtCosmo.Derivation.SchurDifferentialExamples]',
    '`SbtCosmo.Derivation.SchurDifferentialExamples, ' + ', '.join('`SbtCosmo.Derivation.'+m for m in mods) + ']')
assert read('lean/lakefile.lean') == expected_config

lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=root / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked'] and 'version 4.28.0' in lean_version
assert read('lean/lean-toolchain').strip() == 'leanprover/lean4:v4.28.0'
mathlib = prior['mathlib']
libroot = root / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert digest((libroot / p).read_bytes()) == h
for p in ['Mathlib/Analysis/Calculus/FDeriv/Prod.lean', 'Mathlib/Analysis/Calculus/FDeriv/Add.lean',
          'Mathlib/Analysis/Calculus/FDeriv/Mul.lean', 'Mathlib/Analysis/Calculus/FDeriv/Comp.lean',
          'Mathlib/Analysis/Calculus/FDeriv/Linear.lean', 'Mathlib/Analysis/Calculus/FDeriv/Const.lean',
          'Mathlib/Analysis/Calculus/FDeriv/Affine.lean', 'Mathlib/Analysis/Matrix/Normed.lean',
          'Mathlib/Data/Matrix/Basic.lean', 'Mathlib/LinearAlgebra/Matrix/Trace.lean',
          'Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean',
          'Mathlib/Topology/Algebra/Module/LinearMapPiProd.lean',
          'Mathlib/Analysis/Convex/Function.lean', 'Mathlib/Analysis/Convex/Intrinsic.lean',
          'Mathlib/Analysis/Calculus/Deriv/Abs.lean', 'Mathlib/Analysis/Calculus/LocalExtr/Basic.lean',
          'Mathlib/Data/EReal/Operations.lean']:
    source = (libroot / p).read_bytes()
    assert source == subprocess.check_output(['git', 'show', 'HEAD:' + p], cwd=libroot)
    mathlib['direct_proof_source_sha256'][p] = digest(source)
files = set(prior['source_sha256']) | {prior_path}
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in mods)
files.update(['scripts/de_scalar_stationarity_verify.py', 'math/SCALAR_STATIONARITY_LEAN_2026-10-03.md',
              'lean/manifests/check_scalar_stationarity_statements.lean', 'lean/manifests/check_scalar_stationarity_axioms.lean',
              new_path, combined_path])
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
    'scope': 'Corrected generic scalar Theorem S: one canonical positive price with full nonsmooth stationarity and actual Schur return',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8140, 'warnings_as_errors': True, 'receipt': 'lean_build.txt'},
    'axiom_audit': {'command_fresh_suffix': 'lake env lean -DwarningAsError=true manifests/check_scalar_stationarity_axioms.lean',
                    'success': True, 'declarations_cumulative': 1130, 'declarations_fresh': 19,
                    'declarations_preserved': 1111, 'new_local_theorems': new, 'axioms': sorted(actual),
                    'full_cumulative_command_rerun': False, 'preserved_raw_prefix': old_path,
                    'preserved_prefix_sha256': digest(old_raw.encode()), 'fresh_suffix_receipt': new_path,
                    'combined_receipt': combined_path, 'old_proof_sources_unchanged': True,
                    'ordered_declarations_match_full_manifest': True, 'proof_holes': False, 'native_decide': False},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_scalar_stationarity_statements.lean',
                        'success': True, 'declarations': 19, 'receipt': 'theorem_statements.txt'},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {
        'corrected_LT1_scalar_Theorem_S_same_price_assembly': True,
        'original_target_source': 'math/DERIVATION_LT1_2026-06-02.md sections2.1-2.2',
        'general_energy': 'finite convex ambient extension, may be nonsmooth',
        'objective': 'original ambient no-bottom convex EReal epigraph, including infinite-cost points',
        'qualification': 'actual common ri(dom J)/ri(A) point, no full-dimensional domain assumption',
        'price': 'one constructed p=-actual_V_derivative>0',
        'activity_derived': True, 'original_certificate_and_strong_duality': True,
        'full_stationarity': 'q+p*r+eta=0 with separate ambient J/energy supports and admissibility normal',
        'final_derivative_support_normal_stationarity_dual_premises': False,
        'smooth_specialization': 'actual supplied energy HasFDerivAt identifies its support with derivative',
        'Slater_and_activity_premises_not_required_on_this_route': True,
        'closedness_premises_not_required_given_attainment_and_local_finite_derivative': True,
        'primal_attainment_and_value_derivative_supplied': True,
        'guarded_reverse_extended_domain_return': True,
        'every_certificate_price_identified': True, 'scalar_price_unique_across_optimizers': True,
        'optimizer_or_support_or_matrix_price_uniqueness_claimed': False,
        'actual_Schur_energy_derivative_earned': True, 'native_invertibility_required': False,
        'actual_Schur_matrix_adjoint': 'q+traceAdjoint(fderiv actual_Xi)(p*W)+eta=0',
        'every_primal_direction': 'q(h)+2*p*trace(W D(star) R (D.linear(h))^T)+eta(h)=0',
        'scalar_constraint_not_matrix_budget': True,
        'actual_extended_Schur_example_price_and_dual': 1,
        'nonsmooth_scope_example': 'e(x,y)=x+abs(y), J=-x, actualV=-B, price1, dual0',
        'actual_energy_no_derivative_at_optimizer_proved': True,
        'concrete_construction_output_premises': False,
        'native_L_fixed': True, 'moving_native_calculus_mechanized': False,
        'primal_attainment_derived': False, 'physical_Lambda_bridge': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review',
    'next_construction': 'General matrix-map qualified stationarity versus actual affine Schur instance; remaining original-target audit',
    'goal_complete': False,
    'source_sha256': hashes, 'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_blob_sha256': git_hashes, 'git_crlf_to_lf_normalized_paths': normalized,
}
(root / packet / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print(f'1130 ordered cumulative standard-only closures (1111 immutable + 19 fresh), full same-price nonsmooth scalar and actual Schur stationarity; {len(hashes)} fingerprints')
