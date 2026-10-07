"""Verify actual nonconstant ground-selector/source/normalized Jacobians and cumulative provenance."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = '0dc7f85'
PACKET = 'results/ground_jacobian_2026-10-03/'
MODS = ['GroundBorder', 'GroundEquations', 'GroundSmooth', 'GroundSourceJacobian', 'GroundNormalizedJacobian']
PREFIX = 'SbtCosmo.Derivation.'
PRIOR_PATH = 'results/ground_alternating_2026-10-03/verification.json'
OLD_AUDIT = 'lean/manifests/axiom_audit_ground_alternating_2026-10-03.txt'
NEW_AUDIT = 'lean/manifests/axiom_audit_ground_jacobian_new_2026-10-03.txt'
COMBINED = 'lean/manifests/axiom_audit_ground_jacobian_2026-10-03.txt'
MUTABLE = {'README.md', 'lean/README.md', 'lean/lakefile.lean',
           'lean/manifests/check_axioms.lean', 'lean/manifests/coverage_table.md',
           'math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}


def read(path):
    return (ROOT / path).read_text()


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def git_blob(ref, path):
    return subprocess.check_output(['git', 'show', ref + ':' + path], cwd=ROOT)


def canonical(path):
    blob = (ROOT / path).read_bytes()
    if b'\r\n' in blob:
        attrs = subprocess.check_output(['git', 'check-attr', 'text', 'eol', '--', path], cwd=ROOT).decode()
        assert 'text: auto' in attrs and 'eol: lf' in attrs and b'\0' not in blob, path
        blob = blob.replace(b'\r\n', b'\n')
    return blob


def closures(raw, names):
    entries = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", raw)
    assert [name for name, _ in entries] == names
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
for mod in MODS:
    src = read('lean/SbtCosmo/Derivation/' + mod + '.lean')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', src)
    new += [PREFIX + mod + '.' + n for n in re.findall(r'^theorem (\w+)', src, re.M)]
assert len(new) == 51
assert (ROOT / PRIOR_PATH).read_bytes() == git_blob(BASE, PRIOR_PATH)
prior = json.loads(read(PRIOR_PATH))
for path, digest in prior['source_sha256'].items():
    if path not in MUTABLE:
        assert sha((ROOT / path).read_bytes()) == digest, path
        assert canonical(path) == git_blob(BASE, path), path
old_manifest = git_blob(BASE, 'lean/manifests/check_axioms.lean').decode()
old_names = re.findall(r'^#print axioms (\S+)', old_manifest, re.M)
assert len(old_names) == 1593
imports = ''.join('import ' + PREFIX + mod + '\n' for mod in MODS)
assert read('lean/manifests/check_axioms.lean') == old_manifest + '\n' + imports + '\n' + ''.join('#print axioms ' + n + '\n' for n in new)
old_roots = git_blob(BASE, 'lean/lakefile.lean').decode()
assert read('lean/lakefile.lean') == old_roots[:-2] + ',\n    ' + ', '.join('`' + PREFIX + m for m in MODS) + ']\n'
for filename, command in [('check_ground_jacobian_axioms.lean', '#print axioms '),
                          ('check_ground_jacobian_statements.lean', '#check ')]:
    assert read('lean/manifests/' + filename) == imports + '\n' + ''.join(command + n + '\n' for n in new)
assert (ROOT / OLD_AUDIT).read_bytes() == git_blob(BASE, OLD_AUDIT)
old_raw, new_raw = read(OLD_AUDIT), read(NEW_AUDIT)
closures(old_raw, old_names)
actual = closures(new_raw, new)
header = ('Cumulative audit: exact immutable earlier 1593-declaration raw prefix plus freshly audited 51-declaration suffix.\n'
          'Baseline: 0dc7f85; earlier proof-source/toolchain identity checked by de_ground_jacobian_verify.py.\n'
          'Full 1644-declaration command was not rerun in this packet.\n\n')
combined = header + old_raw + '\n' + new_raw
closures(combined, old_names + new)
(ROOT / COMBINED).write_text(combined)

statements = read(PACKET + 'theorem_statements.txt')
assert not re.search(r'error:|warning:', statements)
printed = [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)]
assert printed == new
starts = list(re.finditer(r'^SbtCosmo\.Derivation\.(' + '|'.join(MODS) + r')\.(\w+)', statements, re.M))
decls = {}
for i, m in enumerate(starts):
    text = ' '.join(statements[m.start():starts[i + 1].start() if i + 1 < len(starts) else len(statements)].split())
    text = text.replace(PREFIX, '').replace('⇑', '')
    for mod in MODS + ['GroundState']:
        text = text.replace(mod + '.', '')
    decls[m.group(1) + '.' + m.group(2)] = text


def require(name, *tokens):
    declaration = decls[name]
    def flatten(text):
        return ' '.join(text.replace('(', ' ').replace(')', ' ').split())
    for token in tokens:
        assert flatten(token) in flatten(declaration), (name, token, declaration)


B, E, S, J, N = [m + '.' for m in MODS]
# Lean pretty printing elides the proof argument of implicitFunction as a placeholder.
assert '(actual_implicit_data v).implicitFunction' in read('lean/SbtCosmo/Derivation/GroundSmooth.lean')
require(B + 'border_bijective', '(hg : IsGround v u e)', 'Function.Bijective', 'border v u e')
require(E + 'equations_hasFDerivAt', '(p : Domain)', 'HasFDerivAt equations (derivative p) p')
require(E + 'actual_implicit_data', '(v : Field)', 'IsContDiffImplicitAt ↑⊤', 'equations', '(v, groundPair v)')
require(S + 'actual_selector_local_return', '(v : Field)', 'groundPair =ᶠ[nhds v]', '⋯.implicitFunction')
require(S + 'groundPair_smooth', 'ContDiff ℝ ↑⊤', 'groundPair')
require(S + 'positiveGround_smooth', 'ContDiff ℝ ↑⊤', 'positiveGround')
require(S + 'groundEnergy_smooth', 'ContDiff ℝ ↑⊤', 'energy v (positiveGround v)')
require(S + 'actual_pair_fderiv', '(v : Field)', 'fderiv ℝ groundPair v = pairDerivative v')
require(S + 'pairDerivative_unique', '(v h : Field)', 'border v (groundPair v).1 (groundPair v).2 y =', '-h i * positiveGround v i', 'y = pairDerivative v h')
require(S + 'positiveGround_hasFDerivAt', '(v : Field)', 'HasFDerivAt positiveGround (selectorDerivative v) v')
require(S + 'selector_derivative_tangent', '(v h : Field)', 'dot (positiveGround v) (selectorDerivative v h) = 0')
require(J + 'sourceDerivative_apply', '(b : Field) (κ : ℝ) (u h : Field) (i : Fin 8)',
        '2 * κ * (gradient u i * gradient h i + b i * u i * h i)')
require(J + 'sourcePotential_hasFDerivAt', '(b : Field) (κ : ℝ) (u : Field)',
        'HasFDerivAt (sourcePotential b κ) (sourceDerivative b κ u) u')
require(J + 'groundMap_smooth', '(b : Field) (κ : ℝ)', 'ContDiff ℝ ↑⊤', 'groundMap b κ')
require(J + 'groundMap_hasFDerivAt', '(b : Field) (κ : ℝ) (u : Field)', 'HasFDerivAt (groundMap b κ) (jacobian b κ u) u')
require(J + 'jacobian_tangent', '(b : Field) (κ : ℝ) (u h : Field)', 'dot (groundMap b κ u) (jacobian b κ u h) = 0')
require(N + 'normalize_hasFDerivAt', '(hu : normSq u = 1)', 'HasFDerivAt normalize (projection u) u')
require(N + 'normalized_hasFDerivAt', '(hu : normSq u = 1)', '(hf : groundMap b κ u = u)',
        'HasFDerivAt (normalizedRelaxed (groundMap b κ) m) (normalizedJacobian b κ m u) u')
require(N + 'normalized_tangent_return', '(hf : groundMap b κ u = u)', '(ht : dot u h = 0)',
        'normalizedJacobian b κ m u h = (1 - m) • h + m • jacobian b κ u h')
require(N + 'exists_actual_normalized_jacobian', '(b : Field) (κ m : ℝ)', '∃ u,', '∀ (i : Fin 8), 0 < u i',
        'normSq u = 1', 'groundMap b κ u = u', 'HasFDerivAt (normalizedRelaxed (groundMap b κ) m)')
require(N + 'actual_real_eigenmode_return', '(hf : groundMap b κ u = u)', '(ht : dot u h = 0)',
        '(he : jacobian b κ u h = t • h)', 'normalizedJacobian b κ m u h = (1 - m + m * t) • h')
require(N + 'zero_coupling_groundMap', '(b u : Field)', 'groundMap b 0 u = positiveGround b')
require(N + 'zero_coupling_jacobian', '(b u : Field)', 'jacobian b 0 u = 0')
require(N + 'zero_coupling_tangent_return', '(ht : dot (positiveGround b) h = 0)',
        'normalizedJacobian b 0 m (positiveGround b) h = (1 - m) • h')

build = read(PACKET + 'lean_build.txt')
assert 'Build completed successfully (8187 jobs).' in build
assert not re.search(r'error:|warning:|Build failed', build)
lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked']
mathlib = prior['mathlib']
libroot = ROOT / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for path, digest in mathlib['direct_proof_source_sha256'].items():
    assert sha((libroot / path).read_bytes()) == digest, path
for path in ['Mathlib/Analysis/Calculus/ImplicitContDiff.lean', 'Mathlib/Analysis/Calculus/Implicit.lean',
             'Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean',
             'Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean',
             'Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean', 'Mathlib/Analysis/Normed/Operator/Banach.lean',
             'Mathlib/Analysis/Calculus/FDeriv/Prod.lean', 'Mathlib/Analysis/Calculus/FDeriv/Mul.lean',
             'Mathlib/Analysis/Calculus/FDeriv/Add.lean', 'Mathlib/Analysis/Calculus/FDeriv/Pow.lean',
             'Mathlib/Analysis/Calculus/Deriv/Inv.lean', 'Mathlib/Analysis/SpecialFunctions/Sqrt.lean']:
    blob = (libroot / path).read_bytes()
    assert blob == subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=libroot)
    mathlib['direct_proof_source_sha256'][path] = sha(blob)
source = 'external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py'
assert sha((ROOT / source).read_bytes()) == '391907fae6fdee8c4e4de1c12ee67d72fdfea4928cad1f148cc30e31584898fd'
extra_protected = [source, 'paper/sections/sec_06_value.tex', 'scripts/de_ground_state_checks.py']
for path in extra_protected:
    assert canonical(path) == git_blob(BASE, path), path
files = set(prior['source_sha256']) | {PRIOR_PATH, NEW_AUDIT, COMBINED,
    'scripts/de_ground_jacobian_verify.py', 'math/GROUND_JACOBIAN_LEAN_2026-10-03.md',
    'lean/manifests/check_ground_jacobian_axioms.lean', 'lean/manifests/check_ground_jacobian_statements.lean'}
files.update(extra_protected)
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT / PACKET).iterdir() if p.name != 'verification.json')
hashes = {path: sha((ROOT / path).read_bytes()) for path in sorted(files)}
git_hashes = {path: sha(canonical(path)) for path in sorted(files)}
assert len(hashes) == 517
v = {
    'baseline_commit': BASE,
    'scope': 'Actual positive-ground smoothness and real Step26 source/normalized Jacobians for arbitrary nonconstant backgrounds',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8187, 'warnings_as_errors': True,
        'receipt_trailing_whitespace_normalized': True, 'diagnostic_content_removed': False},
    'axiom_audit': {'declarations_cumulative': 1644, 'declarations_preserved': 1593, 'declarations_fresh': 51,
        'new_local_theorems': new, 'axioms': sorted(actual), 'full_cumulative_command_rerun': False,
        'preserved_raw_prefix': OLD_AUDIT, 'preserved_prefix_sha256': sha(old_raw.encode()),
        'fresh_suffix_receipt': NEW_AUDIT, 'combined_receipt': COMBINED,
        'old_proof_sources_unchanged': True, 'ordered_declarations_match_full_manifest': True,
        'proof_holes': False, 'native_decide': False, 'success': True},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_ground_jacobian_statements.lean',
                        'declarations': 51, 'success': True},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {'actual_original_cycle_Hamiltonian_sourcing_and_normalized_mixing': True,
        'arbitrary_nonconstant_real_potentials_and_backgrounds': True,
        'normalized_eigen_border_inverse_earned_from_actual_ground_simplicity': True,
        'full_polynomial_equations_and_partial_derivative_earned': True,
        'implicit_branch_return_to_existing_continuous_positive_selector': True,
        'actual_ground_selector_and_energy_C_infinity': True,
        'uniform_global_gap_excited_simplicity_or_analyticity_claimed': False,
        'supplied_selector_derivative_inverse_Jacobian_or_gap': False,
        'selector_derivative_construction': 'inverse earned border applied to (-diag(g)*h,0), first component',
        'actual_source_derivative': '2*k*((G*u)[i]*(G*h)[i]+b[i]*u[i]*h[i])',
        'actual_positive_representative_real_ground_map_Jacobian': True,
        'actual_normalization_derivative': 'P_u h=h-u*(sum_i u[i]*h[i]) at normSq u=1',
        'actual_normalized_fixed_point_derivative': 'P_u*((1-m)*I+m*J)',
        'actual_tangent_derivative_return': '(1-m)*h+m*J*h',
        'all_background_all_coupling_positive_fixed_point_and_normalized_derivative_existence': True,
        'actual_real_eigenmode_damping_return': '1-m+m*t, with explicit actual eigenmode and tangent hypotheses',
        'zero_coupling_control': 'actual constant groundMap, zero J, normalized tangent multiplier1-m',
        'unique_nonlinear_self_consistent_branch_or_smooth_nonlinear_continuation_claimed': False,
        'positive_real_branch_native_interpretation_only': True,
        'arbitrary_signed_complex_phase_rule_or_frozen_complex_initialization_return': False,
        'historical_floating_solver_error_or_sampled_spectral_crossing_certified': False,
        'all_mode_stability_convergence_or_runaway_verdict': False,
        'background_blindness_existential_coupling_boundary_or_physical_Lambda_bridge': False,
        'new_downgrade_of_previously_supported_claim': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review', 'goal_complete': False,
    'next_construction': 'Earn exact numerical branch/error and spectral certificates for the original nonconstant template; actual derivatives now derived; false universal main claims stay parked',
    'source_sha256': hashes, 'git_blob_sha256': git_hashes,
    'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_crlf_to_lf_normalized_paths': [p for p in sorted(files) if (ROOT / p).read_bytes() != canonical(p)],
}
(ROOT / PACKET / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print('1644 ordered cumulative standard-only closures (1593 immutable + 51 fresh); actual nonconstant-selector/source/normalization Jacobians; 517 fingerprints')
