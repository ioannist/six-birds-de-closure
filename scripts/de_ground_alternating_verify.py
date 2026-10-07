"""Verify earned actual Step26 alternating-sector dynamics and cumulative provenance."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = '0912889'
PACKET = 'results/ground_alternating_2026-10-03/'
MODS = ['GroundAlternating', 'GroundAlternatingRelaxation', 'GroundAlternatingOrbit']
PREFIX = 'SbtCosmo.Derivation.'
PRIOR_PATH = 'results/allocation_sample_2026-10-03/verification.json'
OLD_AUDIT = 'lean/manifests/axiom_audit_allocation_sample_2026-10-03.txt'
NEW_AUDIT = 'lean/manifests/axiom_audit_ground_alternating_new_2026-10-03.txt'
COMBINED = 'lean/manifests/axiom_audit_ground_alternating_2026-10-03.txt'
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
assert len(new) == 65
assert (ROOT / PRIOR_PATH).read_bytes() == git_blob(BASE, PRIOR_PATH)
prior = json.loads(read(PRIOR_PATH))
for path, digest in prior['source_sha256'].items():
    if path not in MUTABLE:
        assert sha((ROOT / path).read_bytes()) == digest, path
        assert canonical(path) == git_blob(BASE, path), path
old_manifest = git_blob(BASE, 'lean/manifests/check_axioms.lean').decode()
old_names = re.findall(r'^#print axioms (\S+)', old_manifest, re.M)
assert len(old_names) == 1528
imports = ''.join('import ' + PREFIX + mod + '\n' for mod in MODS)
assert read('lean/manifests/check_axioms.lean') == old_manifest + '\n' + imports + '\n' + ''.join('#print axioms ' + n + '\n' for n in new)
old_roots = git_blob(BASE, 'lean/lakefile.lean').decode()
assert read('lean/lakefile.lean') == old_roots[:-2] + ',\n    ' + ', '.join('`' + PREFIX + m for m in MODS) + ']\n'
for filename, command in [('check_ground_alternating_axioms.lean', '#print axioms '),
                          ('check_ground_alternating_statements.lean', '#check ')]:
    assert read('lean/manifests/' + filename) == imports + '\n' + ''.join(command + n + '\n' for n in new)
assert (ROOT / OLD_AUDIT).read_bytes() == git_blob(BASE, OLD_AUDIT)
old_raw, new_raw = read(OLD_AUDIT), read(NEW_AUDIT)
closures(old_raw, old_names)
actual = closures(new_raw, new)
header = ('Cumulative audit: exact immutable earlier 1528-declaration raw prefix plus freshly audited 65-declaration suffix.\n'
          'Baseline: 0912889; earlier proof-source/toolchain identity checked by de_ground_alternating_verify.py.\n'
          'Full 1593-declaration command was not rerun in this packet.\n\n')
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
    for token in tokens:
        assert token in declaration, (name, token, declaration)


G, R, O = [m + '.' for m in MODS]
require(G + 'ground_eigen', '(c d : ℝ) (i : Fin 8)', 'hamiltonian (pair (c + d) (c - d))', '(1 + c - radius d)')
require(G + 'ground_selected', '(c d : ℝ)', 'positiveGround (pair (c + d) (c - d)) = ground d')
require(G + 'state_source', '(hp : p ∈ Set.Ioo (-1) 1) (b κ : ℝ)', 'sourcePotential (fun x => b) κ (state p)', 'κ * b * p / 8')
require(G + 'selected_state_return', '(hp : p ∈ Set.Ioo (-1) 1)', 'selectedMap b κ (state p) = state (response b κ p)')
require(G + 'response_derivative', '(b κ : ℝ)', 'HasDerivAt (response b κ) (-κ * b / 8) 0')
require(R + 'mixed_norm_positive', '(hm : m ∈ Set.Icc 0 1)', '0 < normSq (relaxed (selectedMap b κ) m (state p))')
require(R + 'normalized_state_return', '(hp : p ∈ Set.Ioo (-1) 1)', '(hm : m ∈ Set.Icc 0 1)',
        'normalizedRelaxed (selectedMap b κ) m (state p) = state (mixedResponse b κ m p)')
require(R + 'actual_response_derivative', '(b κ m : ℝ)', 'HasDerivAt (fun p => contrast (normalizedRelaxed (selectedMap b κ) m (state p))) (mode b κ m) 0')
require(R + 'half_mode_stable_iff', '(b κ : ℝ)', '|mode b κ (1 / 2)| < 1 ↔ -8 < κ * b ∧ κ * b < 24')
require(R + 'local_gain_lower', '(hf : HasDerivAt f d 0)', '(h0 : f 0 = 0)', '(hr : r < |d|)', '0 < |p| → |p| < ε → r * |p| < |f p|')
require(O + 'scalar_orbit_live', '(hm : m ∈ Set.Icc 0 1)', '(n : ℕ)', '(mixedResponse b κ m)^[n] p ∈ Set.Ioo (-1) 1')
require(O + 'iterate_state_return', '(hm : m ∈ Set.Icc 0 1)', '(n : ℕ)', '(normalizedRelaxed (selectedMap b κ) m)^[n] (state p) = state ((mixedResponse b κ m)^[n] p)')
require(O + 'contraction_orbit_bound', '(n : ℕ)', '|f^[n] p| ≤ r ^ n * |p| ∧ |f^[n] p| < ε')
require(O + 'actual_local_attraction', '(hm : m ∈ Set.Icc 0 1)', '(hmode : |mode b κ m| < 1)',
        '∃ ε > 0, ε ≤ 1 ∧ ∀ (p : ℝ)', 'Filter.Tendsto', '(normalizedRelaxed (selectedMap b κ) m)^[n]', 'Filter.atTop (nhds uniform)')
require(O + 'actual_local_escape', '(hm : m ∈ Set.Icc 0 1)', '(hmode : 1 < |mode b κ m|)',
        '∃ ε > 0, ε ≤ 1 ∧ ∀ (p : ℝ), 0 < |p| → |p| < ε → ∃ n', 'ε ≤ |contrast', '(normalizedRelaxed (selectedMap b κ) m)^[n]')
require(O + 'half_local_attraction', '(h : -8 < κ * b ∧ κ * b < 24)', 'Filter.Tendsto', 'Filter.atTop (nhds uniform)')
require(O + 'half_local_escape', '(h : κ * b < -8 ∨ 24 < κ * b)', '0 < |p| → |p| < ε → ∃ n', 'ε ≤ |contrast')
for name, parameters in [('coupling_escape_control', 'selectedMap 1 30'),
                         ('background_escape_control', 'selectedMap 100 (3 / 10)')]:
    require(O + name, '∃ ε > 0, ε ≤ 1 ∧ ∀ (p : ℝ), 0 < |p| → |p| < ε → ∃ n', parameters, '(1 / 2))^[n]')

build = read(PACKET + 'lean_build.txt')
assert 'Build completed successfully (8182 jobs).' in build
assert not re.search(r'error:|warning:|Build failed', build)
lean_version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT / 'lean').decode().strip()
assert lean_version == prior['actual_lean_version_checked']
mathlib = prior['mathlib']
libroot = ROOT / 'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for path, digest in mathlib['direct_proof_source_sha256'].items():
    assert sha((libroot / path).read_bytes()) == digest, path
for path in ['Mathlib/Analysis/Calculus/Deriv/Slope.lean', 'Mathlib/LinearAlgebra/AffineSpace/Slope.lean',
             'Mathlib/Analysis/SpecificLimits/Basic.lean', 'Mathlib/Topology/NhdsWithin.lean',
             'Mathlib/Topology/MetricSpace/Pseudo/Defs.lean', 'Mathlib/Logic/Function/Iterate.lean',
             'Mathlib/Analysis/Calculus/Deriv/Add.lean', 'Mathlib/Analysis/Calculus/Deriv/Mul.lean',
             'Mathlib/Analysis/Calculus/Deriv/Pow.lean']:
    blob = (libroot / path).read_bytes()
    assert blob == subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=libroot)
    mathlib['direct_proof_source_sha256'][path] = sha(blob)
source = 'external/step54_repro/six-birds-sm-qm-gr/physics_atlas/thread_qm_gr/steps/step26_semiclassical_dynamics_artifacts/semiclassical_dynamics_step26.py'
assert sha((ROOT / source).read_bytes()) == '391907fae6fdee8c4e4de1c12ee67d72fdfea4928cad1f148cc30e31584898fd'
extra_protected = [source, 'paper/sections/sec_06_value.tex', 'scripts/de_ground_state_checks.py']
for path in extra_protected:
    assert canonical(path) == git_blob(BASE, path), path
files = set(prior['source_sha256']) | {PRIOR_PATH, NEW_AUDIT, COMBINED,
    'scripts/de_ground_alternating_verify.py', 'math/GROUND_ALTERNATING_LEAN_2026-10-03.md',
    'lean/manifests/check_ground_alternating_axioms.lean', 'lean/manifests/check_ground_alternating_statements.lean'}
files.update(extra_protected)
files.update('lean/SbtCosmo/Derivation/' + m + '.lean' for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT / PACKET).iterdir() if p.name != 'verification.json')
hashes = {path: sha((ROOT / path).read_bytes()) for path in sorted(files)}
git_hashes = {path: sha(canonical(path)) for path in sorted(files)}
assert len(hashes) == 502
v = {
    'baseline_commit': BASE,
    'scope': 'Actual unchanged eight-site Step26 ground map: positive alternating sector under constant background',
    'lean_build': {'command': 'lake build', 'success': True, 'jobs': 8182, 'warnings_as_errors': True,
        'receipt_trailing_whitespace_normalized': True, 'diagnostic_content_removed': False},
    'axiom_audit': {'declarations_cumulative': 1593, 'declarations_preserved': 1528, 'declarations_fresh': 65,
        'new_local_theorems': new, 'axioms': sorted(actual), 'full_cumulative_command_rerun': False,
        'preserved_raw_prefix': OLD_AUDIT, 'preserved_prefix_sha256': sha(old_raw.encode()),
        'fresh_suffix_receipt': NEW_AUDIT, 'combined_receipt': COMBINED,
        'old_proof_sources_unchanged': True, 'ordered_declarations_match_full_manifest': True,
        'proof_holes': False, 'native_decide': False, 'success': True},
    'statement_check': {'command': 'lake env lean -DwarningAsError=true manifests/check_ground_alternating_statements.lean',
                        'declarations': 65, 'success': True},
    'mathlib': mathlib, 'actual_lean_version_checked': lean_version,
    'original_return': {'actual_cycle_Hamiltonian_sourcing_ground_selection_and_normalized_mixing': True,
        'supplied_ground_derivative_mode_Jacobian_or_solution': False,
        'earned_selected_response': '-(k*b*p/8)/sqrt(1+(k*b*p/8)^2)',
        'earned_actual_normalized_response_derivative': '1-m-m*k*b/8',
        'invariant_sector': 'strictly positive alternating normalized Fin8 fields; -1<p<1',
        'convex_mixing_nonzero_normalization_earned': True,
        'all_actual_finite_iteration_field_and_contrast_returns': True,
        'half_mixing_local_slice_attraction': '-8<k*b<24; actual fields converge to uniform',
        'half_mixing_local_finite_escape': 'k*b<-8 or k*b>24; fixed contrast neighborhood independent of starting p',
        'concrete_coupling_control': {'b': 1, 'k': 30, 'm': '1/2', 'actual_finite_escape': True},
        'concrete_background_control': {'b': 100, 'k': '3/10', 'm': '1/2', 'actual_finite_escape': True},
        'background100_inside_original_offset_sweep_claimed': False,
        'all_spatial_mode_stability_claimed': False,
        'boundary_kb_minus8_or24_nonlinear_verdict': False,
        'unbounded_growth_or_nonexistence_inferred': False,
        'original_nonconstant_template_or_frozen_complex_initialization_crossing_certified': False,
        'complex_phase_bug_correction_attributed_to_frozen_run': False,
        'floating_solver_error_or_spectral_crossing_certified': False,
        'background_blindness_existential_coupling_boundary_or_physical_Lambda_bridge': False,
        'new_downgrade_of_previously_supported_claim': False},
    'paper_edited': False, 'frozen_external_edited': False, 'original_python_runtime_edited': False,
    'previous_proof_modules_unchanged': True, 'previous_certificate_artifacts_unchanged': True,
    'python_test_suite_rerun': False, 'original_carrier_solver_rerun': False,
    'review': 'adversarial self-review, not independent review', 'goal_complete': False,
    'next_construction': 'Remaining original-target obligations: earned nonconstant-selector derivative and certified branch/spectral crossing; false universal main claims stay parked',
    'source_sha256': hashes, 'git_blob_sha256': git_hashes,
    'source_byte_representation': 'checkout bytes; historical CRLF preserved',
    'git_crlf_to_lf_normalized_paths': [p for p in sorted(files) if (ROOT / p).read_bytes() != canonical(p)],
}
(ROOT / PACKET / 'verification.json').write_text(json.dumps(v, indent=2) + '\n')
print('1593 ordered cumulative standard-only closures (1528 immutable + 65 fresh); actual alternating-slice iteration; 502 fingerprints')
