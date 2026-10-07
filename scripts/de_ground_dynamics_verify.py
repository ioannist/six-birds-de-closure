"""Actual nonlinear local/global convergence: source, exported statements, exact numerical return and provenance checks."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

import de_ground_interval_certificate as cert

ROOT = cert.ROOT
BASE = 'ac420e8'
PACKET = 'results/ground_dynamics_2026-10-03/'
PRIOR = 'results/ground_interval_2026-10-03/verification.json'
MODS = ['GroundLocalDynamics', 'GroundZeroCouplingOrbit']
PREFIX = 'SbtCosmo.Derivation.'
OLD_AUDIT = 'lean/manifests/axiom_audit_ground_interval_2026-10-03.txt'
NEW_AUDIT = 'lean/manifests/axiom_audit_ground_dynamics_new_2026-10-03.txt'
COMBINED = 'lean/manifests/axiom_audit_ground_dynamics_2026-10-03.txt'
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


prior = json.loads(read(PRIOR))
assert (ROOT/PRIOR).read_bytes() == baseline(PRIOR)
for p, h in prior['source_sha256'].items():
    if p not in MUTABLE:
        assert sha((ROOT/p).read_bytes()) == h and canonical(p) == baseline(p), p
new = []
for mod in MODS:
    source = read('lean/SbtCosmo/Derivation/'+mod+'.lean')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', source)
    new += [PREFIX+mod+'.'+n for n in re.findall(r'^theorem (\w+)', source, re.M)]
assert len(new) == 40
old_manifest = baseline('lean/manifests/check_axioms.lean').decode()
old = re.findall(r'^#print axioms (\S+)', old_manifest, re.M)
assert len(old) == 1655
imports = ''.join('import '+PREFIX+mod+'\n' for mod in MODS)
assert read('lean/manifests/check_axioms.lean') == old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
assert read('lean/lakefile.lean') == baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+mod for mod in MODS)+']\n'
for suffix, cmd in [('axioms', '#print axioms '), ('statements', '#check ')]:
    assert read('lean/manifests/check_ground_dynamics_'+suffix+'.lean') == imports+'\n'+''.join(cmd+n+'\n' for n in new)
assert (ROOT/OLD_AUDIT).read_bytes() == baseline(OLD_AUDIT)
oldraw, newraw = read(OLD_AUDIT), read(NEW_AUDIT)
closures(oldraw, old); closures(newraw, new)
header = ('Cumulative audit: immutable 1655-declaration raw prefix plus freshly audited 40-declaration suffix.\n'
          'Baseline: ac420e8; proof-source/toolchain identity checked by de_ground_dynamics_verify.py.\n'
          'Full 1695-declaration command was not rerun in this packet.\n\n')
combined = header+oldraw+'\n'+newraw
closures(combined, old+new)
(ROOT/COMBINED).write_text(combined)
statements = read(PACKET+'theorem_statements.txt')
assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)', statements, re.M)] == new
assert not re.search(r'error:|warning:', statements)
starts = list(re.finditer(r'^'+re.escape(PREFIX)+r'(\w+)\.(\w+)', statements, re.M))
decls = {}
def flatten(t):
    t = ' '.join(t.replace('(', ' ').replace(')', ' ').split())
    return t.replace('| ', '|').replace(' |', '|')
for i, m in enumerate(starts):
    text = statements[m.start():starts[i+1].start() if i+1 < len(starts) else len(statements)]
    text = re.sub(r'SbtCosmo\.Derivation\.\w+\.', '', text).replace('⇑', '')
    decls[m.group(1)+'.'+m.group(2)] = flatten(text)


def require(name, *tokens):
    for token in tokens:
        assert flatten(token) in decls[name], (name, token, decls[name])


L, Z = [mod+'.' for mod in MODS]
require(L+'c1_fixed_local_attraction', 'hc : ContDiffAt ℝ 1 f u', 'hf : f u = u',
        'hd : ‖fderiv ℝ f u‖ < 1', '∃ r > 0,', 'Tendsto', 'q', 'dist', 'closedBall')
require(L+'normalized_smooth_at', 'hu : normSq u = 1', 'hf : groundMap b κ u = u',
        'ContDiffAt ℝ ↑⊤', 'normalizedRelaxed groundMap b κ m')
require(L+'operator_norm_le_rows', '∑ j, |L column j i|', '‖L‖ ≤ q')
require(L+'coordinate_iterate_return', 'S coordinateMap S b κ m ^[n] x',
        'normalizedRelaxed groundMap b κ m ^[n] S x')
require(L+'actual_local_attraction', 'S : Field ≃L[ℝ] Field', 'hu : normSq u = 1',
        'hf : groundMap b κ u = u', 'hd : ‖coordinateJacobian S b κ m u‖ < 1',
        'S.symm y ∈ Metric.closedBall S.symm u r', 'Tendsto', 'dist', '↑q ^ n')
require(L+'actual_local_attraction_of_rows', 'hq : 0 ≤ q', 'hq1 : q < 1',
        '∑ j, |coordinateJacobian S b κ m u column j i|', 'Tendsto')
require(L+'positive_root_groundPair_return', 'residual b κ x = 0', '0 < x.1 i',
        'groundPair sourcePotential b κ x.1 = x')
require(L+'positive_root_jacobian_return', 'border sourcePotential b κ x.1 x.1 x.2 y',
        'y.1 = jacobian b κ x.1 h')
require(Z+'native_step_unit_positive', 'b : Field', 'κ : ℝ', '0 ≤ u i', 'm ∈ Set.Ioc 0 1',
        'normSq normalizedRelaxed groundMap b κ m u = 1', '0 <')
require(Z+'native_orbit_unit_nonnegative', 'b : Field', 'κ : ℝ', 'n : ℕ', '^[n]', 'normSq', '0 ≤')
require(Z+'actual_zero_coupling_global_convergence', 'b : Field', 'hu : normSq u = 1',
        'hup : ∀ i : Fin 8 , 0 ≤ u i', 'hm : m ∈ Set.Ioc 0 1',
        'Tendsto', 'normalizedRelaxed groundMap b 0 m ^[n] u', 'nhds positiveGround b')
require(Z+'actual_zero_coupling_distance_bound', 'n : ℕ', '‖', 'positiveGround b',
        '≤ √ 2 * 1 - m ^ n * gap positiveGround b u')

build = read(PACKET+'lean_build.txt')
assert 'Build completed successfully (8190 jobs).' in build
assert not re.search(r'error:|warning:|Build failed', build)
version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT/'lean').decode().strip()
assert version == prior['actual_lean_version_checked']
mathlib = prior['mathlib']
libroot = ROOT/'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert sha((libroot/p).read_bytes()) == h
for p in ['Mathlib/Analysis/Calculus/ContDiff/RCLike.lean',
          'Mathlib/Analysis/Normed/Operator/Basic.lean',
          'Mathlib/Analysis/Normed/Group/Constructions.lean', 'Mathlib/Algebra/BigOperators/Pi.lean',
          'Mathlib/Analysis/SpecificLimits/Basic.lean']:
    b = (libroot/p).read_bytes()
    assert b == subprocess.check_output(['git', 'show', 'HEAD:'+p], cwd=libroot)
    mathlib['direct_proof_source_sha256'][p] = sha(b)

# Read-only exact replay: no original receipt or witness is overwritten.
data = json.loads(read('results/ground_interval_2026-10-03/witnesses.json'))
result = cert.replay(data)
assert result == json.loads(read('results/ground_interval_2026-10-03/certificates.json'))
stable = [r for r in result['certificates'] if r['verdict'].startswith('all_real')]
assert len(stable) == 28
assert all(int(r['spectral_radius_upper']) < cert.SCALE for r in stable)
landing = dict(fresh_read_only_exact_replay=True, original_sample_roots=30,
               exact_induced_norm_bounds_below_one=28,
               positive_real_local_convergence_mathematical_return=True,
               analytic_local_convergence_criterion_lean_checked=True,
               concrete_root_basis_and_norm_bounds_lean_instantiated=False,
               explicit_numerical_basin_radius_or_budget_bound=False,
               continuous_branch_between_samples=False, original_complex_initialization=False,
               stable_samples=[dict(sweep=r['sweep'], parameter_hex=r['parameter_hex'],
                                    actual_transformed_derivative_norm_upper=r['spectral_radius_upper']) for r in stable])
(ROOT/PACKET/'original_sample_local_return.json').write_text(json.dumps(landing, indent=2)+'\n')
files = set(prior['source_sha256']) | {PRIOR, NEW_AUDIT, COMBINED,
    'lean/manifests/check_ground_dynamics_axioms.lean', 'lean/manifests/check_ground_dynamics_statements.lean',
    'math/GROUND_NONLINEAR_DYNAMICS_2026-10-03.md', 'scripts/de_ground_dynamics_verify.py'}
files.update('lean/SbtCosmo/Derivation/'+mod+'.lean' for mod in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.name != 'verification.json')
assert len(files) == 545, len(files)
v = dict(baseline_commit=BASE,
         scope='Actual all-direction real nonlinear local attraction; unconditional global zero-coupling positive-real convergence for all backgrounds',
         axiom_audit=dict(declarations_cumulative=1695, declarations_preserved=1655,
                         declarations_fresh=40, new_local_theorems=new,
                         axioms=['Classical.choice', 'Quot.sound', 'propext'],
                         full_cumulative_command_rerun=False, preserved_raw_prefix=OLD_AUDIT,
                         preserved_prefix_sha256=sha(oldraw.encode()), fresh_suffix_receipt=NEW_AUDIT,
                         combined_receipt=COMBINED, success=True),
         lean_build=dict(command='lake build', jobs=8190, success=True, warnings_as_errors=True,
                         receipt_trailing_whitespace_normalized=True, diagnostic_content_removed=False),
         statement_check=dict(declarations=40, success=True), mathlib=mathlib,
         actual_lean_version_checked=version,
         original_return=dict(actual_ground_source_and_normalized_iteration=True,
                              local_all_directions_in_real_slice=True,
                              actual_C_infinity_normalization_and_coordinate_conjugacy_earned=True,
                              local_derivative_or_row_sum_bound_explicit=True,
                              exact_sample_local_convergence_foundation='Lean analytic criterion plus exact Python root/basis/induced-norm certificates; concrete kernel instantiations incomplete',
                              original_zero_coupling_global_convergence_all_backgrounds=True,
                              zero_coupling_initial_guard='nonnegative real unit field',
                              zero_coupling_mixing_guard='0 < m <= 1',
                              actual_zero_coupling_distance_rate_earned=True,
                              all_coupling_positive_unit_invariant=True,
                              unstable_nonlinear_escape=False, frozen_complex_orbit=False,
                              continuous_nonlinear_branch_or_sampled_crossing=False,
                              physical_Lambda_bridge=False),
         python_test_suite_rerun=False, original_runtime_edited=False, paper_edited=False,
         review='adversarial self-review, not independent review', goal_complete=False,
         next_construction='Concrete kernel root/basis/norm certificates; native complex phase/local return; continuous original nonlinear branch/crossing if needed',
         source_sha256={p: sha((ROOT/p).read_bytes()) for p in sorted(files)},
         git_blob_sha256={p: sha(canonical(p)) for p in sorted(files)})
(ROOT/PACKET/'verification.json').write_text(json.dumps(v, indent=2)+'\n')
print('1695 cumulative standard-only closures; actual nonlinear local/global zero-coupling return; 545 fingerprints')
