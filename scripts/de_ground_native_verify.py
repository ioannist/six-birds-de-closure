"""Original complex phase/local-convergence packet: statement, trust and provenance gates."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

import de_ground_native_certificate as native

ROOT = native.ROOT
BASE = 'df001e0'
PACKET = 'results/ground_native_2026-10-03/'
PRIOR = 'results/ground_dynamics_2026-10-03/verification.json'
MODS = ['GroundNativePhase', 'GroundNativeDerivative', 'GroundNativeIteration',
        'GroundNativeJacobian', 'GroundNativeLocal', 'GroundNativeControls']
PREFIX = 'SbtCosmo.Derivation.'
OLD_AUDIT = 'lean/manifests/axiom_audit_ground_dynamics_2026-10-03.txt'
NEW_AUDIT = 'lean/manifests/axiom_audit_ground_native_new_2026-10-03.txt'
COMBINED = 'lean/manifests/axiom_audit_ground_native_2026-10-03.txt'
MUTABLE = {'README.md', 'lean/README.md', 'lean/lakefile.lean',
           'lean/manifests/check_axioms.lean', 'lean/manifests/coverage_table.md',
           'math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}


def read(p):
    return (ROOT/p).read_text()


def sha(b):
    return hashlib.sha256(b).hexdigest()


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
    for n, a in entries:
        assert {x.strip() for x in a.split(',') if x.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, n


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
assert len(new) == 87
old_manifest = baseline('lean/manifests/check_axioms.lean').decode()
old = re.findall(r'^#print axioms (\S+)', old_manifest, re.M)
assert len(old) == 1695
imports = ''.join('import '+PREFIX+mod+'\n' for mod in MODS)
assert read('lean/manifests/check_axioms.lean') == old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
assert read('lean/lakefile.lean') == baseline('lean/lakefile.lean').decode()[:-2]+',\n    '+', '.join('`'+PREFIX+mod for mod in MODS)+']\n'
for suffix, cmd in [('axioms', '#print axioms '), ('statements', '#check ')]:
    assert read('lean/manifests/check_ground_native_'+suffix+'.lean') == imports+'\n'+''.join(cmd+n+'\n' for n in new)
assert (ROOT/OLD_AUDIT).read_bytes() == baseline(OLD_AUDIT)
oldraw, newraw = read(OLD_AUDIT), read(NEW_AUDIT)
closures(oldraw, old); closures(newraw, new)
header = ('Cumulative audit: immutable 1695-declaration raw prefix plus freshly audited 87-declaration suffix.\n'
          'Baseline: df001e0; proof-source/toolchain identity checked by de_ground_native_verify.py.\n'
          'Full 1782-declaration command was not rerun in this packet.\n\n')
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
    t = statements[m.start():starts[i+1].start() if i+1 < len(starts) else len(statements)]
    t = re.sub(r'SbtCosmo\.Derivation\.\w+\.', '', t).replace('⇑', '')
    decls[m.group(1)+'.'+m.group(2)] = flatten(t)


def require(name, *tokens):
    for token in tokens:
        assert flatten(token) in decls[name], (name, token, decls[name])


P, D, I, J, L, C = [m+'.' for m in MODS]
require(P+'source_pack', 'complexSourcePotential b κ pack x = pairSource b κ x')
require(P+'native_factor', 'hz : z ≠ 0', 'Complex.exp', '-z.arg', 'star z /', '‖z‖')
require(P+'nativePhase_real_sign_invariant', 'hτ : 0 ≤ τ', 'ho : τ < ‖overlap candidate reference‖',
        'nativePhase τ -candidate reference = nativePhase τ candidate reference')
require(D+'aligned_hasFDerivAt', 'hu : normSq u = 1', 'hf : groundMap b κ u = u',
        'HasFDerivAt aligned b κ alignedDerivative b κ u u, 0')
require(I+'nativeUpdate_near_fixed', '∀ᶠ x : State in nhds u, 0', 'ActivePhase', 'NativeLegal',
        'pack fullMap b κ m x = nativeUpdate τ b κ m pack x')
require(J+'nativePairMap_hasFDerivAt', 'HasFDerivAt nativePairMap τ b κ m fullDerivative b κ m u u, 0',
        'hτ0 : 0 ≤ τ', 'hτ1 : τ < 1')
require(J+'imaginary_phase_mode', 'hu : normSq u = 1', 'imaginaryDerivative m u u = 1 - 2 * m • u')
require(J+'half_mixing_imaginary_projection', 'imaginaryDerivative 1 / 2 u = 1 / 2 • projection u')
require(J+'nativePairMap_iterate_return', 'n : ℕ', 'nativeUpdate τ b κ m ^[n] pack x')
require(L+'c1_local_attraction_inside', 's ∈ nhds u', 'closedBall u r ⊆ s',
        'f^[n] y ∈ s', '↑q ^ n * dist y u')
require(L+'native_complex_local_attraction_of_rows', 'S R : Field ≃L[ℝ] Field',
        '∑ j, |', 'a < 1', 'c < 1', 'z : ComplexField', 'Tendsto', 'nativeUpdate τ b κ m ^[n] z',
        '∀ n : ℕ', 'ActivePhase', 'NativeLegal')
require(C+'originalTolerance_guard', '0 ≤ originalTolerance ∧ originalTolerance < 1')
require(C+'real_eigensolver_phase_return', 'hw : normSq w = 1', 'hamiltonian v w i',
        'energy v positiveGround v', 'nativePhase τ realEmbed w z')
require(C+'exists_legal_native_fixed', 'b : Field', 'κ m : ℝ', '∃ u,',
        '0 < u i', 'normSq u = 1', 'nativeUpdate τ b κ m realEmbed u = realEmbed u',
        'ActivePhase', 'NativeLegal')
require(C+'real_mode_full_return', 'he : normalizedJacobian b κ m u h = ℓ • h',
        'fullDerivative b κ m u h, 0 = ℓ • h, 0')
require(C+'native_half_imaginary_illegal', 'complexNormSq pack 0, u = 1', 'ActivePhase',
        'nativeMixed τ b κ 1 / 2 pack 0, u = 0', '¬NativeLegal')

build = read(PACKET+'lean_build.txt')
assert 'Build completed successfully (8196 jobs).' in build
assert not re.search(r'error:|warning:|Build failed', build)
version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT/'lean').decode().strip()
assert version == prior['actual_lean_version_checked']
mathlib = prior['mathlib']
libroot = ROOT/'lean/.lake/packages/mathlib'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=libroot).decode().strip() == mathlib['revision']
for p, h in mathlib['direct_proof_source_sha256'].items():
    assert sha((libroot/p).read_bytes()) == h
for p in ['Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean',
          'Mathlib/Analysis/Normed/Module/FiniteDimension.lean',
          'Mathlib/Analysis/Normed/Operator/Prod.lean']:
    b = (libroot/p).read_bytes()
    assert b == subprocess.check_output(['git', 'show', 'HEAD:'+p], cwd=libroot)
    mathlib['direct_proof_source_sha256'][p] = sha(b)

data = json.loads(read(PACKET+'imaginary_witnesses.json'))
result = native.replay(data)
assert result == json.loads(read(PACKET+'native_certificates.json'))
assert native.controls(data) == json.loads(read(PACKET+'controls.json'))
assert result['imaginary_strict_norm_bounds'] == 30
assert result['full_native_complex_locally_attracting_samples'] == 28
assert result['real_unstable_samples'] == 2
files = set(prior['source_sha256']) | {PRIOR, NEW_AUDIT, COMBINED,
    'lean/manifests/check_ground_native_axioms.lean', 'lean/manifests/check_ground_native_statements.lean',
    'math/GROUND_NATIVE_COMPLEX_2026-10-03.md', 'scripts/de_ground_native_verify.py',
    'scripts/de_ground_native_certificate.py'}
files.update('lean/SbtCosmo/Derivation/'+m+'.lean' for m in MODS)
files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.name != 'verification.json')
assert len(files) == 565, len(files)
v = dict(baseline_commit=BASE,
         scope='Unchanged original complex phase update: full real derivative, guarded local convergence and exact sampled imaginary-block certificates',
         axiom_audit=dict(declarations_cumulative=1782, declarations_preserved=1695,
                         declarations_fresh=87, new_local_theorems=new,
                         axioms=['Classical.choice', 'Quot.sound', 'propext'],
                         full_cumulative_command_rerun=False, preserved_raw_prefix=OLD_AUDIT,
                         preserved_prefix_sha256=sha(oldraw.encode()), fresh_suffix_receipt=NEW_AUDIT,
                         combined_receipt=COMBINED, success=True),
         lean_build=dict(command='lake build', jobs=8196, success=True, warnings_as_errors=True,
                         receipt_trailing_whitespace_normalized=True, diagnostic_content_removed=False),
         statement_check=dict(declarations=87, success=True), mathlib=mathlib,
         actual_lean_version_checked=version,
         original_return=dict(original_phase_sign_bug_retained=True, real_eigensolver_sign_return=True,
                              real_frechet_derivative_all_sixteen_coordinates=True,
                              actual_C_infinity_and_eventual_native_return_earned=True,
                              phase_and_normalization_guards_at_every_local_iterate=True,
                              mathematical_native_complex_local_attraction_samples=28,
                              exact_imaginary_block_norm_certificates=30,
                              concrete_sample_kernel_instantiations=False,
                              legal_native_fixed_points_all_backgrounds_couplings=True,
                              imaginary_unit_half_mixing_cancellation_and_illegality=True,
                              arbitrary_complex_eigensolver_phase_covariance=False,
                              unstable_nonlinear_escape=False, frozen_complex_initialization_basin=False,
                              continuous_nonlinear_branch_or_crossing=False, physical_Lambda_bridge=False),
         python_test_suite_rerun=False, exact_sample_replay_fresh=True,
         original_runtime_edited=False, paper_edited=False,
         review='adversarial self-review, not independent review', goal_complete=False,
         next_construction='Concrete kernel sample certificates; original-initialization basin or finite-run bound; continuous nonlinear branch/crossing if needed',
         source_sha256={p: sha((ROOT/p).read_bytes()) for p in sorted(files)},
         git_blob_sha256={p: sha(canonical(p)) for p in sorted(files)})
(ROOT/PACKET/'verification.json').write_text(json.dumps(v, indent=2)+'\n')
print('1782 cumulative standard-only closures; 87 new statements; 28 full complex local returns; 565 fingerprints')
