"""Audit all eighteen populated original rounded-offset sixty-update verdicts."""
import hashlib,json,re,subprocess
from pathlib import Path
from de_ground_offset_prefix_verify import closures,flatten,canonical
from de_ground_offset_sixty_render import replay,render_extensions,render_prefixes,render_fast,render_direct,render_failures
ROOT=Path(__file__).resolve().parents[1]
BASE='07b31f573c5a340ac2aadff1e48a775e5394656c'
PRIOR='results/ground_offset_prefix_2026-10-04/verification.json'
PACKET='results/ground_offset_sixty_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
OLD_AUDIT='lean/manifests/axiom_audit_ground_offset_prefix_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_offset_sixty_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_offset_sixty_2026-10-04.txt'
MUTABLE={'README.md','lean/README.md','lean/lakefile.lean','lean/manifests/check_axioms.lean','lean/manifests/coverage_table.md','math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}
def read(p):return (ROOT/p).read_text()
def sha(b):return hashlib.sha256(b).hexdigest()
def blobs(ref,paths):
 raw=subprocess.check_output(['git','cat-file','--batch'],cwd=ROOT,input=''.join(ref+':'+p+'\n' for p in paths).encode())
 out={};at=0
 for p in paths:
  end=raw.index(b'\n',at);header=raw[at:end].split();assert len(header)==3 and header[1]==b'blob',(p,header)
  size=int(header[2]);at=end+1;out[p]=raw[at:at+size];at+=size;assert raw[at:at+1]==b'\n';at+=1
 assert at==len(raw);return out
W=json.loads(read(PACKET+'witnesses.json'))
MODS=['GroundComplexCoordinateBudget','GroundComplexFiniteBudget','GroundOffsetSelectorBudget']
MODS += [f'GroundOffsetSixtyPrefix.Point{p["index"]:03d}.Step{n:03d}' for p in W['extensions'] for n in range(p['start'],60)]
MODS += [f'GroundOffsetSixtyPrefix.Point{p["index"]:03d}' for p in W['extensions']]
MODS += [f'GroundOffsetSixtyTests.Point{i:03d}' for i in range(18)]+['GroundOriginalOffsetSixty']
def sourcepath(m):return 'lean/'+(PREFIX+m).replace('.','/')+'.lean'
def names():
 ns=[]
 for m in MODS:
  s=read(sourcepath(m));assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),m
  namespace=re.search(r'^namespace (\S+)',s,re.M).group(1)
  ns += [namespace+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
 assert len(MODS)==159 and len(ns)==len(set(ns))==423,(len(MODS),len(ns))
 return ns

def verify():
 prior=json.loads(read(PRIOR));baseline=blobs(BASE,sorted(set(prior['source_sha256'])|{PRIOR}))
 assert (ROOT/PRIOR).read_bytes()==baseline[PRIOR]
 assert len(prior['source_sha256'])==2521
 for p,h in prior['source_sha256'].items():
  if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline[p],p
 new=names();old_manifest=baseline['lean/manifests/check_axioms.lean'].decode()
 old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M);assert len(old)==4444
 imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
 assert read('lean/manifests/check_axioms.lean')==old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)
 assert read('lean/lakefile.lean')==baseline['lean/lakefile.lean'].decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
 for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
  assert read('lean/manifests/check_ground_offset_sixty_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
 oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT);assert (ROOT/OLD_AUDIT).read_bytes()==baseline[OLD_AUDIT]
 closures(oldraw,old);closures(newraw,new)
 header=('Cumulative audit: immutable 4444-declaration raw prefix plus freshly audited 423-declaration suffix.\n'
  'Baseline: 07b31f5; proof-source/toolchain identity checked by de_ground_offset_sixty_verify.py.\n'
  'Full 4867-declaration command was not rerun in this packet.\n\n')
 combined=header+oldraw+'\n'+newraw;closures(combined,old+new);(ROOT/COMBINED).write_text(combined)
 raw=read(PACKET+'theorem_statements.txt')
 assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',raw,re.M)]==new
 assert not re.search(r'error:|warning:',raw)
 starts=list(re.finditer(r'^SbtCosmo[\w.]*',raw,re.M));decls={}
 for i,m in enumerate(starts):decls[m.group().rstrip('.')]=flatten(raw[m.start():starts[i+1].start() if i+1<len(starts) else len(raw)].replace(PREFIX,''))
 def require(n,*ts):
  for t in ts:assert flatten(t) in decls[PREFIX+n],(n,t,decls[PREFIX+n])
 require('GroundOriginalOffsetSixty.original_sixty_verdict','i : Fin 18','GroundOriginalOffsetSixty.Tests i','↔','GroundOriginalOffsetSixty.verdict i = true')
 assert not re.search(r'\b(?:h\w*)\s*:',decls[PREFIX+'GroundOriginalOffsetSixty.original_sixty_verdict'])
 require('GroundOriginalOffsetSixty.failed_offsets','¬GroundOriginalOffsetSixty.Tests i','i = 1 ∨ i = 2 ∨ i = 17')
 require('GroundOriginalOffsetSixty.passing_count','verdict i = true','card = 15')
 require('GroundOriginalOffsetSixty.failing_count','verdict i = false','card = 3')
 for i in range(18):
  name=f'GroundOffsetSixtyTests.Point{i:03d}.'+('actual_four_source_tests_fail' if i in [1,2,17] else 'actual_four_source_tests')
  require(name,'GroundSourceDiagnostics.MeetsConvergence','GroundNativeControls.originalTolerance',f'GroundOriginalOffsets.rounded_b {i}',f'GroundOffsetSeedReturn.orbit {i} 59',f'GroundOffsetSeedReturn.orbit {i} 60')
  if i in [1,2,17]:require(name,'¬')
 for p,h in W['source_sha256'].items():assert sha((ROOT/p).read_bytes())==h,p
 assert replay(W)
 generated=render_extensions(W)|render_prefixes(W)|render_fast(W)|render_direct(W)|render_failures(W)
 assert len(generated)==155
 for p,s in generated.items():assert read(p)==s,p
 final=read(sourcepath('GroundOriginalOffsetSixty'))
 for t in ['GroundOriginalResiduals.ε','GroundNativeControls.originalTolerance','(κ i : ℝ)','(1/2)','(orbit i 59) (orbit i 60)']:
  assert t in final,t
 for i in range(18):assert f'GroundOffsetSixtyTests.Point{i:03d}.actual_four_source_tests' in final
 for m in ['GroundComplexFiniteBudget','GroundOffsetSelectorBudget']:
  s=read(sourcepath(m))
  assert 'nativeCandidate' in s and 'l2' in s,m
 def receipt(p,success='Build completed successfully'):
  r=read(PACKET+p);assert success in r and not re.search(r'error:|warning:|build failed',r),p
  return r
 receipt('lean_build.txt','Build completed successfully (9557 jobs).')
 leaf=receipt('leaf_builds.txt');assert leaf.count('Build completed successfully (8668 jobs).')==132
 for p in W['extensions']:
  i=p['index']
  for n in range(p['start'],60):
   m=f'GroundOffsetSixtyPrefix.Point{i:03d}.Step{n:03d}';src=sourcepath(m)
   assert 'Frozen source SHA256: '+sha((ROOT/src).read_bytes())+' '+src in leaf
   assert 'Fresh leaf command: lake build '+PREFIX+m in leaf
   receipt(f'point{i:03d}_step{n:03d}_build.txt')
 groups=[('prefix_builds.txt',[f'GroundOffsetSixtyPrefix.Point{i:03d}' for i in [0,2,3,16,17]]),
 ('fast_builds.txt',[f'GroundOffsetSixtyTests.Point{i:03d}' for i in range(4,16)]),
 ('direct_builds.txt',[f'GroundOffsetSixtyTests.Point{i:03d}' for i in [0,3,16]]),
 ('failure_builds.txt',[f'GroundOffsetSixtyTests.Point{i:03d}' for i in [1,2,17]])]
 for name,ms in groups:
  r=receipt(name)
  for m in ms:
   p=sourcepath(m);assert 'Frozen source SHA256: '+sha((ROOT/p).read_bytes())+' '+p in r
   assert 'lake build '+PREFIX+m in r
 for i in range(18):receipt(f'point{i:03d}_tests_build.txt')
 for i in [0,2,3,16,17]:receipt(f'point{i:03d}_prefix_build.txt')
 for m in MODS[:3]:receipt(m+'_build.txt')
 receipt('family_build.txt')
 version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip();assert version==prior['actual_lean_version_checked']
 mathlib=prior['mathlib'];libroot=ROOT/'lean/.lake/packages/mathlib'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
 assert not subprocess.check_output(['git','status','--porcelain'],cwd=libroot).strip()
 for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
 files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,'lean/manifests/check_ground_offset_sixty_axioms.lean','lean/manifests/check_ground_offset_sixty_statements.lean','math/GROUND_OFFSET_SIXTY_VERDICTS_2026-10-04.md','scripts/de_ground_offset_sixty_render.py','scripts/de_ground_offset_sixty_verify.py'}
 files.update(sourcepath(m) for m in MODS)
 files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.is_file() and p.name!='verification.json')
 v=dict(baseline_commit=BASE,scope='Exact fixed60 source convergence verdicts at all18 rounded offset inputs',
  axiom_audit=dict(declarations_cumulative=4867,declarations_preserved=4444,declarations_fresh=423,new_local_theorems=new,axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=False,preserved_raw_prefix=OLD_AUDIT,preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,combined_receipt=COMBINED,success=True),
  lean_build=dict(command='lake build',jobs=9557,success=True,warnings_as_errors=True,receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
  statement_check=dict(declarations=423,success=True),fresh_leaf_compilation=dict(modules=132,receipt=PACKET+'leaf_builds.txt',success=True),mathlib=mathlib,actual_lean_version_checked=version,
  finite_verdict=dict(background_offset_instances=18,passes=15,failures=3,failure_indices=[1,2,17],failure_offsets=['-5','-3','10'],failure_reason='actual59-to60 Euclidean last-update residual exceeds original tolerance',
   rounded_background_inputs=True,exact_uniform_offset_seed_return=False,whole_background_box_seed_return=False,
   mathematical_original_seed_literal=True,both_initial_normalizations_preserved=True,original_phase_rule_unchanged=True,
   actual_current_source_selector=True,actual_Rayleigh_energy=True,both_diagnostic_phase_calls=True,all_native_iterates_guarded_and_unit=True,
   all18_eventual_convergence_preserved=True,IEEE_per_operation_emulation=False,first_stopping_index=False,physical_Lambda_bridge=False),
  Fraction_replay_rerun=True,generated_sources_regenerated_read_only=True,no_floating_solver_rerun=True,saved_matrices_proposal_role_only=True,prior_evidence_immutable_from_baseline=PRIOR,
  paper_edited=False,original_runtime_edited=False,review='adversarial self-review, not independent review',goal_complete=False,next_construction='Exact uniform-offset seed returns and remaining coupling seed returns',
  source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},git_blob_sha256={p:sha(canonical(p)) for p in sorted(files)})
 (ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
 print(f'4867 cumulative standard-only closures;423 fresh statements;18 exact fixed60 verdicts;{len(files)} fingerprints')
if __name__=='__main__':verify()
