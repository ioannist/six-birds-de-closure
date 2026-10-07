"""Audit populated whole-background-box original-seed finite transport returns."""
import hashlib,json,re,subprocess
from pathlib import Path
import sys
sys.path.insert(0,"/home/repos/six-birds-de-closure/scripts")
from de_ground_offset_prefix_verify import closures,flatten,canonical
from de_ground_offset_sixty_verify import blobs
from de_ground_offset_transport_render import render,replay
from de_ground_offset_transport_build import HELPERS

ROOT=Path('/home/repos/six-birds-de-closure')
BASE='b58ad72d038896946db08aac6000e280df77d587'
PRIOR='results/ground_offset_sixty_2026-10-04/verification.json'
PACKET='results/ground_offset_transport_2026-10-04/'
PREFIX='SbtCosmo.Derivation.'
OLD_AUDIT='lean/manifests/axiom_audit_ground_offset_sixty_2026-10-04.txt'
NEW_AUDIT='lean/manifests/axiom_audit_ground_offset_transport_new_2026-10-04.txt'
COMBINED='lean/manifests/axiom_audit_ground_offset_transport_2026-10-04.txt'
FULL_AUDIT='results/ground_offset_transport_2026-10-04/cumulative-registered-receipts/axioms.log'
MUTABLE={'README.md','lean/README.md','lean/lakefile.lean','lean/manifests/check_axioms.lean',
  'lean/manifests/coverage_table.md','math/ORIGINAL_CLAIM_COVERAGE_2026-10-02.md'}
def read(p):return (ROOT/p).read_text()
def sha(b):return hashlib.sha256(b).hexdigest()
W=json.loads(read(PACKET+'witnesses.json'))
LEAVES=[f'GroundOffsetTransport.Point{i:03d}.Step{n:03d}' for i,p in enumerate(W['points']) for n in range(len(p['steps']))]
FAMILIES=[f'GroundOffsetTransport.Point{i:03d}' for i in range(18)]
MODS=HELPERS+LEAVES+FAMILIES+['GroundOriginalOffsetHullSeed']
def sourcepath(m):return 'lean/'+(PREFIX+m).replace('.','/')+'.lean'

def names():
    ns=[]
    for m in MODS:
        s=read(sourcepath(m));assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),m
        namespace=re.search(r'^namespace (\S+)',s,re.M).group(1)
        if m=='GroundCertifiedNativeTransportStep':namespace+='.Data'
        if m=='GroundCertifiedNativeTransport':namespace+='.Certificate'
        ns += [namespace+'.'+n for n in re.findall(r'^theorem ([\w.]+)',s,re.M)]
    assert len(MODS)==446 and len(ns)==len(set(ns))==6909,(len(MODS),len(ns))
    return ns

def hoist(raw):
    lines=raw.splitlines(keepends=True)
    return b''.join(l for l in lines if l.startswith(b'import '))+b''.join(l for l in lines if not l.startswith(b'import '))

def fingerprint_content(p):
    raw=(ROOT/p).read_bytes()
    # Git's automatic text classification checks the first8000 bytes for NUL.
    # Binary proof archives must retain their exact bytes, including CRLF pairs.
    return raw if b'\0' in raw[:8000] else canonical(p)

def verify():
    prior=json.loads(read(PRIOR));baseline=blobs(BASE,sorted(set(prior['source_sha256'])|{PRIOR}))
    assert (ROOT/PRIOR).read_bytes()==baseline[PRIOR]
    assert len(prior['source_sha256'])==2858
    for p,h in prior['source_sha256'].items():
        if p not in MUTABLE:assert sha((ROOT/p).read_bytes())==h and canonical(p)==baseline[p],p
    new=names();old_manifest=baseline['lean/manifests/check_axioms.lean'].decode()
    old=re.findall(r'^#print axioms (\S+)',old_manifest,re.M);assert len(old)==4867
    imports=''.join('import '+PREFIX+m+'\n' for m in MODS)
    expected_before=(old_manifest+'\n'+imports+'\n'+''.join('#print axioms '+n+'\n' for n in new)).encode()
    assert (ROOT/'lean/manifests/check_axioms.lean').read_bytes()==hoist(expected_before)
    assert read('lean/lakefile.lean')==baseline['lean/lakefile.lean'].decode()[:-2]+',\n    '+', '.join('`'+PREFIX+m for m in MODS)+']\n'
    for suffix,cmd in [('axioms','#print axioms '),('statements','#check ')]:
        assert read('lean/manifests/check_ground_offset_transport_'+suffix+'.lean')==imports+'\n'+''.join(cmd+n+'\n' for n in new)
    oldraw,newraw=read(OLD_AUDIT),read(NEW_AUDIT);assert (ROOT/OLD_AUDIT).read_bytes()==baseline[OLD_AUDIT]
    closures(oldraw,old);closures(newraw,new)
    header=('Cumulative audit: immutable 4867-declaration raw prefix plus freshly audited 6909-declaration suffix.\n'
      'Baseline: b58ad72; proof-source/toolchain identity checked by de_ground_offset_transport_verify.py.\n'
      'This concatenation preserves historical receipts; the fresh full 11776-declaration command is verified separately.\n\n')
    combined=header+oldraw+'\n'+newraw;closures(combined,old+new);(ROOT/COMBINED).write_text(combined)
    raw=read(PACKET+'theorem_statements.txt')
    assert [n.rstrip('.') for n in re.findall(r'^(SbtCosmo[\w.]*)',raw,re.M)]==new
    assert not re.search(r'error:|warning:',raw)
    starts=list(re.finditer(r'^SbtCosmo[\w.]*',raw,re.M));decls={}
    for i,m in enumerate(starts):decls[m.group().rstrip('.')]=flatten(raw[m.start():starts[i+1].start() if i+1<len(starts) else len(raw)].replace(PREFIX,''))
    def require(n,*ts):
        for t in ts:assert flatten(t) in decls[PREFIX+n],(n,t,decls[PREFIX+n])
    for name in ['whole_background_box_original_seed_return','whole_background_box_original_geometric_tail','whole_background_box_original_density_limit']:
        require('GroundOriginalOffsetHullSeed.'+name,'i : Fin 18','b : GroundState.Field','hb : ∀','β i j .Contains','orbit i b')
    require('GroundOriginalOffsetHullSeed.whole_background_box_original_seed_return','Tendsto','wholeRoot i hb','ActivePhase','NativeLegal','complexNormSq','= 1')
    final_type=decls[PREFIX+'GroundOriginalOffsetHullSeed.whole_background_box_original_seed_return']
    assert not re.search(r'\b(?:data|c|hentry|hrows|budget|certificate)\s*:',final_type)
    for name,root in [('exact_uniform_offset_original_seed_return','root'),('rounded_original_seed_return','roundedRoot')]:
        require('GroundOriginalOffsetHullSeed.'+name,'i : Fin 18','Tendsto','GroundOriginalOffsets.'+root+' i','ActivePhase','NativeLegal','complexNormSq','= 1')
        assert not re.search(r'\b(?:hb|hentry|data|c)\s*:',decls[PREFIX+'GroundOriginalOffsetHullSeed.'+name])
    require('GroundOriginalOffsetHullSeed.whole_background_box_eventual_density_separation','b₀ b₁ : GroundState.Field','9 / 100','Complex.normSq','orbit 0 b₀','orbit 17 b₁')
    assert replay(W)
    generated=render(W);assert len(generated)==440
    for p,s in generated.items():assert read(p)==s,p
    for p,h in W['source_sha256'].items():assert sha((ROOT/p).read_bytes())==h,p
    def receipt(p,success='Build completed successfully'):
        r=read(PACKET+p);assert success in r and not re.search(r'error:|warning:|build failed',r),p
        return r
    receipt('lean_build.txt','Build completed successfully (10003 jobs).')
    for stage,mods in [('helpers',HELPERS),('leaves',LEAVES),('families',FAMILIES),('return',['GroundOriginalOffsetHullSeed'])]:
        group=receipt(stage+'_builds.txt')
        for m in mods:
            p=sourcepath(m)
            assert 'Frozen source SHA256: '+sha((ROOT/p).read_bytes())+' '+p in group
            assert 'Fresh '+stage+' command: lake build '+PREFIX+m in group
            receipt(stage+'_'+m.replace('GroundOffsetTransport.','').replace('.','_')+'_build.txt')
        assert group.count('Build completed successfully')==len(mods)
    recovery=json.loads(read(PACKET+'leaves_recovery.json'))
    assert recovery['initial_driver_exit_code']==143
    assert recovery['initial_terminal_zero_leaves_retained']==102
    assert recovery['remaining_fresh_leaf_commands']==319
    assert recovery['preserved_cache_check_exit_code']==0 and recovery['remaining_complete']
    initial=read(PACKET+'leaves_initial_driver_interrupted.txt')
    finished=re.findall(r'^leaves (\S+) terminal (\d+) completed (\d+) / 421$',initial,re.M)
    assert len(finished)==102 and all(s=='0' for _,s,_ in finished)
    assert [int(n) for _,_,n in finished]==list(range(1,103))
    assert len({m for m,_,_ in finished})==102 and {m for m,_,_ in finished}<=set(LEAVES)
    cached=receipt('leaves_preserved_cache_check.txt')
    assert not re.search(r'Built SbtCosmo\.Derivation\.GroundOffsetTransport\.',cached)
    # Leaf certificates were built under the original family/template namespace
    # spelling. Preserve that historical evidence; only the explicitly checked
    # namespace patch may differ in the current integrated sources.
    repair_packet = ROOT/'results/ground_offset_namespace_recovery_checked_2026-10-05'
    repair_bindings = json.loads((repair_packet/'source-bindings.json').read_text())
    repair_audit = json.loads((repair_packet/'audit-summary.json').read_text())
    repair_verified = json.loads((repair_packet/'checkpoint-verification.json').read_text())
    assert repair_audit['standard_only'] and repair_audit['terminal_exit_code']==0
    assert repair_audit['checked_declarations']==6909
    assert repair_verified['terminal_exit_code']==0 and repair_verified['fresh_axiom_checks']==6909
    repair_plan = repair_bindings['repair_plan']
    import tarfile
    archive_manifest = json.loads((repair_packet/'archive-manifest.json').read_text())
    archive = repair_packet/'checked_artifacts.tar.gz'
    assert sha(archive.read_bytes())==archive_manifest['archive_sha256']
    entries={r['name']:r for r in archive_manifest['entries']}
    allowed={}
    with tarfile.open(archive,'r:gz') as saved:
        def original_source(member):
            raw=saved.extractfile(member).read()
            assert sha(raw)==entries[member]['sha256'],member
            return raw.decode()
        for r in repair_plan['source_patches']:
            if r['replacement'] is None:continue
            path=str(Path(r['original']).relative_to(ROOT))
            assert path.startswith('lean/SbtCosmo/Derivation/GroundOffsetTransport/Point')
            assert re.fullmatch(r'lean/SbtCosmo/Derivation/GroundOffsetTransport/Point\d{3}\.lean',path)
            before=original_source('workspace/'+path);patch=r['replacement']
            assert patch=={'old':'open GroundState GroundNativePhase GroundNativeBox GroundRationalInterval',
                           'new':'open GroundState GroundNativePhase GroundNativeIteration GroundNativeBox GroundRationalInterval'}
            assert before.count(patch['old'])==1 and sha(before.encode())==r['original_sha256']
            assert read(path)==before.replace(patch['old'],patch['new'])
            assert sha(read(path).encode())==r['repaired_sha256']
            allowed[path]=r['original_sha256']
        assert len(allowed)==18
        renderer='scripts/de_ground_offset_transport_render.py'
        before=original_source('workspace/'+renderer)
        assert sha(before.encode())==repair_plan['renderer_original_sha256']
        assert before.count(patch['old'])==1
        assert read(renderer)==before.replace(patch['old'],patch['new'])
        allowed[renderer]=repair_plan['renderer_original_sha256']
    header_packet=ROOT/'results/audit_manifest_header_repair_candidate_2026-10-05'
    header_manifest=json.loads((header_packet/'file-manifest.json').read_text())
    assert all(sha((header_packet/p).read_bytes())==h for p,h in header_manifest.items())
    header_plan=json.loads((header_packet/'repair-plan.json').read_text())
    manifest_path='lean/manifests/check_axioms.lean'
    before=(header_packet/'current_manifest.before.lean').read_bytes()
    repaired=(header_packet/'current_manifest.repaired.lean').read_bytes()
    assert before==expected_before and repaired==hoist(before)
    assert sha(before)==header_plan['manifests']['current']['before_sha256']
    assert (ROOT/manifest_path).read_bytes()==repaired
    assert sha(repaired)==header_plan['manifests']['current']['repaired_sha256']
    assert re.findall(rb'^#print axioms (\S+)',before,re.M)==re.findall(rb'^#print axioms (\S+)',repaired,re.M)
    assert hoist(repaired)==repaired
    allowed[manifest_path]=sha(before)
    assert len(allowed)==20
    full_root=ROOT/PACKET/'cumulative-registered-receipts'
    full_terminal=json.loads((full_root/'axioms-terminal.json').read_text())
    full_sources=json.loads((full_root/'source-snapshot.json').read_text())
    full_objects=json.loads((full_root/'objects-snapshot.json').read_text())
    expected_sources={str(p):sha(p.read_bytes()) for p in (ROOT/'lean').rglob('*.lean') if '.lake' not in p.relative_to(ROOT/'lean').parts}
    for name in ['lean-toolchain','lake-manifest.json']:p=ROOT/'lean'/name;expected_sources[str(p)]=sha(p.read_bytes())
    assert full_sources==expected_sources
    direct_imports=re.findall(r'^import (\S+)',repaired.decode(),re.M)
    assert len(direct_imports)==len(set(direct_imports))==1965
    expected_objects={m:sha((ROOT/'lean/.lake/build/lib/lean'/Path(*m.split('.')).with_suffix('.olean')).read_bytes()) for m in direct_imports}
    assert full_objects==expected_objects
    assert full_terminal['terminal_exit_code']==0
    assert full_terminal['command']==['lake','env','lean','-s','65536','manifests/check_axioms.lean']
    assert full_terminal['cwd']==str(ROOT/'lean')
    assert full_terminal['environment_overrides']=={'LEAN_NUM_THREADS':'4'}
    assert full_terminal['manifest_sha256']==sha(repaired)
    assert full_terminal['source_snapshot_sha256']==sha((full_root/'source-snapshot.json').read_bytes())
    assert full_terminal['objects_snapshot_sha256']==sha((full_root/'objects-snapshot.json').read_bytes())
    assert full_terminal['log_sha256']==sha((ROOT/FULL_AUDIT).read_bytes())
    fullraw=read(FULL_AUDIT);assert not re.search(r'error:|warning:',fullraw)
    closures(fullraw,old+new)
    changed=[]
    for p,h in recovery['source_sha256'].items():
        if sha((ROOT/p).read_bytes())==h:continue
        assert p in allowed and h==allowed[p],p
        changed.append(p)
    assert set(changed)==set(allowed)

    leaf_group=read(PACKET+'leaves_builds.txt')
    assert '102 fresh terminal-zero commands from the initial driver and319 fresh continuation commands' in leaf_group
    version=subprocess.check_output(['lake','env','lean','--version'],cwd=ROOT/'lean').decode().strip()
    assert version==prior['actual_lean_version_checked']
    mathlib=prior['mathlib'];libroot=ROOT/'lean/.lake/packages/mathlib'
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=libroot).decode().strip()==mathlib['revision']
    assert not subprocess.check_output(['git','status','--porcelain'],cwd=libroot).strip()
    for p,h in mathlib['direct_proof_source_sha256'].items():assert sha((libroot/p).read_bytes())==h,p
    files=set(prior['source_sha256'])|{PRIOR,NEW_AUDIT,COMBINED,
      'lean/manifests/check_ground_offset_transport_axioms.lean','lean/manifests/check_ground_offset_transport_statements.lean',
      'math/GROUND_OFFSET_HULL_SEED_RETURNS_2026-10-04.md','scripts/de_ground_offset_transport_render.py',
      'scripts/de_ground_offset_transport_build.py','scripts/de_ground_offset_transport_resume.py',
      'scripts/de_ground_offset_transport_verify.py'}
    files.update(sourcepath(m) for m in MODS)
    files.update(str(p.relative_to(ROOT)) for p in repair_packet.rglob('*') if p.is_file())
    files.update(str(p.relative_to(ROOT)) for p in header_packet.rglob('*') if p.is_file())
    files.update(str(p.relative_to(ROOT)) for p in full_root.rglob('*') if p.is_file())
    files.update(str(p.relative_to(ROOT)) for p in (ROOT/PACKET).iterdir() if p.is_file() and p.name!='verification.json')
    v=dict(baseline_commit=BASE,scope='Original complex-seed convergence for every fixed background in eighteen certified input boxes',
      axiom_audit=dict(declarations_cumulative=11776,declarations_preserved=4867,declarations_fresh=6909,new_local_theorems=new,
        axioms=['Classical.choice','Quot.sound','propext'],full_cumulative_command_rerun=True,fresh_full_receipt=FULL_AUDIT,preserved_raw_prefix=OLD_AUDIT,
        preserved_prefix_sha256=sha(oldraw.encode()),fresh_suffix_receipt=NEW_AUDIT,combined_receipt=COMBINED,success=True),
      lean_build=dict(command='lake build',jobs=10003,success=True,warnings_as_errors=True,receipt_trailing_whitespace_normalized=True,diagnostic_content_removed=False),
      statement_check=dict(declarations=6909,success=True),fresh_leaf_compilation=dict(modules=421,receipt=PACKET+'leaves_builds.txt',success=True,
        uninterrupted_cohort=False,initial_driver_exit_code=143,initial_terminal_zero_leaves_retained=102,
        remaining_fresh_continuation_commands=319,preserved_cache_check=PACKET+'leaves_preserved_cache_check.txt',
        interruption_history=PACKET+'leaves_initial_driver_interrupted.txt',recovery_provenance=PACKET+'leaves_recovery.json'),
      mathlib=mathlib,actual_lean_version_checked=version,
      seed_return=dict(background_boxes=18,finite_transport_steps=421,entry_times=[len(p['steps']) for p in W['points']],
        all_fixed_backgrounds_in_each_box=True,exact_uniform_offset_inputs=True,rounded_inputs=True,
        continuous_offset_interval=False,mathematical_original_seed_literal=True,both_initial_normalizations_preserved=True,
        original_phase_rule_unchanged=True,all_native_iterates_guarded_and_unit=True,geometric_tail=True,density_limits=True,
        eventual_endpoint_site_zero_density_gap='>9/100',whole_box_sixty_update_verdict=False,IEEE_per_operation_emulation=False,
        first_stopping_index=False,physical_Lambda_bridge=False),
      manifest_header_repair=dict(verified=True,packet=str(header_packet.relative_to(ROOT)),import_occurrences_preserved=True,nonimport_bytes_preserved=True,ordered_queries_preserved=11776,raw_byte_prefix_preserved=False),
      namespace_recovery=dict(verified=True,changed_historical_leaf_freeze_inputs=changed,old_leaf_certificates_unchanged=True,repair_packet=str(repair_packet.relative_to(ROOT))),
      Fraction_replay_rerun=True,generated_sources_regenerated_read_only=True,no_floating_solver_rerun=True,
      saved_matrices_proposal_role_only=True,prior_evidence_immutable_from_baseline=PRIOR,paper_edited=False,original_runtime_edited=False,
      review='adversarial self-review, not independent review',goal_complete=False,next_construction='Remaining coupling original-seed behavior and native cycles',
      source_sha256={p:sha((ROOT/p).read_bytes()) for p in sorted(files)},git_blob_sha256={p:sha(fingerprint_content(p)) for p in sorted(files)})
    (ROOT/PACKET/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
    print('11776 cumulative standard-only closures;6909 fresh statements;18 whole-box seed returns;',len(files),'fingerprints')
if __name__=='__main__':verify()
