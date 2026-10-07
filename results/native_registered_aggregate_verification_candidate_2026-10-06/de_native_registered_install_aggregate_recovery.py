"""Install exact native proof sources only after private and whole-offset gates."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,tarfile,datetime,uuid,traceback,io
ROOT=Path('/home/repos/six-birds-de-closure')
VERIFIER=Path('/tmp/de_native_registered_verify_aggregate_recovery.py')
RECEIPTS=ROOT/'results/native_registered_original_audit_installation_receipts_2026-10-05'
spec=importlib.util.spec_from_file_location('native_installation_guards',VERIFIER)
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,data):p.write_text(json.dumps(data,indent=2)+'\n')
def current_hash(p):
    assert not p.is_symlink(),('Source target is a symlink',str(p))
    if p.exists():
        assert p.is_file(),('Source target is not a file',str(p))
        return sha(p)
    return None
def check_preimages(plan):
    for r in plan['targets']:
        p=ROOT/r['path']
        assert p.resolve().is_relative_to(ROOT.resolve()),r['path']
        assert current_hash(p)==r['existing_target_sha256'],('Unexpected target preimage',r['path'])
    for p,h in plan['input_sha256'].items():assert sha(p)==h,p
def snapshot_sources():
    result={str(p):sha(p) for p in (ROOT/'lean').rglob('*.lean') if '.lake' not in p.relative_to(ROOT/'lean').parts}
    for n in ['lean-toolchain','lake-manifest.json']:p=ROOT/'lean'/n;result[str(p)]=sha(p)
    return result
def snapshot_objects():return {str(p):sha(p) for p in (ROOT/'lean/.lake/build/lib/lean').rglob('*.olean')}
def atomically_install(p,raw):
    p.parent.mkdir(parents=True,exist_ok=True)
    assert p.parent.resolve().is_relative_to(ROOT.resolve())
    tmp=p.with_name(p.name+'.native-install-'+uuid.uuid4().hex)
    try:
        with tmp.open('xb') as stream:stream.write(raw);stream.flush();os.fsync(stream.fileno())
        os.replace(tmp,p)
        descriptor=os.open(p.parent,os.O_RDONLY|os.O_DIRECTORY)
        try:os.fsync(descriptor)
        finally:os.close(descriptor)
    finally:tmp.unlink(missing_ok=True)
def install_target(row,raw,receipts,installed,attempted):
    p=ROOT/row['path']
    assert current_hash(p)==row['existing_target_sha256'],row['path']
    attempted.append(row['path'])
    write(receipts/'journal.json',dict(installed=installed,attempted=attempted,pending_target=row['path'],phase='before_write',fresh_registered_build_pending=True,goal_complete=False))
    atomically_install(p,raw)
    assert sha(p)==row['sha256'],row['path']
    installed.append(row['path'])
    write(receipts/'journal.json',dict(installed=installed,attempted=attempted,pending_target=None,phase='write_completed',fresh_registered_build_pending=True,goal_complete=False))

def observed_targets(plan):
    observations={}
    for row in plan['targets']:
        p=ROOT/row['path']
        item=dict(original_sha256=row['existing_target_sha256'],proposed_sha256=row['sha256'])
        try:
            assert p.resolve().is_relative_to(ROOT.resolve()),'Target resolves outside repository'
            value=current_hash(p)
            item.update(observed_sha256=value,matches_original=value==row['existing_target_sha256'],matches_proposed=value==row['sha256'],absent=value is None)
        except BaseException as e:item.update(observation_error=repr(e))
        observations[row['path']]=item
    return observations

def record_installation_failure(receipts,plan,installed,attempted,error):
    observed=observed_targets(plan)
    pending=[p for p in attempted if p not in installed]
    write(receipts/'journal.json',dict(installed=installed,attempted=attempted,pending_targets=pending,phase='failed',observed_targets=observed,fresh_registered_build_pending=True,goal_complete=False))
    write(receipts/'terminal.json',dict(terminal_exit_code=1,installed=installed,attempted=attempted,pending_targets=pending,observed_targets=observed,error=repr(error),traceback=traceback.format_exc(),goal_complete=False))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--mode',choices=['candidate','apply'],default='candidate');args=ap.parse_args()
    plan,files,names,full=v.candidate()
    if args.mode=='candidate':
        print(json.dumps(dict(prepared_source_files=len(files),native_modules=1772,native_declarations=len(names),cumulative_queries=len(full),registered_sources_changed=False,proof_objects_installed=0,proof_gates_checked=False,goal_complete=False)),flush=True)
        return 0
    try:
        v.require_freezes_released()
        v.proof_gates(plan)
        offset=v.required(ROOT/'results/ground_offset_transport_2026-10-04/verification.json')
        assert offset['axiom_audit']['success'] and offset['axiom_audit']['declarations_cumulative']==11776
        assert offset['axiom_audit']['full_cumulative_command_rerun']
        assert offset['lean_build']['success'] and offset['lean_build']['jobs']==10003
        assert offset['namespace_recovery']['verified'] and offset['manifest_header_repair']['verified']
        for p,h in offset['source_sha256'].items():
            if p not in v.MUTABLE_DOCS:assert sha(ROOT/p)==h,p
        check_preimages(plan)
    except v.Pending as e:
        print(json.dumps(dict(status='pending',reason=str(e),registered_sources_changed=False,proof_objects_installed=0,goal_complete=False)),flush=True)
        return 2
    assert not RECEIPTS.exists();RECEIPTS.mkdir()
    before=snapshot_sources();objects=snapshot_objects()
    write(RECEIPTS/'before-source-snapshot.json',before);write(RECEIPTS/'before-objects-snapshot.json',objects)
    old_files={r['path']:(ROOT/r['path']).read_bytes() for r in plan['targets'] if r['existing_target_sha256'] is not None}
    archive=RECEIPTS/'original_target_files.tar.gz';entries=[]
    with tarfile.open(archive,'w:gz') as t:
        for p,raw in sorted(old_files.items()):
            info=tarfile.TarInfo(p);info.size=len(raw);t.addfile(info,io.BytesIO(raw));entries.append(dict(path=p,size=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
    with tarfile.open(archive,'r|gz') as t:
        for m,r in zip(t,entries,strict=True):assert m.isfile() and m.name==r['path'] and m.size==r['size'] and hashlib.sha256(t.extractfile(m).read()).hexdigest()==r['sha256']
    write(RECEIPTS/'original-target-archive-manifest.json',dict(archive_sha256=sha(archive),entries=entries))
    check_preimages(plan)
    assert snapshot_sources()==before and snapshot_objects()==objects
    write(RECEIPTS/'intent.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),installation_plan_sha256=sha(v.CANDIDATE/'installation-plan.json'),installer_sha256=sha(__file__),verifier_sha256=sha(VERIFIER),whole_offset_verification_sha256=sha(ROOT/'results/ground_offset_transport_2026-10-04/verification.json'),before_source_snapshot_sha256=sha(RECEIPTS/'before-source-snapshot.json'),before_objects_snapshot_sha256=sha(RECEIPTS/'before-objects-snapshot.json'),targets=plan['targets'],source_files=1786,proof_objects_installed=0,fresh_registered_build_pending=True,goal_complete=False))
    installed=[];attempted=[]
    try:
        for r in plan['targets']:
            install_target(r,files[r['path']],RECEIPTS,installed,attempted)
        assert all((ROOT/p).read_bytes()==raw for p,raw in files.items())
        after=snapshot_sources()
        target_sources={str(ROOT/p) for p in files}
        assert set(after)==set(before)|target_sources
        assert all(after[p]==h for p,h in before.items() if p not in target_sources)
        assert all(after[str(ROOT/r['path'])]==r['sha256'] for r in plan['targets'])
        assert snapshot_objects()==objects,'Source installation must not copy or alter proof objects'
        v.original_audit_proof_gate(plan)
        write(RECEIPTS/'after-source-snapshot.json',after)
        result=dict(terminal_exit_code=0,installed_source_files=len(installed),native_modules=1772,native_declarations=20798,cumulative_queries=32574,proof_objects_installed=0,existing_objects_unchanged=True,fresh_registered_build_pending=True,fresh_registered_statements_pending=True,fresh_registered_cumulative_axioms_pending=True,goal_complete=False)
        write(RECEIPTS/'terminal.json',result);print(json.dumps(result),flush=True);return 0
    except BaseException as e:
        record_installation_failure(RECEIPTS,plan,installed,attempted,e)
        raise
if __name__=='__main__':raise SystemExit(main())
