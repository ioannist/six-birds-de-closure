"""Continue a terminal interrupted leaf cohort without losing its history.

Retained leaves require authoritative terminal-zero lines, successful receipts,
and a current Lake cache check. Every remaining leaf is forced to compile.
"""
from pathlib import Path
import concurrent.futures,hashlib,json,re,subprocess,time
from de_ground_offset_transport_build import ROOT,CWD,PACKET,PREFIX,sha,norm

def main():
    log=Path('/tmp/de-offset-transport-leaves-driver.log')
    history=PACKET/'leaves_initial_driver_interrupted.txt'
    assert not history.exists()
    # The original exec handle returned143, and its driver and workers are gone.
    processes=subprocess.check_output(['ps','-eo','args='],text=True)
    assert not any(x.strip()=='/usr/bin/python3 scripts/de_ground_offset_transport_build.py leaves' for x in processes.splitlines())
    assert not any(x.lstrip().startswith('lean ') and '/GroundOffsetTransport/Point' in x for x in processes.splitlines())
    original=log.read_text();history.write_text(norm(original))
    done=re.findall(r'^leaves (\S+) terminal (\d+) completed (\d+) / 421$',original,re.M)
    assert len(done)==102 and all(s=='0' for _,s,_ in done)
    assert [int(n) for _,_,n in done]==list(range(1,103))
    kept={m for m,_,_ in done};assert len(kept)==102
    w=json.loads((PACKET/'witnesses.json').read_text())
    modules=[f'GroundOffsetTransport.Point{i:03d}.Step{n:03d}' for i,p in enumerate(w['points']) for n in range(len(p['steps']))]
    assert len(modules)==421 and kept<=set(modules)
    files=[p for p in sorted(CWD.rglob('*.lean')) if '.lake' not in p.relative_to(CWD).parts]
    files += [PACKET/'witnesses.json',ROOT/'scripts/de_ground_offset_transport_render.py']
    frozen={p:sha(p) for p in files}
    def check():
        assert all(sha(p)==h for p,h in frozen.items()),'A frozen source changed'
    records={}
    for m in modules:
        p=PACKET/('leaves_'+m.replace('GroundOffsetTransport.','').replace('.','_')+'_build.txt')
        if m in kept:
            s=p.read_text();assert 'Build completed successfully' in s and not re.search(r'error:|warning:|build failed',s),m
            assert (CWD/'.lake/build/lib/lean'/((PREFIX+m).replace('.','/')+'.olean')).exists()
        elif p.exists():
            archived=p.with_name(p.stem+'_interrupted.txt');assert not archived.exists();p.rename(archived)
        records[m]=p
    cache=PACKET/'leaves_preserved_cache_check.txt';assert not cache.exists()
    with cache.open('w') as f:r=subprocess.run(['lake','build']+[PREFIX+m for m in modules if m in kept],cwd=CWD,stdout=f,stderr=subprocess.STDOUT)
    check();s=cache.read_text();cache.write_text(norm(s))
    assert r.returncode==0 and 'Build completed successfully' in s and not re.search(r'error:|warning:|build failed',s)
    assert not re.search(r'Built SbtCosmo\.Derivation\.GroundOffsetTransport\.',s),'Retained leaf cache was stale'
    provenance={'initial_driver_exit_code':143,'initial_terminal_zero_leaves_retained':102,'remaining_fresh_leaf_commands':319,'preserved_cache_check_exit_code':0,'remaining_complete':False,'source_sha256':{str(p.relative_to(ROOT)):h for p,h in frozen.items()},'initial_progress_receipt':str(history.relative_to(ROOT))}
    (PACKET/'leaves_recovery.json').write_text(json.dumps(provenance,indent=2)+'\n')
    print('Retained102 authoritative terminal-zero leaves; current cache/source check passed;319 fresh leaves remain',flush=True)
    def build(m):
        check();p=records[m];assert not p.exists()
        olean=CWD/'.lake/build/lib/lean'/((PREFIX+m).replace('.','/')+'.olean');olean.unlink(missing_ok=True)
        with p.open('w') as f:r=subprocess.run(['lake','build',PREFIX+m],cwd=CWD,stdout=f,stderr=subprocess.STDOUT)
        check();s=p.read_text();p.write_text(norm(s));bad=not ('Build completed successfully' in s) or bool(re.search(r'error:|warning:|build failed',s))
        return m,r.returncode,bad
    waiting=[m for m in modules if m not in kept];passed=set(kept);failures=[]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        it=iter(waiting);pending={pool.submit(build,next(it)) for _ in range(4)}
        while pending:
            completed,_=concurrent.futures.wait(pending,return_when=concurrent.futures.FIRST_COMPLETED)
            for f in completed:
                pending.remove(f)
                try:m,status,bad=f.result()
                except BaseException as e:failures.append(repr(e));print('exception',repr(e),flush=True);continue
                print('resumed leaves',m,'terminal',status,'completed',len(passed)+(status==0),'/421',flush=True)
                if status!=0 or bad:failures.append((m,status,bad))
                else:passed.add(m)
            if not failures:
                while len(pending)<4:
                    try:m=next(it)
                    except StopIteration:break
                    pending.add(pool.submit(build,m))
    check();assert not failures,failures;assert passed==set(modules)
    raw='Leaf verification combines102 fresh terminal-zero commands from the initial driver and319 fresh continuation commands.\n'
    raw+='Initial driver terminated143; retained command caches validated unchanged before continuation. No partial command is counted as passed.\n'
    raw+=f'{len(files)} source/configuration files frozen before/after continuation and preserved-cache validation.\n'
    raw+=''.join('Frozen source SHA256: '+h+' '+str(p.relative_to(ROOT))+'\n' for p,h in frozen.items())+'\n'
    for m in modules:raw+='Fresh leaves command: lake build '+PREFIX+m+'\n'+records[m].read_text()+'\n'
    (PACKET/'leaves_builds.txt').write_text(norm(raw))
    provenance['remaining_complete']=True;(PACKET/'leaves_recovery.json').write_text(json.dumps(provenance,indent=2)+'\n')
    print('All421 leaf commands covered with preserved interruption history and frozen-source checks',flush=True)
if __name__=='__main__':main()
