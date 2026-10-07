"""Fresh builds of the whole-box transport packet with frozen source hashes.

Run one stage at a time. The leaf stage forces each certificate to compile
again, including any prototype previously built under the same module name.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,time

ROOT=Path(__file__).resolve().parents[1]
CWD=ROOT/'lean'
PACKET=ROOT/'results/ground_offset_transport_2026-10-04'
PREFIX='SbtCosmo.Derivation.'
HELPERS=['GroundFiniteNativeTransport','GroundNativeTransportGeometry','GroundNativeTransportJets',
  'GroundCertifiedNativeTransportStep','GroundCertifiedNativeTransport','GroundOffsetTransportReturn']

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def norm(s):return '\n'.join(t.rstrip() for t in s.splitlines()).rstrip()+'\n'

def run(stage,workers):
    w=json.loads((PACKET/'witnesses.json').read_text())
    leaves=[f'GroundOffsetTransport.Point{i:03d}.Step{n:03d}' for i,p in enumerate(w['points']) for n in range(len(p['steps']))]
    families=[f'GroundOffsetTransport.Point{i:03d}' for i in range(18)]
    mods=HELPERS if stage=='helpers' else leaves if stage=='leaves' else families if stage=='families' else ['GroundOriginalOffsetHullSeed']
    # Freeze the package options and every proof source, not only the direct imports.
    files=sorted(CWD.rglob('*.lean'))
    files=[p for p in files if '.lake' not in p.relative_to(CWD).parts]
    files += [PACKET/'witnesses.json',ROOT/'scripts/de_ground_offset_transport_render.py']
    hashes={p:sha(p) for p in files}
    if stage=='helpers':workers=1
    records=[]
    for m in mods:
        receipt=PACKET/(stage+'_'+m.replace('GroundOffsetTransport.','').replace('.','_')+'_build.txt')
        assert not receipt.exists(),receipt
        source=CWD/((PREFIX+m).replace('.','/')+'.lean')
        assert source.exists(),source
        if stage in ['helpers','leaves']:
            # No compiler for this packet may be live before starting this stage.
            olean=CWD/'.lake/build/lib/lean'/((PREFIX+m).replace('.','/')+'.olean')
            olean.unlink(missing_ok=True)
        records.append((m,receipt,['lake','build',PREFIX+m]))
    waiting=list(records);live={};done={}
    while waiting or live:
        while waiting and len(live)<workers:
            m,p,cmd=waiting.pop(0);f=p.open('w')
            live[m]=(subprocess.Popen(cmd,cwd=CWD,stdout=f,stderr=subprocess.STDOUT),f,p,cmd)
        for m,(proc,f,p,cmd) in list(live.items()):
            status=proc.poll()
            if status is not None:
                f.close();p.write_text(norm(p.read_text()));done[m]=status;del live[m]
                print(stage,m,'terminal',status,'completed',len(done),'/',len(mods),flush=True)
        if any(s!=0 for s in done.values()):waiting=[]
        if live:time.sleep(.5)
    assert all(sha(p)==h for p,h in hashes.items()),'A frozen source changed during compilation'
    assert len(done)==len(mods) and all(s==0 for s in done.values()),done
    raw=f'Fresh {stage} commands; {len(files)} source/configuration files frozen before/after execution.\n'
    raw+=''.join('Frozen source SHA256: '+h+' '+str(p.relative_to(ROOT))+'\n' for p,h in hashes.items())+'\n'
    for m,p,cmd in records:
        s=p.read_text();assert 'Build completed successfully' in s and not re.search(r'error:|warning:|build failed',s),m
        raw+='Fresh '+stage+' command: '+' '.join(cmd)+'\n'+s+'\n'
    (PACKET/(stage+'_builds.txt')).write_text(norm(raw))
    print('All',len(mods),stage,'commands passed with frozen sources',flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('stage',choices=['helpers','leaves','families','return'])
    parser.add_argument('--workers',type=int,default=4);args=parser.parse_args()
    assert 1<=args.workers<=4
    run(args.stage,args.workers)
