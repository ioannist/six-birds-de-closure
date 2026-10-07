"""Refresh one proof body; preserve the complete registered theorem inventory."""
from pathlib import Path
import copy, hashlib, io, json, tarfile

ROOT = Path('/home/repos/six-birds-de-closure')
OLD = ROOT / 'results/native_registered_original_audit_installation_candidate_2026-10-05'
OUT = ROOT / 'results/native_registered_aggregate_installation_candidate_2026-10-06'
Q = Path('/tmp/de_native_campaign_aggregate_recovery_2026-10-05')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
digest = lambda b: hashlib.sha256(b).hexdigest()
load = lambda p: json.loads(Path(p).read_text())
assert not OUT.exists()
assert all(sha(OLD / p) == h for p, h in load(OLD / 'file-manifest.json').items())
old = load(OLD / 'installation-plan.json')
qp = load(Q / 'production-plan.json')
repair = qp['aggregate_proof_repair']
module = 'SbtCosmo.Derivation.NativeOriginalSampleResults'
qr = next(r for r in qp['modules'] if r['production_module'] == module)
new_source = Path(qr['production_source_override'])
assert sha(new_source) == qr['production_sha256']
payload = {}
with tarfile.open(OLD / 'proposed_registered_files.tar.gz', 'r|gz') as archive:
    for member, row in zip(archive, old['targets'], strict=True):
        assert member.isfile() and member.name == row['path']
        raw = archive.extractfile(member).read()
        assert digest(raw) == row['sha256'] and len(raw) == row['size']
        payload[member.name] = raw
plan = copy.deepcopy(old)
row = next(r for r in plan['modules'] if r['module'] == module)
target = row['target']
assert digest(payload[target]) == row['source_sha256'] == qr['historical_production_sha256']
assert row['declared_theorems'] == qr['declared_theorems']
payload[target] = new_source.read_bytes()
row['candidate_source'] = str(new_source)
row['source_sha256'] = sha(new_source)
plan['aggregate_proof_repair'] = repair
plan['aggregate_recovery_production_plan_sha256'] = sha(Q / 'production-plan.json')
plan['historical_original_audit_candidate_plan_sha256'] = sha(OLD / 'installation-plan.json')
plan['status'] = 'One aggregate proof-body repair; unchanged1772 modules/20798 declarations/32574 cumulative queries; registered gates pending'
plan['input_sha256'][str(OLD / 'installation-plan.json')] = sha(OLD / 'installation-plan.json')
plan['input_sha256'][str(Q / 'production-plan.json')] = sha(Q / 'production-plan.json')
plan['input_sha256'][str(new_source)] = sha(new_source)
OUT.mkdir()
archive_path = OUT / 'proposed_registered_files.tar.gz'
with tarfile.open(archive_path, 'w:gz') as archive:
    for entry in plan['targets']:
        raw = payload[entry['path']]
        entry.update(sha256=digest(raw), size=len(raw))
        member = tarfile.TarInfo(entry['path']); member.size = len(raw)
        archive.addfile(member, io.BytesIO(raw))
plan['source_archive_sha256'] = sha(archive_path)
assert (plan['native_modules'], plan['native_fresh_declarations'], plan['prospective_default_declarations'], len(payload)) == (1772, 20798, 32574, 1786)
assert [r for r in old['targets'] if r != next(s for s in plan['targets'] if s['path'] == r['path'])] == [next(r for r in old['targets'] if r['path'] == target)]
assert [r for r, s in zip(old['modules'], plan['modules'], strict=True) if r != s] == [next(r for r in old['modules'] if r['module'] == module)]
with tarfile.open(archive_path, 'r|gz') as archive:
    for member, entry in zip(archive, plan['targets'], strict=True):
        assert member.isfile() and member.name == entry['path']
        assert digest(archive.extractfile(member).read()) == entry['sha256']
(OUT / 'installation-plan.json').write_text(json.dumps(plan, indent=2) + '\n')
(OUT / 'prepare_driver.py').write_bytes(Path(__file__).read_bytes())
(OUT / 'README.md').write_text('Source-only candidate. Exactly one aggregate proof body differs from the historical original-audit candidate. All theorem headers, definitions, imports, inventories, source preimages and registered gates are retained. No registered source or object has been changed. The repaired aggregate has private evidence; qualified and registered gates remain pending.\n')
(OUT / 'file-manifest.json').write_text(json.dumps({p.name: sha(p) for p in OUT.iterdir() if p.is_file()}, indent=2) + '\n')
print(json.dumps(dict(changed_proof_sources=1, modules=1772, declarations=20798, cumulative_queries=32574, archive_targets=1786, registered_sources_changed=False)))
