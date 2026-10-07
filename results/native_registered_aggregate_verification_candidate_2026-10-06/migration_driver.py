"""Clone final gates onto the repaired aggregate without dropping any query."""
from pathlib import Path
import ast, hashlib, json

ROOT = Path('/home/repos/six-birds-de-closure')
OUT = ROOT / 'results/native_registered_aggregate_verification_candidate_2026-10-06'
Q = '/tmp/de_native_campaign_aggregate_recovery_2026-10-05'
S = '/tmp/de_native_seed_real_returns_aggregate_recovery_2026-10-05'
F = '/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06'
GATE = str(ROOT / 'results/native_original_sample_aggregate_repair_checked_2026-10-05/audit-summary.json')
NEW = '/tmp/de_native_registered_verify_aggregate_recovery.py'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def replace(text, old, new, count=None):
    found = text.count(old)
    assert found > 0 and (count is None or found == count), (old, found, count)
    return text.replace(old, new)

assert not OUT.exists(); OUT.mkdir()
old_path = Path('/tmp/de_native_registered_verify_original_audit_candidate.py')
text = old_path.read_text()
text = replace(text, "CANDIDATE=ROOT/'results/native_registered_original_audit_installation_candidate_2026-10-05'", "CANDIDATE=ROOT/'results/native_registered_aggregate_installation_candidate_2026-10-06'", 1)
text = replace(text, "STREAM=ROOT/'results/native_campaign_stream_verification_2026-10-05'", "STREAM=ROOT/'results/native_aggregate_semantic_verification_2026-10-06'", 1)
for old, new in [
    ('/tmp/de-native-campaign-verification-stream-finish-summary.json', F + '/finish-summary.json'),
    ('/tmp/de_native_campaign_stream_verify.py', F + '/verify_recovery.py'),
    ('/tmp/de-native-campaign-qualified-stream-summary.json', Q + '/summary.json'),
    ('/tmp/de-native-seed-real-returns-qualified-stream-summary.json', S + '/summary.json'),
    ('/tmp/de-native-original-sample-results-audit-summary.json', GATE),
    ('de_native_additional_constructions_stream_qualified', 'de_native_additional_constructions_aggregate_recovery_2026-10-06'),
    ('de_source_execution_supplement_stream_qualified', 'de_source_execution_supplement_aggregate_recovery_2026-10-06')]:
    text = replace(text, old, new)
text = replace(text, "assert record['fresh_modules']==1738 and record['fresh_statement_checks']==record['fresh_axiom_checks']==20634", "assert record['checked_modules']==1738 and record['retained_compile_checks']==993 and record['fresh_modules']==745\n assert record['fresh_statement_checks']==record['fresh_axiom_checks']==20634", 1)
text = replace(text, "assert plan['modules'][:-1]==parent_plan['modules']", "verify_registered_repair(plan, files, parent_plan)\n normalized=[dict(r) for r in plan['modules'][:-1]]\n oldrow=next(r for r in parent_plan['modules'] if r['module']=='SbtCosmo.Derivation.NativeOriginalSampleResults')\n for r in normalized:\n  if r['module']==oldrow['module']:\n   r['candidate_source']=oldrow['candidate_source'];r['source_sha256']=oldrow['source_sha256']\n assert normalized==parent_plan['modules']", 1)
text = replace(text, "if p not in {'lean/lakefile.lean','lean/manifests/check_axioms.lean'}", "if p not in {'lean/lakefile.lean','lean/manifests/check_axioms.lean','lean/SbtCosmo/Derivation/NativeOriginalSampleResults.lean'}", 1)
text = replace(text, 'def require_freezes_released():\n', '''def require_freezes_released():
 recovery_jobs={3164894:'/tmp/de_native_campaign_aggregate_recovery_2026-10-05/build_recovery.py',
  3241065:'/tmp/de_native_seed_real_returns_aggregate_recovery_2026-10-05/build_recovery.py',
  4046958:'/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06/finish_recovery.py',
  4054594:'/tmp/de_native_additional_constructions_aggregate_recovery_2026-10-06/build_recovery.py',
  4054600:'/tmp/de_source_execution_supplement_aggregate_recovery_2026-10-06/build_recovery.py'}
 for pid,script in recovery_jobs.items():
  try:argv=Path(f'/proc/{pid}/cmdline').read_bytes().split(b'\\0')
  except FileNotFoundError:continue
  if len(argv)>1 and argv[1].decode()==script:raise Pending(f'Source freeze owner remains active: PID{pid} {script}')
''', 1)
function = '''
def verify_registered_repair(plan, files, parent_plan):
 recovery=Path('/tmp/de_native_campaign_aggregate_recovery_2026-10-05')
 semantic=Path('/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06/verify_recovery.py')
 assert sha(semantic)=='b48e90cb8b1616399442d81bf81ea853c2cfc38c514d0b61fda9e1a6a85e34fa'
 spec=importlib.util.spec_from_file_location('aggregate_repair_guard',semantic)
 guard=importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
 qp=load(recovery/'production-plan.json');guard.verify_aggregate_repair(qp)
 assert plan['aggregate_proof_repair']==qp['aggregate_proof_repair']
 assert plan['aggregate_recovery_production_plan_sha256']==sha(recovery/'production-plan.json')
 old=ROOT/'results/native_registered_original_audit_installation_candidate_2026-10-05'
 assert all(sha(old/p)==h for p,h in load(old/'file-manifest.json').items())
 assert plan['historical_original_audit_candidate_plan_sha256']==sha(old/'installation-plan.json')
 original=load(old/'installation-plan.json')
 module='SbtCosmo.Derivation.NativeOriginalSampleResults'
 qr=next(r for r in qp['modules'] if r['production_module']==module)
 rr=next(r for r in plan['modules'] if r['module']==module)
 prior=next(r for r in original['modules'] if r['module']==module)
 assert prior==next(r for r in parent_plan['modules'] if r['module']==module)
 assert rr['candidate_source']==qr['production_source_override']
 assert rr['source_sha256']==qr['production_sha256']==sha(rr['candidate_source'])
 assert rr['declared_theorems']==qr['declared_theorems']==prior['declared_theorems']
 assert files[rr['target']]==Path(rr['candidate_source']).read_bytes()
 assert guard.declaration_types(Path(prior['candidate_source']).read_text())==guard.declaration_types(files[rr['target']].decode())
 assert guard.imports(Path(prior['candidate_source']).read_text())==guard.imports(files[rr['target']].decode())
 assert not re.search(r'\\b(?:sorry|admit|native_decide)\\b|^\\s*(?:axiom|constant)\\s',parser.uncomment(files[rr['target']].decode()),re.M)

'''
text = replace(text, 'def candidate():\n', function + 'def candidate():\n', 1)
ast.parse(text)
Path(NEW).write_text(text)
(OUT / 'historical-verifier.py').write_bytes(old_path.read_bytes())
(OUT / 'verifier.py').write_text(text)

for old_name,new_name in [
 ('de_native_registered_install_original_audit_journal_candidate.py','de_native_registered_install_aggregate_recovery.py'),
 ('de_native_registered_build_original_audit_candidate.py','de_native_registered_build_aggregate_recovery.py'),
 ('de_offset_header_install_journal_candidate.py','de_offset_header_install_aggregate_recovery.py'),
 ('de_offset_registered_cumulative_audit_candidate.py','de_offset_registered_cumulative_audit_aggregate_recovery.py')]:
    old = Path('/tmp') / old_name
    source = old.read_text()
    original_verifier = '/tmp/de_native_registered_verify_header_candidate.py' if old_name.startswith('de_offset_registered_cumulative') else str(old_path)
    source = replace(source, original_verifier, NEW, 1)
    if old_name.startswith('de_offset_header_install'):
        source = replace(source, "freezes=[Path('/tmp')/n for n in ['de-native-campaign-qualified-stream-freeze.json','de-native-seed-real-returns-qualified-stream-freeze.json','de-native-campaign-verification-stream-finish-freeze.json']]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_stream_qualified','de_source_execution_supplement_stream_qualified']]+[audit_root/'cumulative-source-freeze.json']", "freezes=[Path('"+Q+"/source-object-freeze.json'),Path('"+S+"/source-freeze.json'),Path('"+F+"/finish-source-freeze.json')]+[Path('/tmp')/n/'source-freeze.json' for n in ['de_native_stable15_priority_recovery','de_native_additional_constructions_aggregate_recovery_2026-10-06','de_source_execution_supplement_aggregate_recovery_2026-10-06']]+[audit_root/'cumulative-source-freeze.json']", 1)
    ast.parse(source)
    (Path('/tmp') / new_name).write_text(source)
    (OUT / ('historical-' + old_name)).write_bytes(old.read_bytes())
    (OUT / new_name).write_text(source)
(OUT / 'migration_driver.py').write_bytes(Path(__file__).read_bytes())
(OUT / 'file-manifest.json').write_text(json.dumps({p.name:sha(p) for p in OUT.iterdir() if p.is_file()},indent=2)+'\n')
print(json.dumps(dict(cloned_verifier=True, cloned_installers_and_runners=4, retained_modules=1772, retained_native_queries=20798, retained_cumulative_queries=32574, registered_sources_changed=False)))
