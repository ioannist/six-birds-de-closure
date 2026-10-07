from pathlib import Path
import hashlib, json, re, shutil

base = Path('/tmp/de_native_campaign_semantic_aggregate_recovery_2026-10-06')
old_path = Path('/tmp/de_native_campaign_stream_verify.py')
assert not base.exists(); base.mkdir()
s = old_path.read_text()
helper = r'''
REPAIR_MODULE = 'SbtCosmo.Derivation.NativeOriginalSampleResults'
QROOT = Path('/tmp/de_native_campaign_aggregate_recovery_2026-10-05')
SROOT = Path('/tmp/de_native_seed_real_returns_aggregate_recovery_2026-10-05')

def verify_aggregate_repair(plan):
    repair = plan['aggregate_proof_repair']
    assert repair['module'] == REPAIR_MODULE
    old_path = Path('/tmp/de-native-campaign-production-plan.json')
    old_review = Path('/tmp/de-native-campaign-integration-review.json')
    assert repair['historical_plan_sha256'] == sha(old_path)
    assert repair['historical_review_sha256'] == sha(old_review)
    original = read_json(old_path)
    assert len(original['modules']) == len(plan['modules']) == 1734
    assert original['fresh_theorem_count'] == plan['fresh_theorem_count'] == 20628
    changes = []
    for old, new in zip(original['modules'], plan['modules']):
        assert old['production_module'] == new['production_module']
        if old == new: continue
        changes.append(new['production_module'])
        assert new['production_module'] == REPAIR_MODULE
        for key in ['private_module', 'production_module', 'production_path', 'declared_theorems']:
            assert old[key] == new[key]
        assert new['historical_private_sha256'] == old['private_sha256']
        assert new['historical_production_sha256'] == old['production_sha256']
        assert set(new) == set(old) | {'private_source_override', 'production_source_override', 'historical_private_sha256', 'historical_production_sha256'}
    assert changes == [REPAIR_MODULE]
    row = next(r for r in plan['modules'] if r['production_module'] == REPAIR_MODULE)
    gate_path = Path(repair['checked_private_gate']); gate_dir = gate_path.parent
    assert sha(gate_path) == repair['checked_private_gate_sha256']
    manifest = read_json(gate_dir / 'file-manifest.json')
    assert all(sha(gate_dir / p) == h for p, h in manifest.items())
    gate = read_json(gate_path)
    assert gate['compiler_terminal_exit_code'] == gate['audit_terminal_exit_code'] == gate['terminal_exit_code'] == 0
    assert gate['standard_only'] and gate['checked_declarations'] == gate['unchanged_theorem_headers'] == 11
    assert row['declared_theorems'] == gate['names']
    private = Path(row['private_source_override']); public = Path(row['production_source_override'])
    assert private == gate_dir / 'NativeOriginalSampleResults.lean'
    assert public == QROOT / row['production_path']
    assert sha(private) == gate['source_sha256'] == row['private_sha256']
    assert sha(public) == row['production_sha256']
    old_private = Path('/tmp/de_native_cycle_lean/NativeOriginalSampleResults.lean')
    old_public = Path('/tmp/de_native_campaign_production_preview') / row['production_path']
    assert sha(old_private) == row['historical_private_sha256']
    assert sha(old_public) == row['historical_production_sha256']
    assert declaration_types(old_private.read_text()) == declaration_types(private.read_text())
    assert declaration_types(old_public.read_text()) == declaration_types(public.read_text())
    assert imports(old_private.read_text()) == imports(private.read_text())
    assert imports(old_public.read_text()) == imports(public.read_text())
    for original_text, repaired_text in [(old_private.read_text(), private.read_text()), (old_public.read_text(), public.read_text())]:
        assert re.findall(r'^def[^\n]*', original_text, re.M) == re.findall(r'^def[^\n]*', repaired_text, re.M)
    axiom_entries((gate_dir / 'statements-and-axioms.log').read_text(), gate['names'])
    assert sha(gate_dir / 'statements-and-axioms.log') == gate['audit_log_sha256']
    frozen = read_json(gate_dir / 'source-input-freeze.json')
    assert len(frozen) == 3705 and all(sha(p) == h for p, h in frozen.items())
    return private

'''
needle='def verify_sources(args):\n';assert s.count(needle)==1;s=s.replace(needle,helper+needle,1)
changes={
'def verify_exports(private):\n    types = declaration_types((private / "NativeOriginalSampleResults.lean").read_text())':'def verify_exports(private, aggregate_source=None):\n    types = declaration_types((aggregate_source if aggregate_source is not None else private / "NativeOriginalSampleResults.lean").read_text())',
'    plans = [read_json(args.plan), read_json(args.supplement_plan)]':'    plans = [read_json(args.plan), read_json(args.supplement_plan)]\n    aggregate_source = verify_aggregate_repair(plans[0])',
'            sources[row["production_module"]] = preview / row["production_path"]':'            sources[row["production_module"]] = Path(row["production_source_override"]) if "production_source_override" in row else preview / row["production_path"]',
'        p = args.private / (row["private_module"] + ".lean")':'        p = Path(row["private_source_override"]) if "private_source_override" in row else args.private / (row["private_module"] + ".lean")',
'    exports = verify_exports(args.private)':'    exports = verify_exports(args.private, aggregate_source)',
'Path("/tmp/de-native-campaign-qualified-stream-freeze.json")':'QROOT / "source-object-freeze.json"',
'Path("/tmp/de-native-campaign-qualified-stream-driver.log")':'QROOT / "driver.log"',
'"All1734 qualified modules and20628 fresh statement/axiom checks passed; replay, repository integration and commit pending"':'"All1734 qualified modules and20628 fresh statement/axiom checks passed; aggregate proof repaired; supplements, semantic replay and registered integration pending"',
'Path("/tmp/de-native-seed-real-returns-qualified-stream-freeze.json")':'SROOT / "source-freeze.json"',
'Path("/tmp/de-native-seed-real-returns-qualified-stream-driver.log")':'SROOT / "driver.log"',
'    private_gate_path = Path("/tmp/de-native-original-sample-results-audit-summary.json")':'    private_gate_path = Path(plans[0]["aggregate_proof_repair"]["checked_private_gate"])',
'"plan": "/tmp/de-native-campaign-production-plan.json"':'"plan": str(QROOT / "production-plan.json")',
'"supplement-plan": "/tmp/de-native-seed-real-returns-production-plan.json"':'"supplement-plan": str(SROOT / "production-plan.json")',
'"review": "/tmp/de-native-campaign-integration-review.json"':'"review": str(QROOT / "integration-review.json")',
'"qualified-summary": "/tmp/de-native-campaign-qualified-stream-summary.json"':'"qualified-summary": str(QROOT / "summary.json")',
'"qualified-receipts": "/tmp/de_native_campaign_qualified_stream_receipts"':'"qualified-receipts": str(QROOT / "receipts")',
'"qualified-objects": "/tmp/de_native_campaign_qualified_stream_objects"':'"qualified-objects": str(QROOT / "objects")',
'"supplement-summary": "/tmp/de-native-seed-real-returns-qualified-stream-summary.json"':'"supplement-summary": str(SROOT / "summary.json")',
'"supplement-receipts": "/tmp/de_native_seed_real_returns_qualified_stream_receipts"':'"supplement-receipts": str(SROOT / "receipts")',
'"supplement-objects": "/tmp/de_native_seed_real_returns_qualified_stream_objects"':'"supplement-objects": str(SROOT / "objects")',
'            "fresh_modules": 1738, "fresh_statement_checks": 20634,':'            "checked_modules": 1738, "retained_compile_checks": 993, "fresh_modules": 745, "fresh_statement_checks": 20634,',
}
for a,b in changes.items(): assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b,1)
old=r'''            log = receipts / (row["private_module"] + ".log")
            assert sha(log) == record["log_sha256"]
            assert not re.search(r"error:|warning:", log.read_text())
            obj = objects / Path(*record["module"].split(".")).with_suffix(".olean")
            assert sha(obj) == record["olean_sha256"], obj
            assert read_json(receipts / (row["private_module"] + "-terminal.json")) == record'''
new=r'''            if record.get("retained", False):
                assert count == (1734, 20628)
                retained = {r["module"]: r for r in read_json(QROOT / "retained-receipts.json")}
                assert record == dict(retained[record["module"]], retained=True)
                original_terminal = Path(record["original_terminal_path"])
                assert sha(original_terminal) == record["original_terminal_sha256"]
                original = read_json(original_terminal)
                assert all(record[k] == v for k,v in original.items())
                log = Path(record["log_path"]); obj = Path(record["object_path"])
                assert sha(record["source_path"]) == record["source_sha256"]
            else:
                log = receipts / (row["private_module"] + ".log")
                obj = objects / Path(*record["module"].split(".")).with_suffix(".olean")
                assert read_json(receipts / (row["private_module"] + "-terminal.json")) == record
                if "source_path" in record:
                    expected_source = Path(row["production_source_override"]) if "production_source_override" in row else args.preview / row["production_path"]
                    assert Path(record["source_path"]) == expected_source
                    assert Path(record["log_path"]) == log and Path(record["object_path"]) == obj
            assert sha(log) == record["log_sha256"]
            assert not re.search(r"error:|warning:", log.read_text())
            assert sha(obj) == record["olean_sha256"], obj
        if count == (1734, 20628):
            kept = {r["module"] for r in records if r.get("retained", False)}
            assert len(kept) == summary["retained_terminal_zero_modules"] == 993
            assert summary["fresh_recovery_modules"] == len(records)-len(kept) == 741
            dependencies = read_json(args.review)["dependencies"]
            assert REPAIR_MODULE not in kept
            assert all(set(dependencies[m]) <= kept for m in kept)'''
assert s.count(old)==1;s=s.replace(old,new,1)
output=base/'verify_recovery.py';compile(s,str(output),'exec');output.write_text(s)
shutil.copyfile(old_path,base/'historical-stream-verifier.py')
(base/'preparation.json').write_text(json.dumps(dict(controlled_replacements=len(changes)+3,original_verifier_sha256=hashlib.sha256(old_path.read_bytes()).hexdigest(),recovery_verifier_sha256=hashlib.sha256(output.read_bytes()).hexdigest(),source_and_replay_gates_preserved=True,modified_public_modules=1,qualified_success_path_pending=True),indent=2)+'\n')
print({'verifier':str(output),'controlled_replacements':len(changes)+3,'qualified_success_path_pending':True})
