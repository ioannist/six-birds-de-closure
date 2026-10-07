"""Verify exact native-source restoration coverage without overstating completion.

The source stage checks source identity, complete theorem enumeration, import
translation/DAG, aggregate statement shapes, and the saved full exact replay.
The qualified stage additionally requires all fresh qualified compile/audit
receipts. It does not infer repository integration or IEEE execution.
"""
import argparse
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path('/home/repos/six-birds-de-closure')
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COUNTS = [(1734, 20628), (4, 6)]
SAMPLES = {"cycle20": (10, 320), "cycle30": (11, 152)} | {
    f"stable{i:03d}": (i, 178 if i == 9 else 60)
    for i in [1, 3, 4, 5, 6, 7, 8, 9]
}
COUPLINGS = [Fraction.from_float(x) for x in
             [0., .1, .3, .5, 1., 2., 3., 5., 10., 15., 20., 30.]]


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        while chunk := stream.read(1 << 20):
            digest.update(chunk)
    return digest.hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def uncomment(source):
    """Remove nested Lean comments, preserving line boundaries and strings."""
    output = []
    index = 0
    token = re.compile(r'/-|--|"')
    comment_token = re.compile(r"/-|-/")
    while index < len(source):
        match = token.search(source, index)
        if match is None:
            output.append(source[index:])
            break
        output.append(source[index:match.start()])
        start = match.start()
        index = match.end()
        if match[0] == "/-":
            depth = 1
            while depth:
                nested = comment_token.search(source, index)
                assert nested is not None, "Unterminated Lean block comment"
                depth += 1 if nested[0] == "/-" else -1
                index = nested.end()
            output.append(re.sub(r"[^\n]", " ", source[start:index]))
        elif match[0] == "--":
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            output.append(" " * (end - start))
            index = end
        else:
            while index < len(source):
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise AssertionError("Unterminated Lean string")
            assert index <= len(source), "Unterminated Lean string escape"
            output.append(source[start:index])
    return "".join(output)


def declarations(source):
    source = uncomment(source)
    stack = []
    result = []
    for raw in source.splitlines():
        line = raw.strip()
        match = re.fullmatch(r"namespace (\S+)", line)
        if match:
            stack.append(("namespace", match[1]))
            continue
        match = re.fullmatch(r"(?:noncomputable )?section(?: (\S+))?", line)
        if match:
            stack.append(("section", match[1]))
            continue
        match = re.fullmatch(r"end(?: (\S+))?", line)
        if match:
            assert stack, ("Unbalanced end", raw)
            kind, name = stack.pop()
            if match[1]:
                assert kind == "namespace" and name == match[1], raw
            continue
        match = re.match(r"theorem ([\w.]+)", line)
        if match:
            namespace = [name for kind, name in stack if kind == "namespace"]
            result.append(".".join(namespace + [match[1]]))
    assert not stack, stack
    assert len(result) == len(re.findall(r"^\s*theorem [\w.]+", source, re.M))
    return result


def imports(source):
    result = []
    for line in uncomment(source).splitlines():
        if line.strip().startswith("import "):
            pieces = line.strip().split()
            assert len(pieces) == 2, line
            result.append(pieces[1])
    return result


def declaration_types(source):
    """Read the frozen source statement, ending before its proof body."""
    source = uncomment(source)
    matches = list(re.finditer(r"^theorem ([\w.]+)", source, re.M))
    result = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(source)
        block = source[match.start():end]
        assert ":=" in block, match[1]
        result[match[1]] = re.sub(r"\s+", " ", block.split(":=", 1)[0]).strip()
    return result


def require_parts(text, *parts):
    for part in parts:
        assert re.sub(r"\s+", " ", part).strip() in text, (part, text)


def verify_exports(private):
    types = declaration_types((private / "NativeOriginalSampleResults.lean").read_text())
    expected = {
        "original_sample_guards_unit", "original_sample_stable_return",
        "original_sample_cyclic_return", "original_sample_has_limit_iff",
        "original_sample_stable_density_limit", "original_sample_sixty_tests_iff",
        "coupling_fifteen_finite_failure_with_limit", "original_sample_euclidean_norm",
        "original_sample_eventual_tests_iff", "coupling_fifteen_eventual_success",
        "original_sample_successful_prefix_iff",
    }
    assert set(types) == expected
    require_parts(types["original_sample_guards_unit"], "(i : Fin 12) (n : ℕ)",
                  "ActivePhase", "NativeLegal", "complexNormSq (orbit i n) = 1")
    require_parts(types["original_sample_stable_return"], "(i : Fin 12)",
                  "(hi : i.val < 10)", "Tendsto (orbit i) atTop (nhds (target i))")
    require_parts(types["original_sample_stable_density_limit"], "(hi : i.val < 10)",
                  "(j : Fin 8)", "Complex.normSq (orbit i n j)",
                  "Complex.normSq (target i j)")
    require_parts(types["original_sample_cyclic_return"], "(hi : 10 ≤ i.val)",
                  "g i a = c", "g i c = a", "c ≠ a", "complexNormSq a = 1",
                  "complexNormSq c = 1", "densityGap i", "orbit i (2*n)",
                  "orbit i (2*n+1)", "¬ ∃ l", "Complex.normSq (orbit i n 4)")
    require_parts(types["original_sample_has_limit_iff"], "Tendsto", "↔ i.val < 10")
    require_parts(types["original_sample_sixty_tests_iff"], "MeetsConvergence",
                  "(orbit i 59) (orbit i 60)", "↔ i.val < 9")
    require_parts(types["original_sample_eventual_tests_iff"], "∀ᶠ n in atTop",
                  "(orbit i n) (orbit i (n+1))", "↔ i.val < 10")
    require_parts(types["original_sample_successful_prefix_iff"], "∃ n : ℕ",
                  "n < 60", "(orbit i n) (orbit i (n+1))", "↔ i.val < 9")
    require_parts(types["coupling_fifteen_finite_failure_with_limit"],
                  "Tendsto (orbit 9)", "¬ MeetsConvergence", "(orbit 9 59) (orbit 9 60)")
    require_parts(types["original_sample_euclidean_norm"],
                  "(i : Fin 12) (n : ℕ)", "GroundComplexEuclidean.l2 (orbit i n) = 1")
    require_parts(types["coupling_fifteen_eventual_success"], "∀ᶠ n in atTop",
                  "(orbit 9 n) (orbit 9 (n+1))")
    # Source coverage is conditional on the sample index only. No hidden entry,
    # contraction, local-cycle, guard or certificate hypotheses may be exported.
    for text in types.values():
        assert not re.search(r"\b(?:hentry|hguards|certificate|budget|hreturn|hrows)\s*:", text), text
    interface = uncomment((private / "NativeOriginalSampleInterface.lean").read_text())
    vector = interface.split("def κ : Fin 12 → ℚ := ![", 1)[1].split("]", 1)[0]
    actual = [Fraction(part.strip().strip("()")) for part in vector.split(",")]
    assert actual == COUPLINGS
    require_parts(re.sub(r"\s+", " ", interface),
                  "nativeUpdate GroundNativeControls.originalTolerance b (κ i : ℝ) (1/2)",
                  "fun n => (g i)^[n] GroundOriginalSeed.initial",
                  "realEmbed (-(GroundOriginalContinuation.branch (κ i : ℝ)).1)")
    for k, gap in [(20, "1/4"), (30, "9/20")]:
        conditional = declaration_types((private / f"NativeCycle{k}RealOriginalReturn.lean").read_text())
        assert set(conditional) == {"real_even_odd_limits_of_entry", "limits_real_of_entry"}
        for text in conditional.values():
            require_parts(text, "(hentry :", "closedBall", "IsReal")
        result = declaration_types((private / f"NativeCycleSeed{k}RealReturn.lean").read_text())
        assert set(result) == {"original_seed_cycle_real"}
        text = result["original_seed_cycle_real"]
        require_parts(text, "theorem original_seed_cycle_real :", "IsReal z₀ ∧ IsReal z₁",
                      "g z₀ = z₁", "g z₁ = z₀", gap, "GroundOriginalSeed.initial",
                      "∀ n : ℕ, ActivePhase", "NativeLegal", "¬ ∃ l")
        assert "hentry" not in text
    return {"aggregate_declarations": 11, "sample_count": 12,
            "sixty_success_sample_indices": list(range(9)),
            "convergent_sample_indices": list(range(10)),
            "cyclic_sample_indices": [10, 11],
            "conditional_cycle_entry_premises_preserved": True,
            "unconditional_cycle_wrapper_entry_premises": False}


def verify_replay(private, replay_root, by_private):
    receipt = read_json(replay_root / "replay.json")
    status = read_json(replay_root / "status.json")
    frozen = read_json(replay_root / "replay-freeze.json")
    assert status["terminal_exit_code"] == 0 and status["samples"] == 10
    assert receipt["all_ten_samples"] and receipt["steps"] == 1070 and receipt["pairs"] == 535
    assert receipt["raw_seed_literal_checked"] and receipt["initial_mathematical_normalization_enclosed"]
    assert receipt["source_sha256"] == frozen and len(frozen) == 1831
    assert receipt["source_freeze_sha256"] == sha(replay_root / "replay-freeze.json")
    assert status["log_sha256"] == sha(replay_root / "replay_driver.txt")
    log = (replay_root / "replay_driver.txt").read_text()
    assert "Exact native transport replay passed: 10 samples; 1070 steps; 535 pairs." in log
    assert not re.search(r"Traceback|error:|warning:", log)
    for path, digest in frozen.items():
        assert sha(path) == digest, path
    assert len(receipt["samples"]) == 10
    assert {sample["sample"] for sample in receipt["samples"]} == set(SAMPLES)
    for sample in receipt["samples"]:
        tag = sample["sample"]
        index, count = SAMPLES[tag]
        assert sample["steps"] == count and sample["pairs"] == count // 2
        assert Fraction(sample["coupling"]) == COUPLINGS[index]
        assert sample["exact_arithmetic_replay"] and sample["read_only_leaf_render_match"]
        payload = (Path("/tmp") / f"de_native_cycle_seed_transport_{tag[5:]}.json"
                   if tag.startswith("cycle") else
                   Path("/tmp") / f"de-native-stable-seed-{tag[6:]}-transport.json")
        assert sha(payload) == sample["payload_sha256"]
        prefix = f"NativeCycleSeed{tag[5:]}" if tag.startswith("cycle") else f"NativeStableSeed{tag[6:]}"
        expected = {str(private / f"{prefix}Step{n:03d}.lean") for n in range(count)}
        assert set(sample["leaf_source_sha256"]) == expected
        for path, digest in sample["leaf_source_sha256"].items():
            assert sha(path) == digest
            assert by_private[Path(path).stem]["private_sha256"] == digest
    return {"samples": 10, "steps": 1070, "pairs": 535,
            "replay_receipt_sha256": sha(replay_root / "replay.json"),
            "revalidated_inputs": len(frozen),
            "scope": "Completed exact arithmetic replay tied to the same Lean leaf sources; no IEEE trace"}


def verify_sources(args):
    plans = [read_json(args.plan), read_json(args.supplement_plan)]
    assert plans[1]["parent_plan_sha256"] == sha(args.plan)
    mapping = {}
    rows = []
    sources = {}
    for plan, count, preview in zip(plans, COUNTS, [args.preview, args.supplement_preview]):
        assert plan["module_count"] == count[0] and plan["fresh_theorem_count"] == count[1]
        assert len(plan["modules"]) == count[0]
        names = [name for row in plan["modules"] for name in row["declared_theorems"]]
        assert len(names) == len(set(names)) == count[1]
        for row in plan["modules"]:
            assert row["private_module"] not in mapping
            mapping[row["private_module"]] = row["production_module"]
            rows.append(row)
            sources[row["production_module"]] = preview / row["production_path"]
    assert len(set(mapping.values())) == 1738
    by_name = {row["production_module"]: row for row in rows}
    by_private = {row["private_module"]: row for row in rows}
    names = [name for row in rows for name in row["declared_theorems"]]
    assert len(names) == len(set(names)) == 20634
    edges = {}
    outside = set()
    for row in rows:
        p = args.private / (row["private_module"] + ".lean")
        q = sources[row["production_module"]]
        assert sha(p) == row["private_sha256"] and sha(q) == row["production_sha256"], p
        source = p.read_text()
        qualified = q.read_text()
        translated = re.sub(r"^(\s*import )(\S+)",
                            lambda m: m[1] + mapping.get(m[2], m[2]), source, flags=re.M)
        assert translated == qualified, q
        assert declarations(source) == declarations(qualified) == row["declared_theorems"], p
        plain = uncomment(qualified)
        assert not re.search(r"\b(?:sorry|admit|native_decide)\b", plain), q
        assert not re.search(r"^\s*(?:axiom|constant)\s", plain, re.M), q
        dependencies = imports(qualified)
        assert not any((args.private / (d + ".lean")).exists() for d in dependencies), q
        edges[row["production_module"]] = [d for d in dependencies if d in by_name]
        outside.update(d for d in dependencies if d not in by_name)
        assert str(Path("lean") / Path(*row["production_module"].split(".")).with_suffix(".lean")) == row["production_path"]
    review = read_json(args.review)
    assert review["modules"] == 1734 and review["theorem_names"] == 20628
    assert review["plan_sha256"] == sha(args.plan)
    assert set(review["external_imports"]) == outside
    assert len(outside) == 23
    for name in outside:
        record = review["external_sources"][name]
        assert sha(record["path"]) == record["sha256"], name
    main_names = {r["production_module"] for r in plans[0]["modules"]}
    assert {n: ds for n, ds in edges.items() if n in main_names} == review["dependencies"]
    done = set()
    active = set()
    def visit(name):
        if name in done:
            return
        assert name not in active, ("Import cycle", name)
        active.add(name)
        for dependency in edges[name]:
            visit(dependency)
        active.remove(name)
        done.add(name)
    for name in by_name:
        visit(name)
    assert len(done) == 1738
    for plan, preview, suffix in zip(plans, [args.preview, args.supplement_preview],
                                    ["native_campaign", "native_seed_real_returns"]):
        ns = [n for r in plan["modules"] for n in r["declared_theorems"]]
        manifest = "".join("import " + r["production_module"] + "\n" for r in plan["modules"])
        manifest += "set_option warningAsError true\n"
        for stage, command in [("statements", "#check "), ("axioms", "#print axioms ")]:
            expected = manifest + "".join(command + n + "\n" for n in ns)
            assert (preview / "lean/manifests" / ("check_" + suffix + "_" + stage + ".lean")).read_text() == expected
    exports = verify_exports(args.private)
    replay = verify_replay(args.private, args.replay_root, by_private)
    return {"source_stage_passed": True, "module_count": 1738,
            "enumerated_theorem_count": 20634, "export_statement_coverage": exports,
            "exact_replay": replay, "parent_plan_sha256": sha(args.plan),
            "supplement_plan_sha256": sha(args.supplement_plan),
            "source_sha256": {str(p): sha(p) for p in sources.values()}}, plans


def axiom_entries(text, names):
    entries = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|(does not depend on any axioms))", text, re.S)
    assert [name for name, _, _ in entries] == names
    assert all(set(raw.replace("\n", " ").replace(",", " ").split()) <= STANDARD_AXIOMS
               for _, raw, _ in entries)


def statement_entries(text, names):
    matches = list(re.finditer(r"^([\w.]+)(?=\s|:|\()", text, re.M))
    assert [m[1] for m in matches] == names
    return {m[1]: text[m.start():matches[i + 1].start() if i + 1 < len(matches) else len(text)]
            for i, m in enumerate(matches)}


def verify_qualified(args, plans):
    packets = [
        (args.qualified_summary, args.qualified_receipts, args.qualified_objects,
         Path("/tmp/de-native-campaign-qualified-stream-freeze.json"),
         Path("/tmp/de-native-campaign-qualified-stream-driver.log"),
         "All1734 qualified modules and20628 fresh statement/axiom checks passed; replay, repository integration and commit pending"),
        (args.supplement_summary, args.supplement_receipts, args.supplement_objects,
         Path("/tmp/de-native-seed-real-returns-qualified-stream-freeze.json"),
         Path("/tmp/de-native-seed-real-returns-qualified-stream-driver.log"),
         "All four supplemental qualified modules and six statement/axiom checks passed; repository integration pending"),
    ]
    all_types = {}
    for plan, count, packet in zip(plans, COUNTS, packets):
        summaryp, receipts, objects, freeze_path, driver_log, marker = packet
        assert summaryp.exists(), "Required qualified gate is still pending: " + str(summaryp)
        summary = read_json(summaryp)
        assert summary["terminal_exit_code"] == 0 and summary["standard_only"]
        assert summary["module_count"] == count[0]
        assert summary["fresh_statement_count"] == summary["fresh_axiom_count"] == count[1]
        assert summary["source_freeze_sha256"] == sha(freeze_path)
        frozen = read_json(freeze_path)
        for path, digest in frozen.items():
            assert sha(path) == digest, path
        text = driver_log.read_text()
        assert marker in text and not re.search(r"terminal [1-9]|Traceback|exception ", text)
        rows = {r["production_module"]: r for r in plan["modules"]}
        records = read_json(receipts / "modules.json")
        assert len(records) == len(rows) == count[0]
        assert {r["module"] for r in records} == set(rows)
        for record in records:
            row = rows[record["module"]]
            assert record["terminal_exit_code"] == 0
            assert record["source_sha256"] == row["production_sha256"]
            log = receipts / (row["private_module"] + ".log")
            assert sha(log) == record["log_sha256"]
            assert not re.search(r"error:|warning:", log.read_text())
            obj = objects / Path(*record["module"].split(".")).with_suffix(".olean")
            assert sha(obj) == record["olean_sha256"], obj
            assert read_json(receipts / (row["private_module"] + "-terminal.json")) == record
        names = [n for r in plan["modules"] for n in r["declared_theorems"]]
        statement_log = (receipts / "statements.log").read_text()
        axiom_log = (receipts / "axioms.log").read_text()
        assert not re.search(r"error:|warning:", statement_log + axiom_log)
        all_types.update(statement_entries(statement_log, names))
        axiom_entries(axiom_log, names)
    parent = read_json(args.qualified_summary)
    assert parent["original_private_aggregate_gate_passed"]
    private_gate_path = Path("/tmp/de-native-original-sample-results-audit-summary.json")
    private_gate = read_json(private_gate_path)
    assert private_gate["terminal_exit_code"] == 0 and private_gate["standard_only"]
    assert len(private_gate["names"]) == 11
    assert parent["original_private_aggregate_summary_sha256"] == sha(private_gate_path)
    supplement = read_json(args.supplement_summary)
    assert parent["plan_sha256"] == sha(args.plan)
    assert supplement["plan_sha256"] == sha(args.supplement_plan)
    assert supplement["parent_summary_sha256"] == sha(args.qualified_summary)
    assert supplement["parent_module_receipts_sha256"] == sha(args.qualified_receipts / "modules.json")
    assert supplement["seed_summary_sha256"] == sha("/tmp/de-native-seed-real-returns-summary.json")
    aggregate = "SbtCosmo.Derivation.NativeOriginalSampleResults."
    for name, parts in {
        "original_sample_sixty_tests_iff": ["Fin 12", "↔", "< 9", "59", "60"],
        "original_sample_has_limit_iff": ["Fin 12", "↔", "< 10", "Tendsto"],
        "original_sample_eventual_tests_iff": ["Fin 12", "↔", "< 10", "∀ᶠ"],
        "original_sample_successful_prefix_iff": ["Fin 12", "↔", "< 9", "< 60", "∃"],
    }.items():
        statement = re.sub(r"\s+", " ", all_types[aggregate + name])
        require_parts(statement, *parts)
        assert not re.search(r"\b(?:hentry|hguards|certificate|budget|hrows)\s*:", statement)
    return {"qualified_stage_passed": True, "standard_only": True,
            "fresh_modules": 1738, "fresh_statement_checks": 20634,
            "fresh_axiom_checks": 20634,
            "parent_summary_sha256": sha(args.qualified_summary),
            "supplement_summary_sha256": sha(args.supplement_summary)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=["source", "qualified"], required=True)
    defaults = {
        "plan": "/tmp/de-native-campaign-production-plan.json",
        "supplement-plan": "/tmp/de-native-seed-real-returns-production-plan.json",
        "review": "/tmp/de-native-campaign-integration-review.json",
        "private": "/tmp/de_native_cycle_lean",
        "preview": "/tmp/de_native_campaign_production_preview",
        "supplement-preview": "/tmp/de_native_seed_real_returns_preview",
        "replay-root": str(ROOT / "results/native_sample_transport_2026-10-04"),
        "qualified-summary": "/tmp/de-native-campaign-qualified-stream-summary.json",
        "qualified-receipts": "/tmp/de_native_campaign_qualified_stream_receipts",
        "qualified-objects": "/tmp/de_native_campaign_qualified_stream_objects",
        "supplement-summary": "/tmp/de-native-seed-real-returns-qualified-stream-summary.json",
        "supplement-receipts": "/tmp/de_native_seed_real_returns_qualified_stream_receipts",
        "supplement-objects": "/tmp/de_native_seed_real_returns_qualified_stream_objects",
    }
    for name, default in defaults.items():
        parser.add_argument("--" + name, type=Path, default=Path(default))
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists(), args.output
    result, plans = verify_sources(args)
    result["qualified_stage_passed"] = False
    if args.stage == "qualified":
        result.update(verify_qualified(args, plans))
    result.update({"stage": args.stage, "verifier_sha256": sha(__file__),
                   "repository_integrated": False, "IEEE_operation_certificate": False,
                   "original_paper_restoration_complete": False,
                   "review": "Adversarial self-review; no independent reviewer"})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print("Native campaign", args.stage, "verification passed:", result["module_count"],
          "modules;", result["enumerated_theorem_count"], "source declarations.")
    if args.stage == "source":
        print("Qualified compilation/audits and repository integration remain separate pending gates.")


if __name__ == "__main__":
    main()
