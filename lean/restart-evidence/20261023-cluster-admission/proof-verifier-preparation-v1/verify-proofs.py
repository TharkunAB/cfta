"""Check saved cluster-admission evidence without running Lean or Lake."""
import argparse
import difflib
import hashlib
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--root", required=True, type=Path)
parser.add_argument("--live", action="store_true")
args = parser.parse_args()
root = args.root.resolve()
evidence = root / "lean/restart-evidence/20261023-cluster-admission"
def digest(data):
    return hashlib.sha256(data).hexdigest()
def read(relative):
    path = Path(relative)
    assert not path.is_absolute() and ".." not in path.parts
    return (evidence / path).read_bytes()
def load(relative):
    return json.loads(read(relative))
def pinned(record):
    data = read(record["path"])
    assert len(data) == record["bytes"] and digest(data) == record["sha256"], record["path"]
    return data
def canonical(text):
    return re.sub(r"[ \t\r\n]+", " ", text).strip(" \t\r\n")
raw_data = read("bound-data.json")
assert digest(raw_data) == "b3aacbf63eb1a9f4e8c974af919be30ba7df588a923930515484aef60b548c19"
assert not re.search(r"__H\d+_", raw_data.decode()), "Unbound evidence input"
bound = json.loads(raw_data)
modules = bound["modules"]
assert [m["key"] for m in modules] == ["execution", "boundary", "outer"]
assert [m["source_cap"] for m in modules] == [130, 230, 230]
assert [len(m["specs"]) for m in modules] == [3, 1, 2]
by_name = {m["name"]: m for m in modules}
jobs = json.loads(pinned(bound["job_history"]))
actual = set()
for path in evidence.glob("*.json"):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and "wrapper" in item and "exit_code" in item:
        if Path(item.get("command", [""])[0]).name in {"lean", "lake"}:
            actual.add(path.stem)
assert actual == set(jobs)
metrics = bound["metrics"]
assert metrics["actual_jobs"] == len(actual)
assert metrics["source_jobs"] == sum(j["kind"] in {"strict", "full"} for j in jobs.values())
assert metrics["focused_build_jobs"] == sum(j["kind"] == "focused_build" for j in jobs.values())
assert metrics["audit_jobs"] == sum(j["kind"] == "audit" for j in jobs.values()) == 1
assert metrics["actual_jobs"] == sum(metrics[k] for k in ["source_jobs", "focused_build_jobs", "audit_jobs"])
assert metrics["failed_jobs"] == sum(j["exit_code"] != 0 for j in jobs.values())
assert metrics["warned_source_exit_zero_jobs"] == sum(j["kind"] in {"strict", "full"} and j["exit_code"] == 0 and bool(j["source_warnings"]) for j in jobs.values())
for stem, job in jobs.items():
    receipt = load(stem + ".json")
    assert receipt["exit_code"] == job["exit_code"] and receipt["observed_at"]
    assert receipt["log"] == stem + ".log" and receipt["limits"] == stem + ".limits.json"
    raw = read(receipt["log"])
    assert re.fullmatch(r"[0-9a-f]{64}", job["log_sha256"]) and digest(raw) == job["log_sha256"]
    assert load(receipt["limits"]) == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    usage = load(stem + ".usage.json")
    assert 0 <= usage["age_seconds"] <= 600 and usage["remaining_percent"] > 1
    assert receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
    assert job["kind"] in {"strict", "full", "focused_build", "audit"}
    if job["kind"] in {"strict", "full"}:
        assert job["module"] in by_name and re.fullmatch(r"[0-9a-f]{64}", job["source_sha256"])
        assert receipt["source"] == stem + ".source.lean" and receipt["sha256"] == job["source_sha256"]
        source = read(receipt["source"])
        assert digest(source) == job["source_sha256"]
        assert len(receipt["command"]) == 3 and Path(receipt["command"][0]).name == "lean"
        assert receipt["command"][1] == "-Dlinter.all=true" and Path(receipt["command"][-1]).resolve() == (evidence / receipt["source"]).resolve()
        assert len(re.findall(r"^.+?:\d+:\d+: error(?:\([^)]*\))?:", raw.decode(), re.M)) == job["errors"]
        assert len(re.findall(r"^.+?:\d+:\d+: warning(?:\([^)]*\))?:", raw.decode(), re.M)) == job["source_warnings"]
        if job["kind"] == "strict":
            assert not re.search(r"^\s*set_option (?:maxHeartbeats|maxRecDepth|linter\.)", source.decode(), re.M)
    else:
        assert job["source_sha256"] is None and "source" not in receipt and "sha256" not in receipt
        target = "MicroCFTA.Audit" if job["kind"] == "audit" else "MicroCFTA." + job["module"]
        assert len(receipt["command"]) == 5 and Path(receipt["command"][0]).name == "lake"
        assert receipt["command"][1:] == ["-d", str(root / "lean"), "build", target]
        assert receipt["exit_code"] == 0 and not re.search(r"\berror(?:\([^)]*\))?:", raw.decode())
        build = re.search(r"Build completed successfully \((\d+) jobs\)\.", raw.decode())
        expected = bound["audit"] if job["kind"] == "audit" else bound["focused_builds"][stem]
        assert build and int(build.group(1)) == expected["build_jobs"]
        assert re.findall(r"(?m)^warning: .+$", raw.decode()) == expected["warnings"]
        assert all("InternedFreshOrdinaryClosedCompletion.lean:24:5:" in warning for warning in expected["warnings"])
        assert job["module"] is None if job["kind"] == "audit" else job["module"] in by_name
history = json.loads(pinned(bound["history"]))
assert history["status"] == "ROOT_ACCEPTED"
assert set(history) == {"status", "selected_sources", "variants", "artifacts", "patches", "rejected_public_types"}
assert history["selected_sources"] == {m["source_path"]: m["source_sha256"] for m in modules}
variants = {v["path"]: v for v in history["variants"]}
artifacts = {a["path"]: a for a in history["artifacts"]}
assert variants and len(variants) == len(history["variants"]) and len(artifacts) == len(history["artifacts"])
assert not set(variants) & set(artifacts)
for path, record in {**artifacts, **variants}.items():
    data = read(path)
    assert re.fullmatch(r"[0-9a-f]{64}", record["sha256"]) and digest(data) == record["sha256"]
    if path in variants:
        assert record["module"] in by_name and record["reason"].strip()
        assert 0 < len(data.splitlines()) == record["lines"] <= by_name[record["module"]]["source_cap"]
    else:
        assert len(data) == record["bytes"]
for stem, job in jobs.items():
    assert all(stem + suffix in artifacts for suffix in [".json", ".log", ".limits.json", ".usage.json"])
    if job["kind"] == "strict":
        assert any(v["module"] == job["module"] and v["sha256"] == job["source_sha256"] and read(path) == read(stem + ".source.lean") for path, v in variants.items())
    elif job["kind"] == "full":
        assert stem + ".source.lean" in artifacts, "Printers are artifacts, not bounded math variants"
for patch in history["patches"]:
    assert patch["reason"].strip() and patch["before"] in variants and patch["after"] in variants
    assert patch["module"] == variants[patch["before"]]["module"] == variants[patch["after"]]["module"]
    assert patch["path"] in artifacts and artifacts[patch["path"]]["sha256"] == patch["sha256"]
    before, after = [read(patch[key]).decode() for key in ["before", "after"]]
    expected = "".join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile=patch["fromfile"], tofile=patch["tofile"]))
    assert read(patch["path"]).decode() == expected
rejected = {r["stem"]: r for r in history["rejected_public_types"]}
assert len(rejected) == len(history["rejected_public_types"]) == metrics["rejected_public_type_jobs"]
for stem, record in rejected.items():
    assert stem in jobs and jobs[stem]["kind"] == "full" and jobs[stem]["exit_code"] == 0
    assert record["raw_sha256"] == jobs[stem]["log_sha256"] and record["reason"].strip()
    assert record["artifacts"] and all(path in artifacts for path in record["artifacts"])
cut = json.loads(pinned(bound["metadata_cut"]))
metadata_jobs = cut["jobs"]
assert cut["status"] == "COMPLETE_TERMINAL_METADATA_CUT_BEFORE_CLOSING_TOOLS"
assert [p for p, code in metadata_jobs.items() if code != 0] == bound["metadata_failure_paths"]
assert cut["failed_jobs"] == sum(code != 0 for code in metadata_jobs.values())
for relative, code in metadata_jobs.items():
    assert relative.startswith("root-metadata-history/") and relative.endswith(".json") and relative in artifacts
    assert type(code) is int
    receipt = load(relative)
    assert receipt["exit_code"] == code and receipt["observed_at"] and Path(receipt["command"][0]).name not in {"lean", "lake"}
    assert all(relative[:-5] + suffix in artifacts for suffix in [".json", ".log", ".limits.json", ".usage.json", ".source.py", ".peaks.txt"])
    assert load(relative[:-5] + ".limits.json") == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    usage = load(relative[:-5] + ".usage.json")
    assert 0 <= usage["age_seconds"] <= 600 and usage["remaining_percent"] > 1
selection = json.loads(pinned(bound["selection"]))
assert selection == {m["source_path"]: dict(sha256=m["source_sha256"], lines=m["source_lines"], strict=m["strict"], full=m["full"]) for m in modules}
assert json.loads(pinned(bound["frozen_modules"])) == {m["name"]: m["source_sha256"] for m in modules}
full_variant_keys = []
for m in modules:
    name, namespace = m["name"], "MicroCFTA." + m["name"] + "."
    specs = m["specs"]
    shorts = [short for short, kind in specs]
    source = read(m["snapshot"])
    assert re.fullmatch(r"[0-9a-f]{64}", m["source_sha256"]) and digest(source) == m["source_sha256"]
    assert source == read(m["strict"] + ".source.lean") and 0 < len(source.splitlines()) == m["source_lines"] <= m["source_cap"]
    assert read(m["strict"] + ".log") == b"" and jobs[m["strict"]]["kind"] == "strict"
    assert jobs[m["strict"]]["module"] == name and jobs[m["strict"]]["exit_code"] == 0
    assert jobs[m["full"]]["kind"] == "full" and jobs[m["full"]]["module"] == name and jobs[m["full"]]["exit_code"] == 0
    assert jobs[m["strict"]]["errors"] == jobs[m["strict"]]["source_warnings"] == jobs[m["full"]]["errors"] == jobs[m["full"]]["source_warnings"] == 0
    assert m["full"] not in rejected and source.rstrip().endswith(("end MicroCFTA." + name).encode())
    assert any(v["module"] == name and read(path) == source for path, v in variants.items())
    gate = json.loads(pinned(m["selected_gate"]))
    assert gate["status"] == "ACCEPTED_STRICT_SOURCE" and gate["source_sha256"] == m["source_sha256"]
    assert gate["source_lines"] == m["source_lines"] and gate["source_cap"] == m["source_cap"]
    assert gate["selected_strict"] == m["strict"] and gate["strict_log_bytes"] == 0 and gate["public_heads"] == shorts
    assert gate["receipt_sha256"] == digest(read(m["strict"] + ".json"))
    assert gate["declaration_gate"] == m["declaration_gate"]["path"] and gate["body_gate"] == m["body_gate"]["path"]
    body_gate = json.loads(pinned(m["body_gate"]))
    assert body_gate["source_sha256"] == m["source_sha256"]
    assert body_gate[m["body_review_field"]] == m["body_review"]["sha256"]
    assert json.loads(pinned(m["body_review"]))["status"] == "CLEAR"
    declaration = json.loads(pinned(m["declaration_gate"]))
    assert declaration["status"] == "ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY" and declaration["module"] == name
    assert declaration["public_heads"] == shorts and declaration["contracts_sha256"] == m["manifest"]["sha256"]
    assert declaration["whole_source_hard_stop"] == m["source_cap"] and declaration["default_declaration_limits"] and declaration["all_linters"]
    manifest = json.loads(pinned(m["manifest"]))
    schema = json.loads(pinned(m["schema"]))
    fragments = m["fragments"]
    assert list(manifest) == [f["file"] for f in fragments] and [f["order"] for f in fragments] == list(range(1, len(fragments) + 1))
    if "layout" in m:
        layout = json.loads(pinned(m["layout"]))["compiled_fragments"]
        assert [{k: v for k, v in f.items() if k not in {"owner", "path"}} for f in fragments] == [{k: v for k, v in f.items() if k != "owner"} for f in layout]
    data = {}
    for f in fragments:
        raw_fragment = read(f["path"])
        assert digest(raw_fragment) == f["sha256"] and len(raw_fragment.splitlines()) == f["lines"]
        assert manifest[f["file"]] == (dict(lines=f["lines"], sha256=f["sha256"]) if m["key"] == "execution" else f["sha256"])
        data[f["file"]] = raw_fragment
    assert source.startswith(data["context.lean.txt"]) and source.count(data["context.lean.txt"]) == 1
    bodies, positions = {}, {}
    for i, short in enumerate(shorts):
        header = data[m["headers"][short]].rstrip(b"\n") + b" := by\n"
        assert source.count(header) == 1 and source.index(header) >= len(data["context.lean.txt"])
        positions[short] = (source.index(header), source.index(header) + len(header))
    assert [positions[s][0] for s in shorts] == sorted(positions[s][0] for s in shorts)
    for i, short in enumerate(shorts):
        end = positions[shorts[i + 1]][0] if i + 1 < len(shorts) else source.rindex(("end MicroCFTA." + name).encode())
        bodies[short] = source[positions[short][1]:end]
    matched = []
    for f in fragments:
        fragment = data[f["file"]]
        if f["role"] == "context":
            matched.append(0)
            continue
        if "future_body_attachment" in f:
            fragment = fragment.rstrip(b"\n") + f["future_body_attachment"].encode()
        scope = source if f["role"] == "public-header" else bodies[f["owner"]]
        assert scope.count(fragment) == 1, f["file"]
        matched.append(scope.index(fragment) + (0 if f["role"] == "public-header" else positions[f["owner"]][1]))
    assert matched == sorted(matched) and len(set(matched)) == len(matched)
    for short, body in bodies.items():
        expected = m["bodies"][short]
        assert re.findall(rb"\bhave[ \t]+([^ \t:\n]+)", body) == [n.encode() for n in expected["have_names"]]
        assert len(re.findall(rb"\bhave\b", body)) == len(expected["have_names"])
        assert re.findall(rb"\blet[ \t]+([^ \t:=\n]+)", body) == [n.encode() for n in expected["let_names"]]
        assert len(re.findall(rb"\blet\b", body)) == len(expected["let_names"])
        assert re.findall(rb"\bby_cases[ \t]+([^ \t:\n]+)", body) == [n.encode() for n in expected["by_cases_names"]]
        assert re.findall(rb"\bcases[ \t]+([^ \t:\n]+)[ \t]*:", body) == [n.encode() for n in expected["case_equations"]]
        groups = [[n.strip().decode() for n in g.split(b",")] for g in re.findall(rb"(?s)\bobtain[ \t]+\xe2\x9f\xa8(.*?)\xe2\x9f\xa9[ \t\r\n]*:=", body)]
        assert groups == expected["obtain_groups"] and len(re.findall(rb"\bobtain\b", body)) == len(groups)
        assert re.findall(rb"(?m)^\s*(induction .+? with)\s*$", body) == [n.encode() for n in expected["inductions"]]
        assert len(re.findall(rb"\binduction\b", body)) == len(expected["inductions"])
        assert not re.search(rb"\b(?:show|suffices|haveI|letI)\b", body) and not re.search(rb"\bobtain\b(?:(?!:=).)*:(?!=)", body, re.S)
    assert schema["private_helpers"] == schema["global_definitions"] == schema["typed_show_fragments"] == []
    for record in m["review_only"]:
        reviewed = pinned(record)
        if record["path"].endswith("ih-schema.lean.txt"):
            assert reviewed not in source, "Generated IH schemas are review-only"
    public = re.findall(r"(?m)^\s*(?:(?:noncomputable|unsafe|partial)\s+)?(def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", source.decode())
    assert public == [(kind, short) for short, kind in specs]
    helpers = []
    for line in source.decode().splitlines():
        if re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\b", line):
            found = re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\s+(?:(?:noncomputable|unsafe|partial)\s+)?(?:def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", line)
            assert found, line
            helpers.append(found.group(1))
    assert helpers == schema["private_helpers"] == []
    if args.live:
        assert (root / m["source_path"]).read_bytes() == source
    tool_gate = json.loads(pinned(m["tool_gate"]))
    assert tool_gate["status"] == "ACCEPTED_EXACT_TOOLS_FOR_SELECTED_STRICT_SOURCE" and tool_gate["source_sha256"] == m["source_sha256"]
    assert tool_gate["public_heads"] == shorts and tool_gate["materializer_activation"] and tool_gate["sole_FULL_activation"] and tool_gate["reader_activation_after_actual_FULL"]
    for tool in ["reader", "materializer"]:
        active, archived = m[tool + "_active"], m[tool + "_archived"]
        assert pinned(active) == pinned(archived) and tool_gate["installed_tools"][active["path"]] == active["sha256"]
    report = json.loads(pinned(m["readback"]))
    printer, raw = read(m["full"] + ".source.lean"), read(m["full"] + ".log")
    options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
    tail = "\n" + "".join("set_option " + option + "\n" for option in options)
    for short, kind in specs:
        tail += "".join(d + namespace + short + "\n" for d in ["#check @", "#print ", "#print axioms "])
    assert printer == source + tail.encode() and len(tail.splitlines()) == 11 + 3 * len(specs)
    assert len(printer.splitlines()) == m["source_lines"] + len(tail.splitlines()) == tool_gate["diagnostic_tail_lines"] + m["source_lines"]
    assert all(printer.decode().splitlines().count("set_option " + option) == 1 for option in options)
    assert all(printer.decode().splitlines().count(d + namespace + short) == 1 for short, kind in specs for d in ["#check @", "#print ", "#print axioms "])
    for stem, job in jobs.items():
        if job["kind"] == "full" and job["module"] == name:
            matching = [v for path, v in variants.items() if v["module"] == name and read(stem + ".source.lean") == read(path) + tail.encode()]
            assert len(matching) == 1
            full_variant_keys.append((name, matching[0]["sha256"]))
    assert (report["source_sha256"], report["source_lines"], report["printer_sha256"]) == (m["source_sha256"], m["source_lines"], digest(printer))
    assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw)
    assert report["receipt_sha256"] == digest(read(m["full"] + ".json")) and report["owned_public_job_exit"] == 0
    assert all(report[k] for k in ["all_eight_printer_settings", "exact_module_and_diagnostic_tail", "diagnostic_limits_after_module_only", "no_omissions"])
    assert (report["pp_option_count"], report["linter_option_count"], report["diagnostic_limit_count"]) == (7, 1, 2)
    assert report["configured_paths"] == {k: str(path.resolve()) for k, path in dict(source=evidence / m["snapshot"], printer=evidence / (m["full"] + ".source.lean"), raw=evidence / (m["full"] + ".log"), receipt=evidence / (m["full"] + ".json")).items()}
    assert [(h["head"], h["kind"]) for h in report["heads"]] == [(namespace + short, kind) for short, kind in specs]
    log, starts = raw.decode(), []
    assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
    for short, kind in specs:
        pattern = re.escape(namespace + short) + r"(?:\.\{[^}\n]*\})?"
        matches = list(re.finditer(r"^(?:@)?" + pattern + r" :", log, re.M))
        assert len(matches) == 1, short
        starts.append(matches[0])
    assert starts == sorted(starts, key=lambda match: match.start()) and not log[:starts[0].start()].strip()
    actual_axioms, retained_names, reconstructed = {}, [], [log[:starts[0].start()]]
    for i, (short, kind) in enumerate(specs):
        head = namespace + short
        segment = log[starts[i].end():starts[i + 1].start() if i + 1 < len(starts) else len(log)]
        pattern = re.escape(head) + r"(?:\.\{[^}\n]*\})?"
        delimiters = list(re.finditer(r"\n" + kind + " " + pattern + r" :", segment))
        assert len(delimiters) == 1, short
        checked, printed = segment[:delimiters[0].start()], segment[delimiters[0].end():]
        axiom_matches = list(re.finditer(r"^'" + re.escape(head) + r"' (depends on axioms:|does not depend on any axioms)", printed, re.M))
        assert len(axiom_matches) == 1, short
        axiom = axiom_matches[0]
        declaration, axiom_output = printed[:axiom.start()], printed[axiom.start():]
        normalized, matches = canonical(checked), []
        for match in re.finditer(r" :=\n", declaration):
            prefix = canonical(declaration[:match.start()])
            if prefix == normalized:
                matches.append(match)
            elif len(prefix) > len(normalized):
                break
        assert len(matches) == 1, short
        declared, body = declaration[:matches[0].start()], declaration[matches[0].end():]
        reconstructed += [starts[i].group(0), checked, delimiters[0].group(0), declared, matches[0].group(0), body, axiom_output]
        metric, head_report = m["head_metrics"][short], report["heads"][i]
        raw_identity = checked.encode() == declared.encode()
        assert normalized == canonical(declared) and raw_identity is metric["raw_type_byte_identity"]
        assert len(checked.encode()) == metric["type_bytes"] and len(checked) == metric["type_characters"] and digest(checked.encode()) == metric["type_sha256"]
        assert len(checked.splitlines()) == metric["type_logical_lines"] and checked.count("\n") == metric["type_line_feeds"] and checked.endswith("\n") == metric["type_final_newline"]
        assert len(declared.encode()) == metric["printed_type_bytes"] and digest(declared.encode()) == metric["printed_type_sha256"]
        assert digest(normalized.encode()) == metric["canonical_type_sha256"]
        assert not any(token in checked + declared for token in ["_private", "✝", "†", "‡"])
        assert not any(re.search(re.escape(namespace + helper) + r"(?![\w'])", checked + declared) for helper in helpers)
        assert all(head_report[k] for k in ["check_print_type_identity", "check_print_type_lexical_identity", "unique_complete_type_body_delimiter", "actual_axioms_within_standard_allowed"])
        assert head_report["check_print_type_byte_identity"] is raw_identity
        assert head_report["private_namespace_helpers_checked"] == helpers and head_report["private_type_spellings_checked"] == ["_private", "✝", "†", "‡"] and head_report["private_public_type_names"] is False
        assert head_report["checked_type_characters"] == len(checked) and head_report["checked_type_bytes"] == len(checked.encode()) and head_report["checked_type_sha256"] == metric["type_sha256"]
        assert head_report["printed_type_bytes"] == metric["printed_type_bytes"] and head_report["printed_type_characters"] == len(declared) and head_report["printed_type_sha256"] == metric["printed_type_sha256"]
        assert head_report["normalized_type_characters"] == len(normalized) and head_report["canonical_type_sha256"] == metric["canonical_type_sha256"]
        assert head_report["body_characters"] == len(body) == metric["body_characters"] and len(body.encode()) == metric["body_bytes"]
        assert body.startswith("fun ") and len(body) > 50 and digest(body.encode()) == metric["body_sha256"]
        values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
        assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
        axioms = sorted({re.sub(r"\.\{[^}]*\}", "", value.strip()) for value in values.group(1).split(",") if value.strip()}) if values else []
        assert axioms == head_report["actual_axioms"] == metric["actual_axioms"] and set(axioms) <= {"Classical.choice", "Quot.sound", "propext"}
        assert head_report["actual_standard_three_axioms"] == (set(axioms) == {"Classical.choice", "Quot.sound", "propext"})
        actual_axioms[short] = axioms
        for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
            filename = m["prefix"] + "-" + short + "-" + suffix + ".txt"
            retained = read("public-readback/" + filename)
            assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
            retained_names.append(filename)
    assert "".join(reconstructed) == log and set(report["retained_slices"]) == set(retained_names)
    review = json.loads(pinned(m["root_full"]))
    independent = json.loads(pinned(m["type_review"]))
    assert review["status"] == "ACCEPTED_COMPLETE_PUBLIC_TYPES_AND_INSTALLED" and review["source_sha256"] == m["source_sha256"] and review["source_lines"] == m["source_lines"]
    assert review["root_manual_complete_TYPEs"] is True and review["goal_status"] == "ACTIVE_INCOMPLETE"
    assert review["readback_sha256"] == m["readback"]["sha256"]
    assert review["independent_complete_TYPE_review_sha256"] == m["type_review"]["sha256"] and independent["status"] == "CLEAR"
    assert set(review["TYPEs"]) == set(shorts)
    for short in shorts:
        metric = m["head_metrics"][short]
        assert review["TYPEs"][short] == dict(sha256=metric["type_sha256"], bytes=metric["type_bytes"], logical_lines=metric["type_logical_lines"], actual_axioms=actual_axioms[short])
    if m["key"] == "execution":
        assert independent["source_sha256"] == m["source_sha256"] and independent["source_lines"] == m["source_lines"]
        assert independent["public_heads"] == [namespace + short for short in shorts]
        assert independent["complete_checked_TYPEs_manually_read"] == independent["printed_TYPE_byte_comparisons"] == len(specs)
        assert independent["all_twelve_slice_hashes_verified"] and independent["entire_raw_byte_reconstruction_verified"]
        assert independent["all_raw_TYPE_byte_identity"] == all(v["raw_type_byte_identity"] for v in m["head_metrics"].values())
        assert independent["all_lexical_TYPE_identity"] and independent["all_private_type_markers_absent"] and independent["actual_private_helpers"] == helpers
        assert independent["actual_axioms_by_head"] == {namespace + short: actual_axioms[short] for short in shorts}
        assert independent["separate_manual_printed_TYPE_read_claimed"] is independent["whole_BODY_manual_read_claimed"] is independent["reviewer_math_author"] is False
    else:
        assert independent["ownership"]["reviewer_math_author"] is False
        manual = independent["manual_read_scope"]
        if m["key"] == "boundary":
            assert manual["complete_checked_TYPE"] is True and independent["public_head"] == namespace + shorts[0]
            assert manual["logical_lines"] == m["head_metrics"][shorts[0]]["type_logical_lines"]
            assert manual["printed_TYPE"] == "Programmatic raw byte identity; no separate complete manual read claimed."
            assert manual["BODY"] == "Complete retention and raw reconstruction programmatic only; no whole manual read."
        else:
            assert manual["both_complete_checked_TYPEs"] is True and independent["public_heads"] == [namespace + short for short in shorts]
            assert manual["printed_TYPEs"] == "Programmatic raw byte identity; no separate full manual printed-TYPE read claimed."
            assert manual["BODYs"] == "Complete retention and raw reconstruction programmatic only; no whole manual BODY read."
        for short in shorts:
            metric = m["head_metrics"][short]
            item = independent["metrics"] if m["key"] == "boundary" else independent["metrics"][short]
            assert item["checked_type"] == dict(logical_lines=metric["type_logical_lines"], LF=metric["type_line_feeds"], final_LF=metric["type_final_newline"], characters=metric["type_characters"], bytes=metric["type_bytes"], sha256=metric["type_sha256"])
            assert item["printed_type"] == dict(bytes=metric["printed_type_bytes"], sha256=metric["printed_type_sha256"])
            assert item["actual_raw_byte_identity"] is metric["raw_type_byte_identity"] and item["lexical_identity"] is True
            assert item["canonical_sha256"] == metric["canonical_type_sha256"] and item["axioms"]["actual"] == actual_axioms[short]
            assert item["body"] == dict(characters=metric["body_characters"], bytes=metric["body_bytes"], sha256=metric["body_sha256"])
        assert review["no_future_Room_or_result_oracle"] is True
    if m["key"] == "outer":
        assert review["producer_derives_actual_completion"] is review["adapter_retains_supplied_fuel_kept_and_full_after"] is True
assert len(full_variant_keys) == len(set(full_variant_keys)), "FULL repeated on an unchanged module variant"
dependency = json.loads(pinned(bound["dependency_gate"]))
assert dependency["status"] == "ACCEPTED_BOUNDARY_READY_FOR_OUTER_STRICT" and dependency["compiler_activation_authorized"] is True
assert dependency["boundary_source_sha256"] == modules[1]["source_sha256"] and dependency["outer_source_sha256"] == modules[2]["source_sha256"]
assert dependency["boundary_full_review_sha256"] == modules[1]["root_full"]["sha256"]
assert dependency["boundary_build_receipt_sha256"] == digest(read("boundary-build1.json")) and dependency["outer_body_gate_sha256"] == modules[2]["body_gate"]["sha256"]
assert load("original-source-index.json")["sources"] == [bound["original_audit"]]
original = read(bound["original_audit"]["snapshot"])
assert digest(original) == bound["original_audit"]["sha256"] and len(original.splitlines()) == bound["original_audit"]["lines"]
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
for m in modules:
    addition = ("import MicroCFTA." + m["name"] + "\n").encode()
    assert audit_source.count(addition) == 1 and audit_source.index(addition) < audit_source.index(b"/-!")
    audit_source = audit_source.replace(addition, b"", 1)
assert audit_source == original
audit_stem = bound["audit"]["stem"]
assert jobs[audit_stem]["kind"] == "audit" and jobs[audit_stem]["exit_code"] == 0
raw_audit = read(audit_stem + ".log")
assert digest(raw_audit) == bound["audit"]["log_sha256"]
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", raw_audit.decode())
assert dependencies and int(dependencies.group(1)) == bound["audit"]["dependencies"]
print(json.dumps(dict(status="PASS", live=args.live, **metrics, new_lean_lake_jobs=0, selected_modules=len(modules), original_archives=1,
    root_metadata_jobs=len(metadata_jobs), failed_root_metadata_jobs=cut["failed_jobs"], warned_focused_build_jobs=sum(bool(v["warnings"]) for v in bound["focused_builds"].values()),
    public_definitions=0, public_theorems=sum(len(m["specs"]) for m in modules),
    audit_build_jobs=bound["audit"]["build_jobs"], audit_dependencies=bound["audit"]["dependencies"], audit_log_sha256=digest(raw_audit)), indent=2))
