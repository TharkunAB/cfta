from pathlib import Path
import hashlib, json
ROOT = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()
index = json.loads((ROOT / "source-index.json").read_text())
cut_count = 0
for record in index["sources"]:
    data = (ROOT / record["copy"]).read_bytes()
    assert len(data) == record["bytes"] and sha(data) == record["sha256"], record
    assert Path(record["source_path"]).read_bytes() == data, record["source_path"]
    lines = data.splitlines(keepends=True)
    for cut in record.get("cuts", []):
        first, last = cut["start_line"], cut["end_line"]
        assert 1 <= first <= last <= len(lines), cut
        expected = b"".join(lines[first - 1:last])
        actual = (ROOT / cut["path"]).read_bytes()
        assert actual == expected and len(actual) == cut["bytes"] and sha(actual) == cut["sha256"], cut
        cut_count += 1
for comparison in ["incoming", "terminal-child", "child"]:
    contract = ROOT / "contracts" / comparison
    assert (contract / "old-conclusion.lean.txt").read_bytes() == (contract / "recovered-conclusion.lean.txt").read_bytes()
    header = "common-admission" if comparison == "incoming" else "admission"
    assert (contract / f"old-{header}.lean.txt").read_bytes() == (contract / f"recovered-{header}.lean.txt").read_bytes()
checks = []
for report_path in sorted((ROOT / "evidence").glob("*/report.json")):
    report = json.loads(report_path.read_text())
    if "exit_code" not in report or not (report_path.parent / "raw.log").is_file():
        continue
    raw = (report_path.parent / "raw.log").read_bytes()
    assert len(raw) == report["bytes"] and sha(raw) == report["sha256"], report_path
    limits = report.get("cgroup_limits", {})
    if limits:
        assert limits == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}, limits
    checks.append({"path": str(report_path.relative_to(ROOT)), "exit_code": report["exit_code"], "raw_bytes": len(raw)})
summary = {"status": "PASS", "source_records": len(index["sources"]), "literal_cuts": cut_count, "checks": checks}

# Check the final checkpoint preservation records at the reviewed live paths.
repo = Path("/home/tritlo/Code/mcfta")
for record in json.loads((ROOT / "prior-source-preservation.json").read_text())["sources"]:
    data = (repo / record["path"]).read_bytes()
    assert len(data) == record["bytes"] and sha(data) == record["sha256"], record
for record in json.loads((ROOT / "documents/comparison.json").read_text())["documents"]:
    data = Path(record["document_source_path"]).read_bytes()
    if "region_copy" in record:
        assert len(data) == record["current_bytes"] and sha(data) == record["current_sha256"]
        start = record["offset"]; end = start + record["region_bytes"]
        assert data[start:end] == (ROOT / record["region_copy"]).read_bytes()
        prior = data[:start] + data[end:]
        assert len(prior) == record["prior_bytes"] and sha(prior) == record["prior_sha256"]
        assert prior == Path(record["prior_copy_source"]).read_bytes()
    else:
        assert data == (ROOT / record["copy"]).read_bytes()
audit = json.loads((ROOT / "audit/comparison.json").read_text())
current = (ROOT / "audit/current.lean").read_bytes(); prior = (ROOT / "audit/prior.lean").read_bytes()
start = audit["offset"]; end = start + audit["added_bytes"]
assert current[:start] + current[end:] == prior
print(json.dumps({**summary, "final_preservation_status": "PASS", "prior_sources": 82, "document_inverse_bodies": 9, "audit_inverse": True}, indent=2))
