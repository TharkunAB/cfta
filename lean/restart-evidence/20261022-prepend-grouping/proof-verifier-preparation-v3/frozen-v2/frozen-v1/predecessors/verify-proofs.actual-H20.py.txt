"""Check saved original-row cluster-language evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261022-original-row-cluster-language"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()
name, head = "SourceCurrentOriginalRowClusterLanguage", "MicroCFTA.SourceCurrentOriginalRowClusterLanguage.cluster_complete"
selected_sha = "e1c54fe63f95392a928cf539b108a061b64101596a3fc6bfc5c09b72a030eba8"
source_lines = int("393")
strict_stem, full_stem, audit_stem = "original-row-cluster-language-strict-2", "original-row-cluster-language-public-1", "original-row-cluster-language-audit-1"
metrics = dict(actual_jobs=int("4"), source_jobs=int("3"), audit_jobs=int("1"),
    failed_jobs=int("0"), warned_source_exit_zero_jobs=int("1"),
    rejected_public_type_jobs=int("0"))
jobs = json.loads('{"original-row-cluster-language-audit-1": [0, null, "9dee6d0995dd5b2b6a7e3ea9dc5866df756abe877e590d15c96fb23a50c597ea", 0, 0], "original-row-cluster-language-public-1": [0, "f4ac5aacc9d7aa79b5fd9716a55793e0ceb1d13963ad5871f5611fb4fcbea400", "b63da6894e9f7d794c8ecaa1bee4bb76664d556d8d96cd2ab0fef8bd060fb34f", 0, 0], "original-row-cluster-language-strict-1": [0, "c045f16537a73802338f3777a6137b3f58a2c26adcd00c8ceef2fb0dabc12b15", "f812d4ccdadf93237b936e2f9b498ed54a3b40ec5b1706d3c55e5e1eb8065ffa", 0, 1], "original-row-cluster-language-strict-2": [0, "e1c54fe63f95392a928cf539b108a061b64101596a3fc6bfc5c09b72a030eba8", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", 0, 0]}')
rejected = json.loads('[]')
assert jobs and all(stem.startswith("original-row-cluster-language-") for stem in jobs)
assert strict_stem in jobs and full_stem in jobs and audit_stem in jobs
assert jobs[strict_stem][0] == jobs[full_stem][0] == jobs[audit_stem][0] == 0
assert jobs[strict_stem][1] == selected_sha and jobs[strict_stem][3:] == jobs[full_stem][3:] == [0, 0]
assert (evidence / (audit_stem + ".json")).is_file(), "Audit is pending; no complete proof report is available"
actual = set()
for path in evidence.glob("*.json"):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and "wrapper" in item and "exit_code" in item:
        if Path(item.get("command", [""])[0]).name in {"lean", "lake"}:
            actual.add(path.stem)
assert actual == set(jobs), actual
assert metrics["actual_jobs"] == len(actual) and metrics["source_jobs"] == sum(bool(row[1]) for row in jobs.values())
assert metrics["audit_jobs"] == sum(not row[1] for row in jobs.values()) and jobs[audit_stem][1] is None
assert metrics["failed_jobs"] == sum(row[0] != 0 for row in jobs.values())
assert metrics["warned_source_exit_zero_jobs"] == sum(row[0] == 0 and bool(row[1]) and bool(row[4]) for row in jobs.values())
assert len(rejected) == len(set(rejected)) == metrics["rejected_public_type_jobs"] and full_stem not in rejected
assert all(stem in jobs and "public" in stem and jobs[stem][0] == 0 for stem in rejected)
public_hashes = [row[1] for stem, row in jobs.items() if row[1] and "public" in stem]
assert len(public_hashes) == len(set(public_hashes)), "FULL repeated on an unchanged source variant"
for stem, (exit_code, source_hash, log_hash, errors, warnings) in jobs.items():
    receipt = load(stem + ".json")
    assert receipt["exit_code"] == exit_code and receipt["log"] == stem + ".log" and receipt["observed_at"]
    raw = (evidence / receipt["log"]).read_bytes()
    assert re.fullmatch(r"[0-9a-f]{64}", log_hash) and digest(raw) == log_hash, stem
    assert receipt["limits"] == stem + ".limits.json"
    assert load(receipt["limits"]) == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    usage = load(stem + ".usage.json")
    assert 0 <= usage["age_seconds"] <= 600 and usage["remaining_percent"] > 1, stem
    assert receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
    if source_hash:
        assert receipt["source"] == stem + ".source.lean" and receipt["sha256"] == source_hash
        source = (evidence / receipt["source"]).read_bytes()
        assert digest(source) == source_hash and Path(receipt["command"][-1]).name == receipt["source"]
        assert len(receipt["command"]) == 3 and Path(receipt["command"][0]).name == "lean" and receipt["command"][1] == "-Dlinter.all=true"
        assert len(re.findall(r"^.+?:\d+:\d+: error(?:\([^)]*\))?:", raw.decode(), re.M)) == errors
        assert len(re.findall(r"^.+?:\d+:\d+: warning(?:\([^)]*\))?:", raw.decode(), re.M)) == warnings
        if "public" not in stem:
            assert not re.search(r"^\s*set_option (?:maxHeartbeats|maxRecDepth|linter\.)", source.decode(), re.M)
    else:
        assert Path(receipt["command"][0]).name == "lake" and receipt["command"][-2:] == ["build", "MicroCFTA.Audit"]
strict_source = (evidence / (strict_stem + ".source.lean")).read_bytes()
assert len(strict_source.splitlines()) == source_lines <= 500
assert (evidence / (strict_stem + ".log")).read_bytes() == b""
selection = load("selected-sources.json")
source_path = "lean/MicroCFTA/" + name + ".lean"
assert selection == {source_path: dict(sha256=selected_sha, lines=source_lines, strict=strict_stem, full=full_stem)}
source = (evidence / (name + ".lean")).read_bytes()
assert digest(source) == selected_sha and source == strict_source
gate = load("selected-source-gate.json")
assert gate == dict(status="ROOT_ACCEPTED", path=source_path, sha256=selected_sha, lines=source_lines, snapshot="selected-sources/" + name + ".lean")
assert (evidence / gate["snapshot"]).read_bytes() == source
history = load("source-history-gate.json")
assert history == json.loads('{"artifacts": [{"bytes": 616, "path": "original-row-cluster-language-audit-1.json", "sha256": "7c0f5f4ac443ecb73349c182b1c7dbbe4178afe2c465b0cef8e7ebe4d8b1ebec"}, {"bytes": 90, "path": "original-row-cluster-language-audit-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 695, "path": "original-row-cluster-language-audit-1.log", "sha256": "9dee6d0995dd5b2b6a7e3ea9dc5866df756abe877e590d15c96fb23a50c597ea"}, {"bytes": 114, "path": "original-row-cluster-language-audit-1.usage.json", "sha256": "bf9a2ee565bebc3c61aa9a4642ab096d86e116c762ce0fefe2df9c9f67665782"}, {"bytes": 850, "path": "original-row-cluster-language-public-1.json", "sha256": "2f5229272509c9d8476cff97e0327b4f1ac6a191a833b8c33adcc59b7a87c4cf"}, {"bytes": 90, "path": "original-row-cluster-language-public-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 7837509, "path": "original-row-cluster-language-public-1.log", "sha256": "b63da6894e9f7d794c8ecaa1bee4bb76664d556d8d96cd2ab0fef8bd060fb34f"}, {"bytes": 25329, "path": "original-row-cluster-language-public-1.source.lean", "sha256": "f4ac5aacc9d7aa79b5fd9716a55793e0ceb1d13963ad5871f5611fb4fcbea400"}, {"bytes": 114, "path": "original-row-cluster-language-public-1.usage.json", "sha256": "bb217547aa590ec9b273c72028e59dae389cfeceec0d7f86a439401b404049c4"}, {"bytes": 850, "path": "original-row-cluster-language-strict-1.json", "sha256": "a47a1ff9a835ae4cae545784466a99b4b7180e28fc2d98e4b3550a2470d03c67"}, {"bytes": 90, "path": "original-row-cluster-language-strict-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 498, "path": "original-row-cluster-language-strict-1.log", "sha256": "f812d4ccdadf93237b936e2f9b498ed54a3b40ec5b1706d3c55e5e1eb8065ffa"}, {"bytes": 114, "path": "original-row-cluster-language-strict-1.usage.json", "sha256": "63c67fa6ed81ccab5dcbfa190ec97d6ab94f96ceaab9dbe7c74d670c17e3a6a5"}, {"bytes": 850, "path": "original-row-cluster-language-strict-2.json", "sha256": "098ffeb6891711e9b2eee5329aa7d27316030478c66a4bb51699819fb76e379d"}, {"bytes": 90, "path": "original-row-cluster-language-strict-2.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 0, "path": "original-row-cluster-language-strict-2.log", "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}, {"bytes": 114, "path": "original-row-cluster-language-strict-2.usage.json", "sha256": "9d3a600a22d1dd09d384eed7da3dcedb3bb485aba15cce87ad67d347a83e72a0"}, {"bytes": 3233, "path": "root-signature-review.json", "sha256": "7c278790e1c83ae2bf15cbbf83495cebcccdbd636e61b1d629525eda8e39a2ce"}, {"bytes": 1498, "path": "root-source-precheck-v2.json", "sha256": "e28d44703a3bcb34ed5eca60bcd36498a70b27adbaf2a7b6b1286f9ca2c5eac8"}, {"bytes": 1492, "path": "root-source-precheck.json", "sha256": "ebd5ae868139cdb2bfefd1f0a5edf1536e2d0b0b4a2535fe9288f5b039f56c4a"}, {"bytes": 1105, "path": "signature-plan/context.lean.txt", "sha256": "c06a00d6a9daff81a2b460f516c6b28052afdbc7a3e5b63c6f845734fc463d64"}, {"bytes": 2539, "path": "signature-plan/local-complete-statement.lean.txt", "sha256": "aa415ae2fb4fb0e58a8c8ce1ba5ed4cb73229bf9853b3e612e408b80ed027e6e"}, {"bytes": 94, "path": "signature-plan/local-rows-binding.lean.txt", "sha256": "1ca635278f46c50ae752a4d523e1520838d3a080ee70f1a270c885e4eea96e06"}, {"bytes": 2585, "path": "signature-plan/local-strong-IH-expanded.lean.txt", "sha256": "c48b7641c04fa86342393163466473b5546906116a479745ed60dc65a8cb2a58"}, {"bytes": 500, "path": "signature-plan/private-execute-yielded-add.lean.txt", "sha256": "36f9082d97a6b46ec650e7f23ecc8746a5b0500125f01d2484e7aaea1a7af758"}, {"bytes": 4198, "path": "signature-plan/private-scan-boundary-complete.lean.txt", "sha256": "00d0e8ba43ede77f379a88e540540ea105713662a33ca9d525d05f26a77afb0a"}, {"bytes": 3515, "path": "signature-plan/proposed-signature.lean.txt", "sha256": "5ba1182f613a4323a9e8e6f105018c1ee829bc5c0e79dc5caaeac215a397102d"}, {"bytes": 3757, "path": "source-proposal-audit/review.md", "sha256": "af6cff85f80e0dfecf8104478939d925b6149bb030681530a7a0f53a5f27cddd"}, {"bytes": 2427, "path": "source-proposal-v2-audit/review.md", "sha256": "45c2ebcdbac95ddab9f2a0d16ca87a7742a20de1c7156eb207b15658509dc3e6"}, {"bytes": 1425, "path": "source-proposal-v2/note.md", "sha256": "9bd548d02a007cfa852b78884f2267fad8d1e7282e6784372d8197688b6c9109"}, {"bytes": 758, "path": "source-proposal-v2/stopped-full-activation-metadata/mcfta-original-row-cluster-language-activate-full-1.json", "sha256": "1722e8be9e26d3cca793f44ec3418586f43a32d7a1ec77f31f40e9ed89a7a277"}, {"bytes": 90, "path": "source-proposal-v2/stopped-full-activation-metadata/mcfta-original-row-cluster-language-activate-full-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 251, "path": "source-proposal-v2/stopped-full-activation-metadata/mcfta-original-row-cluster-language-activate-full-1.log", "sha256": "56aa64c862177e521d5f2b74999c4964705db7f6b334b38db48bac87286b7d95"}, {"bytes": 37, "path": "source-proposal-v2/stopped-full-activation-metadata/mcfta-original-row-cluster-language-activate-full-1.peaks.txt", "sha256": "d96dde34c8eea5e8b71905bcd85c70798c8b6692fb00112b8f720e9eab63f7aa"}, {"bytes": 1473, "path": "source-proposal-v2/stopped-full-activation-metadata/mcfta-original-row-cluster-language-activate-full-1.source.py", "sha256": "e49da57c10e0ca954f45b47d10f48096b0fd5f6d5ebfd7cb26cde714a47f43fb"}, {"bytes": 114, "path": "source-proposal-v2/stopped-full-activation-metadata/mcfta-original-row-cluster-language-activate-full-1.usage.json", "sha256": "d4a9e119e2b92e4177c5830920e204bef3bce9f2930b0d094d2ca5c2aed631b0"}, {"bytes": 582, "path": "source-proposal-v2/warning-repair.patch", "sha256": "776a73c11f907bf8b46075fc3ef937ad8cd2fa41db119afa83daf33d41b7f173"}, {"bytes": 15065, "path": "source-proposal/H17-to-proposal.patch", "sha256": "fe3172196fc77e6d62cec6043e59e2a41a83d4a7c577505cb6b1a6d667c44946"}, {"bytes": 494, "path": "source-proposal/metadata-preflight-diagnostic.md", "sha256": "d6d68bb57796dbff8322aa5a9e0f237753db8875ae034c303b73d19a4aaa391f"}, {"bytes": 1712, "path": "source-proposal/note.md", "sha256": "316cb7dc3df974399206e767ea11e2fd16d3f2e4dc496ff338235f828de68c2b"}], "patches": [{"after": "source-proposal-v2/SourceCurrentOriginalRowClusterLanguage.lean", "before": "source-proposal/SourceCurrentOriginalRowClusterLanguage.lean", "fromfile": "V1/SourceCurrentOriginalRowClusterLanguage.lean", "path": "source-proposal-v2/warning-repair.patch", "reason": "Remove the sole unused simp argument reported by actual strict1; keep the promotion argument.", "sha256": "776a73c11f907bf8b46075fc3ef937ad8cd2fa41db119afa83daf33d41b7f173", "tofile": "V2/SourceCurrentOriginalRowClusterLanguage.lean"}], "rejected_public_types": [], "selected_source_sha256": "e1c54fe63f95392a928cf539b108a061b64101596a3fc6bfc5c09b72a030eba8", "status": "ROOT_ACCEPTED", "variants": [{"lines": 393, "path": "source-proposal/SourceCurrentOriginalRowClusterLanguage.lean", "reason": "Initial complete proposal; strict1 returned one unused-simp warning.", "sha256": "c045f16537a73802338f3777a6137b3f58a2c26adcd00c8ceef2fb0dabc12b15"}, {"lines": 393, "path": "source-proposal-v2/SourceCurrentOriginalRowClusterLanguage.lean", "reason": "Remove only the unused or_comm argument; selected clean strict input.", "sha256": "e1c54fe63f95392a928cf539b108a061b64101596a3fc6bfc5c09b72a030eba8"}, {"lines": 393, "path": "SourceCurrentOriginalRowClusterLanguage.lean", "reason": "Exact selected math source retained by the public printer materializer", "sha256": "e1c54fe63f95392a928cf539b108a061b64101596a3fc6bfc5c09b72a030eba8"}, {"lines": 393, "path": "original-row-cluster-language-strict-1.source.lean", "reason": "Exact actual ordinary-check input: original-row-cluster-language-strict-1", "sha256": "c045f16537a73802338f3777a6137b3f58a2c26adcd00c8ceef2fb0dabc12b15"}, {"lines": 393, "path": "original-row-cluster-language-strict-2.source.lean", "reason": "Exact actual ordinary-check input: original-row-cluster-language-strict-2", "sha256": "e1c54fe63f95392a928cf539b108a061b64101596a3fc6bfc5c09b72a030eba8"}]}') and history["status"] == "ROOT_ACCEPTED"
assert history["selected_source_sha256"] == selected_sha
assert set(history) == {"status", "selected_source_sha256", "variants", "artifacts", "patches", "rejected_public_types"}
variants = {item["path"]: item for item in history["variants"]}
artifacts = {item["path"]: item for item in history["artifacts"]}
assert variants and len(variants) == len(history["variants"]) and len(artifacts) == len(history["artifacts"])
for path, item in {**artifacts, **variants}.items():
    relative = Path(path)
    assert not relative.is_absolute() and ".." not in relative.parts
    data = (evidence / relative).read_bytes()
    assert re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) and digest(data) == item["sha256"]
    if path in variants:
        assert 0 < len(data.splitlines()) == item["lines"] <= 500 and isinstance(item["reason"], str) and item["reason"].strip()
    else:
        assert len(data) == item["bytes"]
assert not set(variants) & set(artifacts)
for stem, row in jobs.items():
    for suffix in [".json", ".log", ".limits.json", ".usage.json"]:
        assert stem + suffix in artifacts, ("unretained actual job artifact", stem, suffix)
    if row[1] and "public" in stem:
        assert stem + ".source.lean" in artifacts, "FULL printer sources are artifacts, not bounded math variants"
assert any((evidence / path).read_bytes() == source for path in variants)
for stem, row in jobs.items():
    if row[1] and "public" not in stem:
        assert any(pin["sha256"] == row[1] and (evidence / path).read_bytes() == (evidence / (stem + ".source.lean")).read_bytes() for path, pin in variants.items()), stem
for patch in history["patches"]:
    assert isinstance(patch["reason"], str) and patch["reason"].strip()
    assert patch["before"] in variants and patch["after"] in variants
    assert patch["path"] in artifacts and artifacts[patch["path"]]["sha256"] == patch["sha256"]
    before, after = [(evidence / patch[key]).read_text() for key in ["before", "after"]]
    expected = "".join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile=patch["fromfile"], tofile=patch["tofile"]))
    assert (evidence / patch["path"]).read_text() == expected
rejections = {item["stem"]: item for item in history["rejected_public_types"]}
assert len(rejections) == len(history["rejected_public_types"]) and set(rejections) == set(rejected)
for stem, item in rejections.items():
    assert item["raw_sha256"] == jobs[stem][2] and item["reason"] and item["artifacts"]
    assert all(path in artifacts for path in item["artifacts"])
contracts = json.loads('{"context.lean.txt": {"path": "signature-plan/context.lean.txt", "sha256": "c06a00d6a9daff81a2b460f516c6b28052afdbc7a3e5b63c6f845734fc463d64", "lines": 18}, "private-execute-yielded-add.lean.txt": {"path": "signature-plan/private-execute-yielded-add.lean.txt", "sha256": "36f9082d97a6b46ec650e7f23ecc8746a5b0500125f01d2484e7aaea1a7af758", "lines": 7}, "private-scan-boundary-complete.lean.txt": {"path": "signature-plan/private-scan-boundary-complete.lean.txt", "sha256": "00d0e8ba43ede77f379a88e540540ea105713662a33ca9d525d05f26a77afb0a", "lines": 68}, "proposed-signature.lean.txt": {"path": "signature-plan/proposed-signature.lean.txt", "sha256": "5ba1182f613a4323a9e8e6f105018c1ee829bc5c0e79dc5caaeac215a397102d", "lines": 57}, "local-complete-statement.lean.txt": {"path": "signature-plan/local-complete-statement.lean.txt", "sha256": "aa415ae2fb4fb0e58a8c8ce1ba5ed4cb73229bf9853b3e612e408b80ed027e6e", "lines": 36}, "local-rows-binding.lean.txt": {"path": "signature-plan/local-rows-binding.lean.txt", "sha256": "1ca635278f46c50ae752a4d523e1520838d3a080ee70f1a270c885e4eea96e06", "lines": 1}, "local-strong-IH-expanded.lean.txt": {"path": "signature-plan/local-strong-IH-expanded.lean.txt", "sha256": "c48b7641c04fa86342393163466473b5546906116a479745ed60dc65a8cb2a58", "lines": 38}}')
contract_order = ["context.lean.txt", "private-execute-yielded-add.lean.txt", "private-scan-boundary-complete.lean.txt",
    "proposed-signature.lean.txt", "local-complete-statement.lean.txt", "local-rows-binding.lean.txt", "local-strong-IH-expanded.lean.txt"]
assert list(contracts) == contract_order and contracts == load("root-signature-review.json")["contracts"]
expected_helpers = ["execute_yielded_add", "scan_boundary_complete"]
positions = {}
for filename, item in contracts.items():
    assert set(item) == {"path", "lines", "sha256"}
    relative = Path(item["path"])
    assert not relative.is_absolute() and ".." not in relative.parts
    declaration = (evidence / relative).read_bytes()
    assert re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) and digest(declaration) == item["sha256"]
    assert type(item["lines"]) is int and 0 < len(declaration.splitlines()) == item["lines"] <= 500
    if filename == "context.lean.txt":
        assert source.startswith(declaration)
    elif filename == "local-strong-IH-expanded.lean.txt":
        assert declaration not in source, "Expanded IH is review-only; it is not an extra source declaration"
    else:
        literal = b"\n" + declaration if filename == "local-rows-binding.lean.txt" else declaration.rstrip(b"\n") + b" := by\n"
        assert source.count(literal) == 1 and source.index(literal) >= len((evidence / contracts["context.lean.txt"]["path"]).read_bytes())
        positions[filename] = source.index(literal)
compiled_order = ["private-execute-yielded-add.lean.txt", "private-scan-boundary-complete.lean.txt", "proposed-signature.lean.txt",
    "local-rows-binding.lean.txt", "local-complete-statement.lean.txt"]
assert [positions[key] for key in compiled_order] == sorted(set(positions.values()))
assert re.findall(r"^(?:private )?(?:noncomputable )?(?:def|theorem|lemma|abbrev|opaque|structure|inductive|instance) (\w+)", source.decode(), re.M) == expected_helpers + ["cluster_complete"]
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "7e754f81ab43baeace185b866adaf0a38c61ab347b402752cf83bba73882de5e" and len(original.splitlines()) == 3125
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3125, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentOriginalRowClusterLanguage\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/original-row-cluster-language-full-readback.json")
printer = (evidence / (full_stem + ".source.lean")).read_bytes()
raw = (evidence / (full_stem + ".log")).read_bytes()
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
tail = "\n" + "".join("set_option " + option + "\n" for option in options) + "".join(d + head + "\n" for d in ["#check @", "#print ", "#print axioms "])
assert printer == source + tail.encode() and len(printer.splitlines()) == source_lines + 14 and len(tail.splitlines()) == 14
assert all(printer.decode().splitlines().count("set_option " + option) == 1 for option in options)
assert all(printer.decode().splitlines().count(d + head) == 1 for d in ["#check @", "#print ", "#print axioms "])
for stem, row in jobs.items():
    if row[1] and "public" in stem:
        public_source = (evidence / (stem + ".source.lean")).read_bytes()
        assert any(public_source == (evidence / path).read_bytes() + tail.encode() for path in variants), stem
assert source.rstrip().endswith(("end MicroCFTA." + name).encode())
assert (report["source_sha256"], report["source_lines"], report["printer_sha256"]) == (selected_sha, source_lines, digest(printer))
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == int("7837509")
assert report["receipt_sha256"] == digest((evidence / (full_stem + ".json")).read_bytes()) and report["owned_public_job_exit"] == 0
assert all(report[key] for key in ["all_eight_printer_settings", "exact_module_and_diagnostic_tail", "diagnostic_limits_after_module_only", "no_omissions"])
assert len(report["heads"]) == 1 and report["heads"][0]["head"] == head and report["heads"][0]["kind"] == "theorem"
log = raw.decode()
assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
markers = list(re.finditer(r"^(?:@)?" + re.escape(head) + r" :", log, re.M))
assert len(markers) == 1 and not log[:markers[0].start()].strip()
segment = log[markers[0].end():]
assert segment.count("\ntheorem " + head + " :") == 1
checked, printed = segment.split("\ntheorem " + head + " :", 1)
axioms = list(re.finditer(r"^'" + re.escape(head) + r"' (depends on axioms:|does not depend on any axioms)", printed, re.M))
assert len(axioms) == 1
axiom = axioms[0]
declaration, axiom_output = printed[:axiom.start()], printed[axiom.start():]
normalized, matches = "".join(checked.split()), []
for match in re.finditer(r" :=\n", declaration):
    prefix = "".join(declaration[:match.start()].split())
    if prefix == normalized:
        matches.append(match)
    elif len(prefix) > len(normalized):
        break
assert len(matches) == 1
declared, body = declaration[:matches[0].start()], declaration[matches[0].end():]
assert checked.encode() == declared.encode() and len(checked) == int("69575") and len(checked.encode()) == int("69619")
assert len(checked.splitlines()) == int("725") and checked.count("\n") == int("724") and checked.endswith("\n") == json.loads('false')
assert digest(checked.encode()) == "c389a111047d46708592ebc6c0b098106bcd6121f25b490285d4f6e0cf3f9f4c"
assert not any(token in checked for token in ["_private", "✝", "†", "‡"])
helpers = []
for line in source.decode().splitlines():
    if re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\b", line):
        declaration = re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\s+(?:(?:noncomputable|unsafe|partial)\s+)?(?:def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", line)
        assert declaration, ("unsupported private declaration", line)
        helpers.append(declaration.group(1))
assert helpers == expected_helpers
assert not any(re.search(re.escape("MicroCFTA." + name + "." + helper) + r"(?![\w'])", checked) for helper in helpers)
head_report = report["heads"][0]
assert all(head_report[key] for key in ["check_print_type_identity", "check_print_type_byte_identity", "unique_complete_type_body_delimiter", "actual_axioms_within_standard_allowed"])
assert head_report["private_namespace_helpers_checked"] == helpers and head_report["private_type_spellings_checked"] == ["_private", "✝", "†", "‡"] and head_report["private_public_type_names"] is False
assert head_report["checked_type_characters"] == len(checked) and head_report["body_characters"] == len(body) == int("7697213")
assert body.startswith("fun ") and len(body.encode()) == int("7697983")
values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
actual_axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
assert actual_axioms == set(head_report["actual_axioms"]) == set(json.loads('["Classical.choice", "Quot.sound", "propext"]')) and actual_axioms <= {"Classical.choice", "Quot.sound", "propext"}
for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
    filename = "original-row-cluster-language-cluster_complete-" + suffix + ".txt"
    retained = (evidence / "public-readback" / filename).read_bytes()
    assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
assert digest((evidence / "full-preparation/check-full-public.py").read_bytes()) == "3ae45e59ff5ab313e2b8824ea67b25ad214d2e5a5f6248dd74db322e45fdfcf3"
review = load("root-full-review.json")
assert review["status"] == "ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT" and review["source_sha256"] == selected_sha and review["source_lines"] == source_lines
assert review["public_theorem"] == head and review["complete_public_type_root_review"] == review["independent_complete_public_type_review"] == "CLEAR"
assert review["root_read_complete_public_type"] and review["root_printed_type_byte_identity_verified"] and review["check_print_type_byte_identity"] and review["four_private_markers_and_all_helpers_absent_from_type"]
assert review["type_sha256"] == digest(checked.encode()) and review["full_raw_sha256"] == digest(raw) and review["actual_axioms"] == sorted(actual_axioms)
assert review["body_retained_and_programmatically_checked"] and review["whole_body_manual_read_claimed"] is False
required_true = ['actual_cluster_completion_derived', 'all_ambient_physical_kept_union_iff', 'exact_original_parent_symbol_filtered_group', 'original_membership_and_length_bounds_retained', 'same_source_facts_holds_admitted_model_and_ranked_input', 'same_original_available_closed_parent', 'same_populated_wrapper_and_native_state', 'same_h15_common_middle_resident_full_law_and_packet', 'h19_sound_deletion_implications_used', 'candidate_first_drop_promotion_and_reversed_accumulators', 'generalized_inner_boundary_and_outer_strong_IH', 'all_current_packet_outputs_retained', 'genuine_initial_width_room_and_initial_domain_valid', 'same_global_allocation_trace_retained', 'noncomputable_modeled_control_explicit']
required_false = ['haskell_execution_or_refinement_claimed', 'public_pass_claimed', 'whole_goal_complete', 'grouping_or_reconstruction_claimed', 'generated_parent_or_mu_claimed', 'practical_width_or_convergence_claimed', 'second_comparison_for_semantics', 'future_success_or_desired_language_oracle', 'post_room_or_per_comparison_room_oracle', 'replacement_input_model', 'silent_original_parent_admission', 'bounded_completeness_projection_used_for_deletion', 'rank_erasure_used', 'semantic_incomparability_or_sublist_claimed']
assert all(review[key] is True for key in required_true) and all(review[key] is False for key in required_false)
audit = (evidence / (audit_stem + ".log")).read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == int("3637") and int(dependencies.group(1)) == int("75482")
print(json.dumps(dict(status="PASS", live=args.live, **metrics, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
