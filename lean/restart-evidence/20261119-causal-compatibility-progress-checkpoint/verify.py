"""Verify the source and result archive without running a compiler."""

from pathlib import Path, PurePosixPath
import hashlib
import json
import tarfile


HERE = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()
manifest = json.loads((HERE / "manifest.json").read_text())
for name, expected in manifest["files"].items():
    data = (HERE / name).read_bytes()
    assert len(data) == expected["bytes"] and sha(data) == expected["sha256"], name

selected = json.loads((HERE / "inputs.json").read_text())
payloads = {}
with tarfile.open(HERE / "inputs.tar.gz", "r:gz") as archive:
    for member in archive.getmembers():
        path = PurePosixPath(member.name)
        assert member.isfile() and not path.is_absolute() and ".." not in path.parts
        assert member.name in selected and member.name not in payloads
        assert path.suffix not in {".olean", ".ilean", ".o", ".hi", ".so", ".a", ".pyc"}
        data = archive.extractfile(member).read()
        expected = selected[member.name]
        assert len(data) == expected["bytes"] and sha(data) == expected["sha256"], member.name
        assert not data.startswith(b"\x7fELF"), member.name
        payloads[member.name] = data
assert payloads.keys() == selected.keys()

def saved(suffix):
    matches = [data for name, data in payloads.items() if name.endswith(suffix)]
    assert len(matches) == 1, suffix
    return json.loads(matches[0])

observed = saved("occurs-probe-work/ROOT-OBSERVATIONS.json")
assert observed["GHC_positive_control_exit"] == 0
assert observed["GHC_negative_control_exit"] == 1
assert observed["runtime_tool_terminal_exit"] == 0
assert not observed["counterexample_established"]
for route, count in [("public", 45), ("typed", 56)]:
    stream = observed["streams"][route]
    assert stream["exhausted"] and stream["scanned"] == count
    assert stream["statuses"] == {
        "fresh_occurs_negative": "absent_after_exhaustion",
        "fresh_identity_positive": "present",
    }
cleanup = saved("occurs-probe-work/ROOT-TMP-CLEANUP.json")
assert cleanup["regular_bytes_removed"] == 10881163
assert cleanup["normal_Source_preserved"] and cleanup["normal_cache_preserved"]
join = saved("terminal-join-check/results.json")
assert join["driver_exit"] == 0 and join["proof_credit"]
assert join["total_axiom_reports"] == 1 and not join["nonstandard_axioms"]
assert not join["diagnostics"] and not join["warnings"] and not join["sorryAx"]

print(json.dumps({
    "status": "PASS: archive hashes and recorded result boundaries",
    "files": len(payloads),
    "compressed_bytes": (HERE / "inputs.tar.gz").stat().st_size,
    "compiler_or_runtime_rerun": False,
    "new_public_theorems": 0,
    "historical_joint_assignment_proved": False,
    "original_root_acceptance_proved": False,
}))
