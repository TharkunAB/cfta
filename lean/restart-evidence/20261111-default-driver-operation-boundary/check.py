from pathlib import Path
import hashlib
import json

packet = Path(__file__).resolve().parent
root = packet.parents[2]
sources = json.loads((packet / "source-hashes.json").read_text())
for name, expected in sources.items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == expected, name
report = {
    "passed": True,
    "all_source_hashes_exact": True,
    "source_files": len(sources),
    "scope": "source operation map; no runtime replay or equivalence proof",
    "default_expansion": "enumerateNode recursively expands ordinary children",
    "shared_expansion": "ShallowChild.prepareChild defers ordinary children",
    "shallow_source_api": "termsPruneUntil",
    "runtime_replay": False,
    "default_erased_term_simulation_proved": False,
    "ordered_output_equivalence_proved": False,
    "production_behavior_bug_established": False,
}
print(json.dumps(report, indent=2))
