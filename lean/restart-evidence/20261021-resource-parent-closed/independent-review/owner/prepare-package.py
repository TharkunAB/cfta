from pathlib import Path
import hashlib
import json
import shutil

HERE = Path(__file__).resolve().parent
PREFIX = "resource-parent-closed"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def write(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + "\n")


shutil.copytree("/tmp/mcfta-resource-parent-closed-next-plan", HERE / "inputs/plan")
source = (HERE / "SourceCurrentResourceParentClosed.lean").read_bytes()
proposal = (HERE / "inputs/plan/proposed-signature.lean.txt").read_bytes()
start = source.index(b"theorem children\n")
end = source.index(b" := by\n", start)
assert source[start:end] == proposal and len(source.splitlines()) == 101
assert source == (HERE / "parent-closed-source-only.lean.txt").read_bytes()
readback = json.loads((HERE / "full-public-readback.json").read_text())
assert readback["source_sha256"] == digest(source)
attempts = []
for stem, kind in [(PREFIX + "-direct-1", "strict"), (PREFIX + "-public-1", "FULL")]:
    receipt = json.loads((HERE / (stem + ".json")).read_text())
    assert receipt["exit_code"] == 0
    attempts.append({"name": stem, "kind": kind, "exit_code": 0,
        "source_sha256": receipt["sha256"], "receipt": stem + ".json",
        "raw_log": stem + ".log", "usage": stem + ".usage.json",
        "limits": stem + ".limits.json", "actually_launched": True})
write("attempt-ledger.json", {"actual_lean_jobs": 2, "failed_jobs": 0,
    "warning_jobs": 0, "infrastructure_nonlaunches": 0, "canonical_jobs": 0,
    "runtime_jobs": 0, "constructed_pairs": 0,
    "prelaunch_source_changes_after_complete_review": 0, "attempts": attempts})
write(PREFIX + "-selection.json", {"finalized": True,
    "source": "SourceCurrentResourceParentClosed.lean", "source_sha256": digest(source),
    "source_lines": 101, "official_path": "lean/MicroCFTA/SourceCurrentResourceParentClosed.lean",
    "selected_strict": PREFIX + "-direct-1", "selected_public": PREFIX + "-public-1",
    "groups": [{"name": head["head"], "pairs": 1, "kind": "production", "full_proof": True}
        for head in readback["heads"]],
    "actual_axioms_by_head": {head["head"]: head["actual_axioms"] for head in readback["heads"]},
    "actual_lean_jobs": 2, "failed_jobs": 0, "warning_jobs": 0,
    "canonical_jobs": 0, "runtime_jobs": 0, "constructed_pairs": 0,
    "all_eight_settings": True, "actual_type_identity": True,
    "exact_public_header_proposal": True,
    "scope": "Closed captured children imply closed returned children for the same historical resource Parent writer.",
    "no_new_edge_ledger_or_current_cut": True,
    "all_prefix_and_node_memo_closure_unproved": True,
    "fuel_adequacy_and_completion_unproved": True})
usage = [json.loads((HERE / attempt["usage"]).read_text()) for attempt in attempts]
(HERE / (PREFIX + "-report.md")).write_text(f'''# Closed children from the same historical Parent writer

Final source: SourceCurrentResourceParentClosed.lean, 101 lines, SHA {digest(source)}. Its sole public children header is byte-identical to the frozen eight-line proposal. The complete approved source passed without any prelaunch review correction or postlaunch source change.

The theorem takes one ResourceParentWriters.Written request returned witness and ClosedValues request.value.children. It proves ClosedValues returned.children. ClosedValues means that each literal Value.free list is empty. It permits references bound inside an opaque Mu. It does not assert that every available heap value is closed.

Written is a genuine historical resource contract. One existential retains the complete before Caller, global memo bundle, inventory, profile, exact captured request and actual Parent done equation. It also retains Context, Frame, Fits, inherited readiness, resident input, the conditional live field, resident reservation, union normality, native positive Support, causal Mu History and both Merge laws at that same entry. These premises were not removed. The new theorem requires no current reader heap, live inherited result, current prefix execution, later growth premise, positive output or new edge memo ledger.

The proof unpacks that writer once. ActualParentBranchCases.edge_cases supplies the exact unchanged, erased, singleton Empty or selected continuation. Literal list closure handles the first three cases, including stopped Scan and constructor rejection. The selected case calls SelectedCertificates.selected_certificates once on the same Parent, precheck, Scan, Required and class pass. It retains the same required result and heap, prepared inventory, path domains, global memo validity and PassReads. A private helper applies the existing requireAll_complete to the original closed list at the actual scanned heap. Existing required_unique aligns both the output list and heap with the same actual completed Required equation. No independent returned value is selected.

The same pass receives the Required receipt's ready, admitted and resident facts. Retained.fields and the actual precheck derive coherence and activity. The required receipt supplies the exact retained path domains. The writer's physical Merge Stored certificate is transported through the actual Scan and Required Keeps. That existing certificate already includes input-closed implies result-closed for each saved cell; availability alone is not used as a replacement. The writer's covered law is unchanged. Existing Pass.verified supplies Receipt.domains. At path [], ForestClosed is exactly ClosedValues, so it closes the same returned child list. The proof adds no native, projection, edit, Head or exposure induction and no guard-alignment argument.

Root and guard read the complete 101-line source and exact header before the first compiler check. Strict1 passed with a literally empty raw log. The sole FULLpublic1 passed. The hardened reader verified all eight settings, complete check/print TYPE identity, one actual lambda proof delimiter, no omissions, no private public TYPE identifiers and the actual axiom set {readback['heads'][0]['actual_axioms']}. The complete public log has {readback['log_bytes']} bytes and SHA {readback['log_sha256']}. The printer SHA is {readback['printer_sha256']}. The normalized TYPE has {readback['heads'][0]['normalized_type_characters']} characters and the proof body has {readback['heads'][0]['body_characters']} characters. Metadata readback passed on its first run.

There are two actual author Lean commands and zero failures, warnings, infrastructure nonlaunches, canonical jobs, runtime examples or constructed pairs. Each actual command has its immutable source input, full raw log, receipt, fresh usage record and effective-limit record. Weekly remaining percentages are {[item['remaining_percent'] for item in usage]}, with ages {[item['age_seconds'] for item in usage]} seconds. Each worker verified MemoryMax=MemoryHigh=4294967296 bytes and memory.swap.max=0. Each wrapper imposed five minutes. The recorded peaks remain in resource-parent-closed-peaks.txt. Root's independent strict and Audit are separate commands and are not included in this author inventory.

This result can close warm returned edge children through the existing same-writer Origins ledger. It does not establish the separate conditional closure invariant for returned node cells, closure at every unfinished outer prefix, exclusion of every unexpectedReference fault under the old generic packet, sufficient outer fuel, a finite-width capacity envelope or successful unrestricted completion. The frozen source-only plan keeps those obligations open and is copied unchanged under inputs/plan.

The author wrote the ResourceParentWriters and SelectedCertificates foundations and related native-store and positive-chronology adapters. This package does not claim independent review of those authored foundations. Guard independently reviewed the new composition, exact source and complete selected public readback. Root owns official installation and independent repository checks. No official source, Audit file, earlier frozen package, Git state or shared board was edited by this component.
''')
excluded = {PREFIX + "-manifest.json", PREFIX + "-verification.json", PREFIX + "-live-verification.json"}
files = []
for path in sorted(HERE.rglob("*")):
    relative = path.relative_to(HERE).as_posix()
    if path.is_file() and relative not in excluded:
        data = path.read_bytes()
        files.append({"path": relative, "bytes": len(data), "sha256": digest(data)})
write(PREFIX + "-manifest.json", {"finalized": True, "source_sha256": digest(source),
    "actual_lean_jobs": 2, "failed_jobs": 0, "files": files})
print(json.dumps({"manifest_sha256": digest((HERE / (PREFIX + "-manifest.json")).read_bytes()),
    "selection_sha256": digest((HERE / (PREFIX + "-selection.json")).read_bytes()),
    "report_sha256": digest((HERE / (PREFIX + "-report.md")).read_bytes()),
    "local_pins": len(files)}))
