import datetime
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-parent-scan.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
counts = json.loads((HERE / 'attempt-expectations.json').read_text())
source = ROOT / 'lean/MicroCFTA/SourceCurrentActualParentScanNativeStores.lean'
digest = hashlib.sha256(source.read_bytes()).hexdigest()
lines = len(source.read_text().splitlines())
audit = (HERE / 'audit-1.log').read_text()
assert f"Build completed successfully ({counts['audit_jobs']} jobs)" in audit
assert f"{counts['audit_dependencies']} MicroCFTA theorems" in audit
assert not (HERE / 'parent-scan-strict-1.log').read_bytes()
evidence = (f"Audit passes {counts['audit_jobs']} jobs /{counts['audit_dependencies']} dependencies. "
    f"There are {counts['actual_lean_lake_jobs']} actual Lean/Lake commands and "
    f"{counts['nonzero_lean_jobs']} retained nonzero commands.")
update = f'''## Current native state at the actual selected Parent Scan

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-actual-parent-scan-stores.md`.

ActualParentScanNativeStores.selected_scan derives the admitted Scan and
its native state laws at the SAME observed historical Parent Scan cut.
It calls the existing numeric Parent producer once. It retains that same
receipt in the conclusion. Successful worker determinism aligns outcome,
selected paths, complete checked state and fourth memo with the literal
RecordScan return. The numeric graph is not an input oracle.

The actual precheck receipt supplies Ready and proper original paths.
Its complete native state is literally unchanged. Entry Values, Current,
positive native Support and causal History therefore apply at that prefix.
ScanNativeStores then supplies full Ready, physical Effects, machine
Extension, original Values, Current, Support and History at the SAME cut.
No cap, future enclosing return or per-sibling Ready is a new premise.

Genuine initial Context, Frame, Profile, Fits, LiveInputs and Reserved
remain explicit resource premises. Initial native laws also remain.
This local producer does not create resources at every unfinished outer
prefix or retain them in the cold/warm historical writer table.

Root strict, complete FULL and independent review pass. {evidence}
Selected checks are clean. Only the old ClosedCompletion Audit warning
remains. Every actual proof command has fresh usage and effective 4 GiB
max/high, swap zero and five-minute limits. Counts do not measure completion.

The frozen next geometry plan derives the actual source row is nonplain
from nonempty retained records. The actual inherited-first combination
gives whole-class Covers and fixedness for the same combined family.
Its proposed consumer lifts actual Required/pass positive ancestry through
that coverage and calls the finite same-child pair theorem. That consumer
is not proved in this checkpoint. Historical writer-entry production,
unfinished prefix resources, owner exclusion, renewal, retention, outer
completion, convergence and Haskell refinement remain open.

All older source/evidence and controlled version exceptions remain.
Haskell/packages/main, stashes and other worktrees stay unchanged.
No new Haskell defect or repair. FINDINGS keeps its repair index FIRST.
The full goal stays active.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
ActualParentScanNativeStores.selected_scan now derives actual Scan
admission and full state laws from one resource-backed Parent receipt.
The literal RecordScan cut aligns in outcome, selected paths, complete
checked state and fourth memo. Initial native laws transport through
literal precheck native equality, then through the SAME admitted Scan.
The same numeric receipt stays in the conclusion. No admission oracle,
cap, future enclosing return or per-sibling Ready is supplied.

Genuine Context/Frame/Profile/Fits/Live/Reserved and initial native laws
remain. Cold/warm writer retention and unfinished prefix production are
still open. The frozen next plan connects the actual source row and
whole-class Covers to same-child geometry. Its consumer is not yet proved.
Owner exclusion, renewal, retention, outer completion, convergence and
Haskell refinement remain open. Counts do not measure completion.

Root strict empty; complete FULL and independent review pass.
{evidence}
Only the old Audit warning remains. All earlier raw attempts survive.
No Haskell source, runtime result, external repair or imported main changes.
Read `lean/notes-current-actual-parent-scan-stores.md`. Goal active.
The external Haskell repair index stays FIRST.
'''
note = f'''# Native state at the same actual selected Parent Scan

Updated: {now}. Selected proof: `{proof}`.
SourceCurrentActualParentScanNativeStores has {lines} lines and one public
selected_scan theorem. Source SHA256: {digest}.

The input describes one literal ParentWorker.edge.done return and its
actual precheck.classes and RecordScan.done none cuts. This is the selected
branch already exposed by ActualOwnerSelection.selected. The theorem
requires genuine initial semantic Context, Frame, Profile, Fits,
LiveInputs and Reserved resources, plus initial CurrentNative.At Plain,
positive native Support and causal History. The width is bits + 2.
Context retains its ordinary initial Merge and global memo semantic laws.
No admitted Scan or desired final state law is a caller premise.

ActualParentSemanticReads.parent runs once. Its numeric receipt retains
the same complete Parent return, admitted Parent graph and semantic reads.
The new theorem returns this exact receipt with its inventory and final
memo parameters. It does not choose an independent second execution.

A private graph_scan helper inverts that receipt's actual Parent graph.
The original noncontradictory test excludes rejection. The supplied
literal precheck excludes unchanged and emptyChildren. Both remaining
ScanClassPass constructors contain an admitted Scan. This extraction does
not assume any native property at a later reader.

ScanWorkerCompletion supplies a stable literal return for that graph.
RecordScanWorker.scan_mapPaths maps the observed record result to the
ordinary worker. ScanWorkerStability.scan_done_unique aligns the full
result pair, checked state and fourth memo. Thus the extracted graph has
outcome none and the supplied kept paths at the exact scanned state.
This is successful-worker determinism. It is not global writer uniqueness
or a claim that raw execute.done itself proves physical word admission.

LiveInputs supplies the exact cached load, inherited readiness and
original forest availability. LocalReductionActual.prefix_verified
constructs the concrete Precheck receipt from initial Context. Its classes
field derives every original path is nonempty. Its ready field supplies
the full Ready at the exact prefix. Precheck.state_native is literal
equality of the complete native state. This equality transports Values,
Current, Support and causal History. Heap growth alone is not used.

ScanNativeStores.scan is called once on the same aligned graph. Its seven
returned laws are full Ready, physical Effects, machine Extension,
original Values, Current, positive Support and Nonempty causal History.
The numeric receipt remains beside those exact state facts. No whole
forest closure, input cap, additional Scan oracle, future enclosing return
or per-sibling Ready is introduced by this adapter.

Root read the complete source-only draft and every final delta. Independent
review checks the new adapter and discloses authored dependencies.
Selected and root strict logs are empty. Complete FULL readback records
all eight printer settings, complete public proof and public type, checked
and printed type identity, and the actual standard axioms.
{evidence}
No canonical, infrastructure or constructed consumer job is hidden.
Copies add no jobs. Every actual proof command retains fresh usage and
effective max/high 4 GiB, swap zero and five-minute limits.

This is a local completed-writer producer. It does not construct initial
resources at every unfinished outer prefix. It does not add native entry
laws to the historical writer ledger or infer them from current reader
laws. A future ledger must retain one joint writer tuple, not independently
chosen old and new witnesses. Warm hits must recover that same request.

The next frozen geometry plan consumes actual Precheck, Retained, Required
and PassReads certificates for one tuple. Nonempty kept records imply the
same original row is nonplain. Actual inherited-first combination supplies
whole-class Covers and fixedness in one live combined payload. A private
Rel lift preserves both endpoints and their same suffix in one component.
RequiredPositiveChronology and PositiveOwnerPair then give two different
suffixes through the chosen child in that same combined family. This
consumer is not proved in this checkpoint. Its genuine historical native
and class resource premises remain separate obligations.

Owner exclusion, renewal, unfolding progress, final retention, outer
completion, convergence and Haskell refinement remain open. Earlier
counterexamples, proofs, raw logs and additive version exceptions remain.
Haskell/packages/main stay unchanged. No new Haskell runtime defect or
external repair. FINDINGS keeps its repair index first. Goal active.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        prefix = '# Current formalization findings\n\n## Haskell fix handoff for external work\n'
        marker = prefix + '\n' + (HERE / 'haskell-repair-index.md').read_text().rstrip() + '\n'
        assert original.startswith(marker)
        rest = original[len(marker):]
        assert rest.startswith('\n')
        changed = marker + '\n' + findings + '\n' + rest[1:]
        assert changed.replace(findings + '\n', '', 1) == original
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.replace(update + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
(ROOT / 'lean/notes-current-actual-parent-scan-stores.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
