from pathlib import Path
import json

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-flat-pruning-callback-20261027')
head = (area / 'source-head.txt').read_text().strip()
prefix = '''
## Actual flat pruning callbacks now retain completion and restart decisions

Source checkpoint: `SOURCE_HEAD`.
Five new modules and nine public theorems execute partial rendering, every
pending read, the full template callback, metadata updates and restart selection.
The catalog can be nonempty. Structural rendering fuel remains explicit.
The original admitted callback producer supplies its full old packet once.
It derives actual flat singleton rows at every adequate larger bound, equal
metadata and restart decisions, valid native indexes and valid stored tries.
The actual callback retains exactly the same complete satisfying assignments.
The initial Canonical condition remains separate from the recursive Packet.

The continuation executes this callback once and passes its actual returned
cache to the supplied recursive function. It does not execute the whole worker.
No pruning-policy soundness, arbitrary low-fuel correspondence, or completion
of the supplied recursive function is asserted. H6 and captured rendering stay
unchanged. Whole recursive output soundness and completeness remain open.
Audit passes 4012 jobs and 78475 theorem dependency checks. All five modules
and Audit pass strict checks. No Haskell source changed in this checkpoint.
The Haskell repair handoffs and extraction-progress limit remain in FINDINGS.

Next transport actual selected-step and child consumers, then the recursive
worker through these same callback and native histories. Derive initial
Canonical, semantic Ranges and allocation bounds from those histories.
Details: `lean/notes-current-flat-pruning-callback.md`.

'''.replace('SOURCE_HEAD', head)
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/API-COVERAGE.md',
    'lean/COVERAGE.md', 'lean/README.md', 'lean/SYSTEM.md',
    'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for name in documents:
    path = root / name
    old = path.read_bytes()
    first, rest = old.split(b'\n', 1)
    assert b'Actual flat pruning callbacks now retain completion' not in old
    path.write_bytes(first + b'\n' + prefix.encode() + rest)

note = '''# Concrete flat pruning callbacks and restart completion

Source checkpoint: SOURCE_HEAD.
Published base: 3adc1f3d66da95166955fb3ce9f5bd0b3938cae7.
Imported main: 82258094c2c32bb93e517427bc649a5c7077adac.
The formalize pull and main fetch succeeded before this work.
The full formalization goal stays ACTIVE and incomplete. Keep the optimized
interned core and all earlier proofs, repairs, counterexamples and marked drafts.
The previous checkpoint is notes-current-flat-native-terminal.md.

## Strongest global claims

SourceCurrentColdFiniteWarmCalls.constructed_node_calls stays unchanged.
Covered closed construction, formal formulas/entailment and valid original
guard allocation history supply any chosen finite budget/rounds trace.
Derived mathematical width and fuels suffice for those node calls.
The final available node accepts exactly the original finite trees in every
ambient environment. The inherited payload is empty.
This theorem does not certify whole Haskell APIs or whole enumeration.

SourcePruningEnumerationCapturedEdge.diagonal_render_sound_current also stays
unchanged. Under its actual stable completion and current admission gates,
structural discharge, successful rendering and checked residuals derive
original edge and parent acceptance and all original suspended constraints.
It constructs a complete assignment. It does not establish that discharge
or successful rendering exists. Neither global theorem is strengthened here.

## New actual operations

EnumerationFlatPartial uses direct representative and value-slot reads.
Its expandPartial retains structural fuel and the fuelExhausted error.
Only an unconstrained recursive boundary yields the truncated marker.
An unexpanded hole retains its original raw variable ID.
Successful old traces supply the replay's actual intermediate states.
No arbitrary correspondence with insufficient old lookup fuel is asserted.

SourceFlatPruningOracle implements the full concrete callback.
part reads a parked representative and compares it to the supplied current ID.
resume reads every parked part before it sequences pure optional matches.
observe renders once and reads every pending group before finishChecks.
The implementation retains order and repeated pending entries.
Early rejection and the idle concrete-root branch remain separate.
Nonempty catalogs use the real template matching path.
recordTypes uses the same raw type-position update and complete Metadata.
The callback retains openHoles and typing. No synthetic Graph is constructed.

SourceFlatPruningRestart implements candidates, next, decision and run.
It scans expandable raw IDs in allocation order and excludes waiting IDs.
It tests the stop rule on all remaining candidates before preference selection.
Related counters and literal indexes suffice for the same decision.
Stop, done and stuck remain distinct. run rejects the same stuck branch.
Decision equality alone does not derive Safe or index validity.

SourceFlatPruningContinuation.continueWith runs the concrete Left callback once.
True gives normal empty completion with the original Caller and Queries.
False frames the actual returned core into the original cache and invokes
the supplied continuation with returned metadata and its actual restart.
Other raw rows pass unchanged to the supplied diagnostic constructor.
An arbitrary constructor can discard its argument. Recoverability from every
possible Reason value is not asserted. Output and Reason are universe polymorphic.
This operation does not implement the rest of the recursive worker.

## Completion from original admission

SourceFlatPruningCallbackCompletion.complete calls
SourcePruningEnumerationRecursive.callback_complete_canonical once.
It retains the producer's entire existential packet and final Canonical.
That packet includes actual old execution at every larger bound, its exact
singleton, returned Packet, RenderStable, compression Frame, metadata fields
and the universal old continuation equation.

The inputs remain the original recursive Packet, allocated fragment and initial
Canonical, plus a flat cache related to that same original old cache.
Packet contains Context at full Memos, Safe, pending references, native cache
validity, dependency order and allocated pending metadata IDs.
Packet alone does not contain Canonical.
No final flat invariant, future flat observation or successful recursion is input.

For every adequate larger callback fuel, replay derives actual flat singleton
rows with the SAME Boolean and complete Metadata from the old producer.
The actual returned flat cache relates to that SAME old returned cache.
It has valid stored tries and correct native expandable/waiting indexes at
the original Caller heap. Correct follows from returned Packet.valid and
storage alignment. Caller, full Memos and heap do not change in the callback.

For any fixed handle language, residual meaning and complete assignment,
the actual returned flat core is satisfied exactly when the input flat core is.
This follows through both Related endpoints and the actual old compression Frame.
It needs no identification of the supplied Graph with the native heap.
Every stop/order rule has the same restart decision at the related returned cache.
The universal flat continuation equation uses that actual singleton and cache.
The false branch makes no assertion about its supplied continuation's outputs.
Flat endpoints are existential for each adequate bound. One literal flat
endpoint for all bounds is not a public conclusion of this theorem.

## Validation and retained evidence

There are five new modules, nine new public theorems and 450 new source lines.
Audit adds only five imports. All earlier proof source remains unchanged.
Each new module and Audit passes -DwarningAsError=true -Dlinter.all=true.
The aggregate build passes 4012 jobs and checks 78475 theorem dependencies.
It permits only propext, Classical.choice and Quot.sound.
The aggregate build replays the existing unused inputs warning in
InternedFreshOrdinaryClosedCompletion. The strict changed-source checks are clean.

Installed readback includes all nine new theorem signatures, retained H6 and
captured rendering, twelve runtime definitions and the recursive renderer body.
Final readback is 43739 bytes. SHA256:
bea1b23365b5415e0ee5dc5ff9d25bf5587efb444d932ae796bff352a728f5c1.
All eleven theorem readbacks use only permitted axioms.
Checks run serially with 4 GiB memory.max/high, zero swap and a five-minute limit.
Exact strict snapshots, failed proof attempts, logs, installed signatures,
review inputs, literal cuts and checksums remain in the evidence snapshot.
The extra readback exposes the renderer body behind its recursive wrapper.

The inspected live Haskell spans agree with the callback and renderer branches.
This is source comparison. It does not prove concrete container correspondence.
No Haskell edit or new runtime defect is part of this checkpoint.
No native suite was repeated because its source did not change.
FINDINGS retains every prior Haskell repair and the extraction-progress limit.

## Remaining work

Transport actual selected-step, captured child consumers and recursive resume.
Keep the captured sibling metadata/cache and thread actual native effects.
Derive Canonical, semantic numeric Ranges and allocation bounds from that history.
The callback result alone does not prove that a pruned cache is unsatisfiable.
Template-pruning policy soundness remains separate from representation replay.
Scheduler done does not imply structural discharge or an available render carrier.
Whole output classification, coverage and forward completeness remain open.
Mixed typing/pruning APIs, concrete solver correspondence, physical containers,
machine overflow, practical resource bounds and unbounded convergence remain open.
Do not infer explicit flat-map address bounds or Safe from Related alone.

Evidence: lean/restart-evidence/20261027-flat-pruning-callback.
'''.replace('SOURCE_HEAD', head)
(root / 'lean/notes-current-flat-pruning-callback.md').write_text(note)
(area / 'document-paths.json').write_text(json.dumps(documents + ['lean/notes-current-flat-pruning-callback.md'],indent=2)+'\n')
print(json.dumps({'documents':len(documents)+1,'note_bytes':len(note.encode()),'source_head':head}))
