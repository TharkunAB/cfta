from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-flat-native-branches-20261027')
head = (area / 'source-head.txt').read_text().strip()
base = (area / 'published-base.txt').read_text().strip()
aggregate = (area / 'aggregate/raw.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', aggregate).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', aggregate).group(1)
modules = json.loads((area / 'modules.json').read_text())
public = json.loads((area / 'installed-public/report.json').read_text())
theorems = len(json.loads((area / 'public-declarations.json').read_text())) - 2
definitions = len(json.loads((area / 'public-definitions.json').read_text()))
lines = sum(len((root / 'lean/MicroCFTA' / (module + '.lean')).read_text().splitlines()) for module in modules)

prefix = f'''
## Actual flat ordinary scans now retain completion and sibling history

Source checkpoint: {head}.
Eight new modules execute ordinary entry and ordered native alternatives.
Original admission derives actual flat plain-sibling and ordinary completion
at every adequate native bound, for any related initial flat cache.
Every sibling restores the captured enumeration cache. Only its actual reached
native Caller and Queries pass to the next sibling. The full earlier packets
retain Post/global Memos, every receipt's prefix postcondition, pending-reference
and fragment histories, and the condition for finishing all supported alternatives.
Receipt consumers derive native index correctness at each receipt's own heap/cache.
No future flat observation or desired final flat invariant is an input.

The hook-aware sibling and ordinary runtimes are also defined and checked.
Their identity bridges hold at every input. Explicit heterogeneous payload
relations support different flat and earlier output and failure types.
These runtimes do not yet prove completion for recursive hooks. Such siblings
must use the actual post-hook native endpoint, beyond the plain scan's contract.
Whole recursive correspondence, output soundness, coverage, pruning-policy
soundness and initial admission histories remain open. H6 stays unchanged.
Audit passes {jobs} jobs and {dependencies} theorem dependency checks.
All eight modules and Audit pass strict checks. No Haskell source changed.
FINDINGS retains every Haskell repair handoff and the extraction-progress limit.

Next compose concrete callbacks and recursive outputs/failures through the
actual post-hook sibling endpoints. Use the original finite-depth resource
induction. Derive initial Canonical, semantic Ranges and allocation histories.
Details: `lean/notes-current-flat-native-branches.md`.

'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/API-COVERAGE.md',
    'lean/COVERAGE.md', 'lean/README.md', 'lean/SYSTEM.md',
    'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
records = []
for name in documents:
    path = root / name
    old = path.read_bytes()
    assert old == subprocess.check_output(['git', 'show', base + ':' + name], cwd=root)
    target = area / 'prior-documents' / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(old)
    first, rest = old.split(b'\n', 1)
    data = first + b'\n' + prefix.encode() + rest
    path.write_bytes(data)
    records.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest(),
        offset=len(first) + 1, inserted_bytes=len(prefix.encode())))

note = f'''# Actual flat ordinary and sibling completion

Source checkpoint: {head}.
Published base: {base}.
Imported main: 82258094c2c32bb93e517427bc649a5c7077adac.
Initial formalize pull and main fetch succeeded. Main did not change.
The preceding goal turn made progress: captured-edge completion was verified
and pushed through 705414c5a. This turn extends that actual flat execution.
The whole goal stays ACTIVE and incomplete. Preserve the optimized interned
core and every earlier proof, repair, counterexample and marked draft.
The preceding checkpoint is `notes-current-flat-captured-edge.md`.

## Target and strongest global statement

The target remains whole-system source-connected correctness, including exact
finite-tree language preservation and enumeration soundness and coverage under
explicit solver and pruning contracts. These new theorems cover actual ordinary
entry and plain ordered siblings. They do not close whole recursive enumeration.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains unchanged.
For covered closed construction and valid original guard-allocation history,
each chosen finite budget and round count has derived mathematical width and
fuels. The actual formal node calls complete. The final node remains available.
Its accepted finite trees equal the original accepted finite trees in every
ambient environment. The inherited payload is empty. This is a formal model
theorem, not end-to-end certification of the Haskell implementation.

SourcePruningEnumerationCapturedEdge.diagonal_render_sound_current is unchanged.
Actual stable captured completion, its original current admission conditions,
structural discharge, successful rendering and checked residuals derive original
edge/parent acceptance and every suspended constraint. It constructs a satisfying
assignment. It does not establish that discharge or successful rendering exists.

## Actual entry and ordered plain siblings

SourceFlatPruningEntry.enter reads the actual current pending value and root.
It decodes the same native handle. A missing decode retains the explicit error.
The native recursion boundary selects the expansion ancestry. enter_replays
reconstructs the actual flat singleton from an actual successful old singleton
at the same native heap and old lookup bound. It needs no future flat observation.
No general equality at arbitrary insufficient old lookup fuel is asserted.

SourceFlatPruningNativeBranches.run calls the actual flat captured-edge worker.
Every alternative uses the SAME captured enumeration cache. A complete edge,
arity rejection or valid raw-empty child rejection supplies the next native
Caller and Queries. Other observations stop and retain the exact optional
receipt. Processed receipts retain order and duplicates. The scan does not
pass one sibling's enumeration cache to the next sibling.

OrderedRelated compares payload lists in independent universes. ReceiptsRelated
specializes it to complete flat/earlier receipt correspondence. Caller data and
recursive outputs inhabit Type 1. The old Language.All₂ only accepts Type 0.
No earlier language definition or proof was changed to add this relation.
ResultRelated keeps all processed receipts, the optional stopping receipt and
literal final Caller/Queries when the scan completes.

## Completion and receipt invariants

SourceFlatPruningNativeBranchCompletion.complete_with_history derives the
entire old packet and actual flat family together. Its head producer handles
all arity and projection branches. Supported heads use the previously checked
flat captured-edge completion. Unsupported projection is explicit unhandled.
Arity rejection returns the unchanged cache and native endpoint.

Each continuable head gives its actual Caller, Queries, full middle Memos and
Post.context to the suffix. Native Keeps transports realization and expandable
flags for the original captured cache at that new native heap. The original
Ranges suffix implication applies to that same actual head receipt. Bounds use
sums and maxima. They precede the universal related flat cache and every adequate
native bound. Each actual flat result is existential for that run.

The full old conclusion remains available: the stable old run, full Post/global
Memos, query equality, each processed receipt's Admitted predicate, conditional
pending-reference history, every receipt's prefix postcondition and full memo
witness, fragment history, the complete-or-unhandled-stop shape and the condition
for finishing all supported alternatives. No final flat invariant is an input.
No one literal flat forest across all native bounds is inferred.

SourceFlatPruningNativeOrdinary.run retains the entire actual entry raw list.
Only an ordinary singleton with a nonterminal suspended bucket starts siblings.
Its captured cache frames the actual entered core over the original indexes.
NativeOrdinaryCompletion.complete_with_history keeps the entire old ordinary
contract. One genuine SelectedEntry.complete supplies the exact old entry.
One new branch producer supplies the coupled old/flat scan. Entry replay and
frame_related connect their actual initial caches. Full original histories,
receipt postconditions, render-stable entry and support conditions are retained.

SourceFlatPruningNativeReceiptValidity derives native index correctness from
the retained old Admitted/CacheValid witnesses and actual cache relations.
It uses each receipt's own reached Caller heap and recovered cache. The ordered
list consumer applies this fact to each related processed receipt. A valid child
rejection keeps its actual cache invariants. It does not imply Safe. No correctness
of a cache is inferred from a core relation alone.

## Hook-aware execution and its exact remaining boundary

SourceFlatPruningNativeContinuations.run invokes a completed edge's hook BEFORE
the next sibling. It threads the actual hook-returned Caller/Queries to that
sibling while restoring the same captured enumeration cache. A stopped hook
retains its emitted prefix, reason and optional endpoint. No endpoint is invented.
Missing/noncontinuable edges retain their exact receipt and do not invoke a hook.
Only completed edges invoke the hook. Valid rejections advance without a hook.

HookResult reuses the existing cache-free generic hook-result type. The existing
flat template callback continuation therefore fits directly. Output and failure
relations accept different types in independent universes. OrderedRelated keeps
output positions; native Caller/Queries and optional endpoints stay literal.
StopRelated keeps the exact stopping stage and related current receipt/reason.

SourceFlatPruningNativeOrdinaryContinuations.run retains complete entry raw and
the same ordinary/nonterminal gate. The sibling fold captures the actual entered
flat core. Identity hooks equal the plain sibling/ordinary runs for ALL inputs
and native bounds, including missing results and all stopping observations.
The equations preserve actual callback outputs and stop reasons. They do not
prove that an arbitrary supplied hook, or the concrete recursive hook, completes.

The next proof must relate actual flat recursive Output and Failure values to
their earlier representations. It must compose successful full-template callbacks
and recursive subtree execution. The next sibling starts at THAT returned native
endpoint. Plain branch Ranges follows the head endpoint before a hook; it cannot
be reused as proof of post-hook admission. The old finite-depth resource theorem
and Complete induction contract provide genuine original resource packets.
Their conclusions still require transport through these actual flat consumers.

## Verification, preservation and restart

Eight new modules contain {lines} lines and {theorems} public theorems.
Audit adds only eight imports. Every earlier proof source is unchanged.
All eight modules and Audit pass Lean 4.34.1 strict checks with warningAsError
and linter.all enabled. Each new module has empty strict compiler output.
Aggregate Audit passes {jobs} jobs and {dependencies} theorem dependency checks.
Only propext, Classical.choice and Quot.sound are permitted. No sorry, admit,
native_decide, new axiom or heartbeat increase was added. Aggregate replay retains
the earlier unused-input warning in InternedFreshOrdinaryClosedCompletion.

Installed readback covers {theorems + 2} theorem signatures/axioms, including
unchanged H6 and captured rendering, and {definitions} complete definitions.
Raw readback: {public['bytes']} bytes; SHA256 {public['sha256']}.
All heavy checks run serially with memory.max/high=4294967296 and swap=0.
Failed drafts, exact source versions, source review cuts and passing checks are
stored losslessly in `restart-evidence/20261027-flat-native-branches`.
The verifier checks the manifest, decoded archives, literal source cuts,
installed sources and every unchanged historical document byte.

No Haskell source changed. FINDINGS retains every earlier Haskell repair handoff.
Imported main still contains the LPO repair and subsequent extraction fixes.
Extraction progress and lexicographic starvation remain open. No native suite
rerun was needed for these Lean-only additions.

Next compose actual hook-aware recursive correspondence and original resource
histories. Then classify recursive outputs and prove their language soundness
and coverage. Derive initial Canonical, semantic request Ranges and allocation
histories from actual construction. Pruning-policy soundness, concrete solver
and container correspondence, machine bounds, practical resource limits and
unbounded convergence remain separate obligations. Do not mark the full goal complete.
'''
name = 'lean/notes-current-flat-native-branches.md'
path = root / name
assert not path.exists()
path.write_text(note)
data = path.read_bytes()
documents.append(name)
records.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
(area / 'document-paths.json').write_text(json.dumps(documents, indent=2) + '\n')
(area / 'document-validation.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps(dict(documents=len(documents), note_bytes=len(data), note_sha256=hashlib.sha256(data).hexdigest())))
