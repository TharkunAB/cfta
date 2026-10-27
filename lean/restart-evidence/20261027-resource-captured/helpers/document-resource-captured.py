from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-resource-captured-20261027')
head = (area / 'source-head.txt').read_text().strip()
base = (area / 'published-base.txt').read_text().strip()
aggregate = (area / 'build-aggregate-final/raw.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', aggregate).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', aggregate).group(1)
public = json.loads((area / 'public-validation.json').read_text())
assert public['status'] == 'pass'

prefix = f'''
## Captured rendering soundness now uses original finite resources

Source checkpoint: {head}.
Eight new modules lift the original resource admission through traversal,
selected edges, captured finalization and actual flat captured rendering.
The complete traversal resource packet retains all runtime and history facts.
Its completed result adds the full assignment iff and ordered effective child
restrictions. Neutralized traversal and selected-edge laws keep the same
conclusions. Original Fits, reservation and guard carrier replace universal
numeric Ranges. Canonical, nonterminal, fresh arity and retention stay explicit.

The flat captured result derives one sufficient bound before its related flat
input. An ACTUAL completed receipt supplies its own reached heap and cache.
Original Stratified dependency order, discharge, actual rendering and checked
residuals construct an assignment and prove acceptance at the original captured
edge and parent. No desired
assignment, old render or future stable completed family is an input.
This result covers one captured step. Whole recursive-input acceptance and
enumeration coverage still need backward history and parked-constraint recovery.

H6 remains the strongest global exact finite-tree construction result.
Audit passes {jobs} jobs and {dependencies} theorem dependency checks.
All eight modules and Audit pass strict checking. No Haskell source changed.
FINDINGS retains all earlier Haskell repair handoffs and extraction limits.
Details: `lean/notes-current-resource-captured.md`. The full goal stays ACTIVE.

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

note = f'''# Captured language soundness from original finite resources

Source checkpoint: {head}.
Published base: {base}.
Imported main: 82258094c2c32bb93e517427bc649a5c7077adac.
The formalize pull and main fetch succeeded. Main did not change.
The preceding checkpoint added actual flat captured rendering, exact native
narrowing and recursion parking laws, and resource-based traversal semantics.
Its note is notes-current-recursive-meaning.md. The full goal stays ACTIVE.
Keep the optimized interned core and all earlier proofs, repairs,
counterexamples, proposals and marked drafts.

## Target and strongest current claims

The target remains whole-system source-connected correctness. It includes
exact finite-tree language preservation and enumeration soundness and coverage
under explicit solver and pruning contracts. This checkpoint does not close it.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
global exact finite-tree language result. Covered closed construction and a
valid original guard-allocation history derive mathematical width and fuels
for each finite budget and round count. The actual formal calls complete.
The final node stays available and accepts exactly the original finite trees
in every ambient environment. Its inherited payload is empty.

The new local claim covers an ACTUAL completed flat captured edge at a bound
derived from original finite resource admission. Original Stratified dependency
order, discharge, actual rendering at that receipt's reached heap and successful
checks of its returned residuals
produce a term accepted by the original captured edge and parent node.
The theorem also constructs an assignment for the original flat input.
It uses no old render or desired assignment premise. It has no universal
numeric Ranges premise. Canonical suspended constraints, nonterminal inherited
constraints, projected arity and child retention remain explicit gates.

This is a single captured-step result. The assignment belongs to that step's
own completed cache. A later recursive output can have a different cache and
heap. Backward transport through that whole history remains necessary.

## Traversal resource packets and exact assignment meaning

SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources_semantics
retains the ENTIRE complete_with_fragments_resources contract. It calls that
producer once. The same result supplies runtime bounds, exact Caller and full
Memos, query equality, roots, storage, pending realization, waiting counts,
native index flags, origin, protected slots, reference histories, fragment
bounds, complete-or-stopped shape, returned Fits and returned guard carrier.
Completed results append the old exact assignment iff and ordered effective
child restrictions. Stopped results retain the full original packet.

SourcePruningEnumerationTraversalCompletion.stable_complete_neutral_semantics_resources
proves the old exact neutralized assignment iff from the original seed, Fits,
finite reservation for cost inputs and guard carrier Heap. The mathematical
width is bits + 2. The complete old conclusion is unchanged. It includes the
same held-slot inside/root/Avoids gates and arbitrary residualMeaning.
No universal traversal Ranges is assumed.

Each actual head resource producer supplies a concrete initial_ranges fact.
Its returned Post, full Memos, singleton Safe, Fits and carrier feed the suffix.
The reservation splits at bucket.length + 1. The actual Protected receipt
transports the same held root and avoidance conditions. Cache growth supplies
the suffix bound for that held variable. The proof does not derive Safe from
Protected, or assume validity of every low-fuel successful prefix.

## Selected-edge and captured-slot meaning

SourcePruningEnumerationSelectedEdge.stable_complete_semantics_resources
and stable_complete_neutral_semantics_resources retain their entire old
assignment iff conclusions. The own-class prefix changes the enumeration
cache and supplies its actual child inputs. The same Caller, Fits and guard
carrier remain valid. The reserved selected cost is the actual traversal cost.
The full traversal resource producer is called once at this own-prefix cache.

Common sufficient bounds align the actual stable edge with that canonical
traversal result. A stopped traversal contradicts an actual completed family.
The complete case retains the exact child fragments, Caller, queries, cache,
effective child restrictions and residual at the actual returned fragment.
The neutral version protects the held root through the own prefix and suffix.

SourcePruningEnumerationSelectedEdge.stable_complete_neutral_sound_current_resources
uses that runtime equivalence to prove native selected-edge and parent-node
acceptance. The original guard projection law supplies native guard meaning.
Child-retention, valid inherited constraints, nonterminal inherited constraints,
allowed arity and fresh projected arity supply the equality restrictions.
The original annotation invariant comes from Context. These gates remain
separate from resource admission. No stronger full-bucket claim is added.

SourcePruningEnumerationCapturedEdge.stable_complete_sound_current_resources
retains the entire old captured conclusion. An assignment for the actual
completed cache implies an assignment for the original cache, original edge
and parent acceptance, every inherited suspended constraint, and the captured
fragment equation. Canonical supplies valid inherited constraints at the
actual stored variable. Ready supplies its bound and avoidance facts.

The selected producer supplies the actual protected captured slot. The actual
finalizer writes its produced fragment. Common independent resource bounds
identify those endpoints with the supplied stable completed family. Neutral
soundness then restores the original captured slot with its native handle and
original suspended constraints. The stopped case contradicts actual completion.
Intermediate stable consumers retain their actual stable observation premise.
The flat results below derive that observation from the resource producer.

## Actual flat completion and rendering

SourceFlatPruningCapturedEdge.complete_sound_current_resources calls the full
SourceFlatPruningCapturedResources.complete_with_history_resources producer.
That original resource producer derives the earlier stable result, full
history packet, returned Fits and guard carrier, and flat correspondence.
Its bounds are fixed before any related flat input is supplied.

The sum r + n + p + h + k supplies one sufficient work bound. At that bound
plus any extra, an ACTUAL completed flat receipt identifies the same earlier
complete result. Fragment, Caller and Queries agree. The reached flat cache
relates to that exact earlier endpoint. The complete packet supplies Safe and
dependency-order transport. A stopped result contradicts the completed receipt.
The native captured resource law restores the original assignment and proves
edge, parent, inherited constraints and fill. related_satisfies transports both
literal endpoint caches. No future completed family is a public input here.

SourceFlatPruningCapturedEdge.render_sound_current_resources then uses explicit
original Stratified dependency order, Discharged, ACTUAL flat rendering at that
same reached heap and checks of every actual returned residual. The original
order is an explicit premise. The completion packet transports that order.
render_assignment constructs the assignment at the
completed cache. The backward law proves original captured-edge and parent
acceptance of the rendered term. It also retains original, completed and
rendered assignments, the fragment equation and exact unchanged rendered core.
It assumes neither an old successful render nor a desired assignment.

The sufficient bound guarantees the correspondence for an actual completed
receipt. It does not force every admitted edge to return complete rather than
stopped. Rendering existence and Discharged are not automatic consequences.

## Verification and preserved findings

Eight new modules contain 1194 lines and eight public theorems. Audit adds
only eight imports. All eight modules and Audit pass Lean 4.34.1 with
warningAsError and linter.all. Every new module has empty strict output.
Aggregate Audit passes {jobs} jobs and {dependencies} theorem dependency checks.
The recorded dependency warning in InternedFreshOrdinaryClosedCompletion is
unchanged. Every heavy check runs serially with memory.max/high=4294967296
and memory.swap.max=0.

Installed readback covers 12 full theorem signatures and axiom lists.
The new eight theorems use only propext, Classical.choice and Quot.sound.
Four earlier signatures compare byte-identical to the previous readback.
They are H6, the earlier native captured renderer and both earlier actual
flat captured results. No proof hole, new axiom, native_decide, heartbeat
increase or signature elision is present. Readback has {public['bytes']} bytes.
SHA256: {public['sha256']}.

All installed proposals pass their first strict check without source changes.
The initial traversal packet proposal and its namespace-open revision remain
preserved. One check command used a nonexistent module name and failed before
Lean. The corrected command passed. A local token scan matched the English
word admit in a comment. The scan now checks code outside comments. Readback
comparison also needed the actual earlier log path and signatures with same-line
binders. These evidence-helper fixes did not change any theorem source.

Every older proof source stays unchanged. Existing H6 and captured-rendering
sources retain their checked identities. Every earlier document byte stays
below the new status region. No Haskell source changed. FINDINGS retains all
earlier Haskell repair handoffs, the integrated LPO fix and extraction progress
limits. This checkpoint establishes no new Haskell defect. Native tests were
not rerun for these Lean-only additions.

Independent exact-source reviews cover the selected edge, neutral traversal,
captured restoration and flat renderer. The claim review checks this note and
the public signatures. Raw receipts, source copies, literal cuts, old and new
contracts, proposals, reviews and helper scripts are stored in
restart-evidence/20261027-resource-captured. Its portable verifier checks hashes,
cuts, document retention, installed sources and committed evidence bytes.

## Remaining work and next proof

Compose the actual selected prefixes, callback siblings and recursive branches
backward to the original recursive input. Use the original finite execution
packet and its own resource and history certificates. Do not add successful
future execution or desired assignment as original producer premises.

The repeated recursion check clears its stored bucket while retaining its
native handle. The existing exact assignment law requires every cleared
constraint to recover the original assignment. An ancestry key alone does not
prove those constraints. Derive a genuine semantic ancestry/history law or
prove that the relevant completed finite output excludes this branch.

Derive initial Canonical, projected arity and retention histories where needed.
Connect the current native narrowing inclusion theorem through those same
actual histories. State pruning coverage contracts. Prove original recursive
root acceptance and enumeration coverage. Done does not imply Discharged.
Native recursive boundaries can remain pending. Complete search depth,
unbounded convergence, physical Haskell containers, concrete solver behavior,
machine bounds and practical resource limits remain separate obligations.
Do not mark the full goal complete.
'''
name = 'lean/notes-current-resource-captured.md'
data = note.encode()
(root / name).write_bytes(data)
documents.append(name)
records.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
(area / 'document-paths.json').write_text(json.dumps(documents, indent=2) + '\n')
(area / 'document-validation.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps({'documents': len(documents), 'note_bytes': len(data), 'note_sha256': hashlib.sha256(data).hexdigest()}))
