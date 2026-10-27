from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-flat-captured-edge-20261027')
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
## Actual flat captured edges now derive completion and full native history

Source checkpoint: {head}.
Fourteen new modules execute own-class allocation, child dispatch, ordered
child traversal, residual recording and captured-slot finalization.
Original admission derives actual flat completion at every adequate native
bound, for any related initial flat cache. The full earlier packet remains
available. The result is a completed edge or the first valid child rejection.
It retains the same reached Caller, saved Queries and full Post/global Memos.
Every returned cache has correct native indexes at that same reached heap.
Completion writes the original captured raw slot and resets expansion ancestry.
Rejection retains its full stopping observation and does not assert Safe.
No future flat observation or final flat invariant is an input.

H6 remains the strongest global finite-tree language theorem. Captured
rendering retains its original admission, discharge and rendering gates.
Whole recursive enumeration, sibling composition, output soundness, coverage,
pruning-policy soundness and initial admission histories remain open.
Audit passes {jobs} jobs and {dependencies} theorem dependency checks.
All fourteen modules and Audit pass strict checks. No Haskell source changed.
FINDINGS retains all Haskell repair handoffs and the extraction-progress limit.

Next transport ordinary siblings and the recursive worker through these same
native histories. Restore the captured enumeration cache for each sibling;
advance the actual native Caller and full Memos. Derive initial Canonical,
semantic Ranges and allocation bounds. Details: `lean/notes-current-flat-captured-edge.md`.

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

note = f'''# Actual flat captured-edge completion

Source checkpoint: {head}.
Published base: {base}.
Imported main: 82258094c2c32bb93e517427bc649a5c7077adac.
The initial formalize pull and main fetch succeeded. Main did not change.
The whole formalization goal stays ACTIVE and incomplete. Keep the optimized
interned core and every previous proof, repair, counterexample and marked draft.
The previous checkpoint is `notes-current-flat-selected-prefix.md`.

## Target and strongest global result

The target is a source-connected correctness argument for the whole system.
It must preserve the original finite-tree language and justify enumeration
outputs and coverage under explicit solver and pruning contracts.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls stays unchanged.
For covered closed construction and valid original guard-allocation history,
any chosen finite budget and round count have derived mathematical width and
fuels. Those actual formal node calls complete. The final node remains available.
Its finite-tree language equals the original language in every ambient environment.
The inherited payload is empty. This result does not certify all Haskell APIs.

SourcePruningEnumerationCapturedEdge.diagonal_render_sound_current also stays
unchanged. Actual stable captured completion, its current admission conditions,
structural discharge, successful rendering and checked residuals derive original
edge and parent acceptance and every suspended constraint. It constructs a
satisfying assignment. It does not prove that discharge or rendering exists.

## Actual flat operations

SourceFlatPruningShallowChild allocates a fresh raw slot and preserves the
actual expansion ancestry. Empty rejects. Reference has no shallow action.
Ordinary nodes write the suspended bucket. Recursive boundaries allocate an
empty bucket. OptionalActions compares every ordered raw result at related cores.

SourceFlatPruningCachedChild classifies the pending native value at the same
heap as the old operation. Allocation increments the counter once. A true
classification sets the fresh expandable flag. A false classification retains
the old flag function. No unstated false-at-fresh invariant is used.
Slot writes remove references from the actual current stored value.
SourceFlatPruningCachedPrepare retains Empty rejection, absent preparation,
and ordered prepared rows. The completed lemma uses an actual old Some receipt
at the same count fuel. The erase lemma identifies the raw action rows from an
actual flat Some receipt. No equality at arbitrary insufficient fuel is asserted.

SourceFlatPruningCachedOwn allocates one suspension per own trie in list order.
It keeps the exact arity and projection branches. Some empty preparation remains
different from absent preparation. StageRelated retains each native value,
bucket and optional shallow action. OwnObservation derives the actual flat
singleton preparation and equality of the projected child-input list.

SourceFlatPruningChildDispatch executes Empty, nonterminal preparation or the
actual native terminal path. It keeps raw diagnostics and optional recovery
separate. It retains Caller, Queries, outer core and moved waiting counts.
SourceFlatPruningChildTraversal continues only after one successful raw row
and an actual recovered cache. It passes that cache and the reached Caller and
Queries to the suffix. It retains every other observation as the first stop.
It does not equate the raw row core, outer core and recovered cache core.

SourceFlatPruningSelectedEdge executes actual own preparation and traversal.
Only complete children build the parent fragment and record its residual.
SourceFlatPruningCapturedEdge then finalizes the original captured raw slot.
It uses the same reached native heap. Finalization resets expansion ancestry,
reads the actual current raw slot and removes that value's references.
A missing raw target still returns None. A stopped child never finalizes.

## Completion from original admission

SourceFlatPruningChildCompletion.complete_with_fragments retains the entire
old child packet from one old producer. It appends actual flat observations.
The stable-observation helper derives terminal-prefix completion from the
original Safe, roots, counts, realized pending inputs and bucket bounds.
It aligns that prefix with the old child family at larger representative bounds.
It then uses the existing flat native terminal observation theorem.
The helper's stable old observation premise is discharged by the old producer.

SourceFlatPruningTraversalCompletion.complete_with_fragments derives the old
packet and actual flat family together by ordered induction. Each successful
old child supplies the actual suffix admission. Its Post.context carries the
full middle Memos into that suffix. At each fixed native bound, the actual
returned flat cache supplies the suffix input. Rejection stops before a suffix runs.

SourceFlatPruningSelectedCompletion.complete_with_fragments uses the original
own-input producer and that coupled traversal producer. It retains every old
result, history and separation predicate. Actual flat own preparation supplies
the related initial child cache. Complete and stopped cases retain the same
native endpoints. Only the complete case adds the residual.

SourceFlatPruningCapturedCompletion.complete_with_history calls the original
captured producer once. A genuine selected completion supplies correspondence.
Representative, native and count bounds use sums; numeric thresholds use maxima.
At those common bounds, the selected result is the actual old selected execution
used by the retained captured observation. run_completed therefore transports
that same finalizer. The proof does not identify independently chosen caches.

The final theorem retains the entire original captured conclusion, including
full native Post, final global Memos, saved-query equality, growth, roots,
storage alignment, realized pending state, both indexes, origin and reference
history, protected classes and the complete-or-rejected shape. Complete results
also retain the original captured-slot write, Safe, fragment bounds, pending
fragment and stratified step. Rejection does not imply Safe.

For every related initial flat cache and every adequate native bound, the
actual flat run returns a related result with the same native endpoints.
Its recovered cache has correct native indexes at that actual reached heap.
Bounds precede the universal flat input. Returned flat caches are existential
per run. No one literal forest across all native fuels is asserted.
No future flat observation or desired final invariant is an input.

## Verification and preservation

Fourteen new modules contain {lines} lines and {theorems} public theorems.
Audit adds only fourteen imports. Previous proof source is unchanged.
Each module passes Lean 4.34.1 with warningAsError=true and linter.all=true,
with empty compiler output. Audit also passes the strict check.
Aggregate Audit passes {jobs} jobs and {dependencies} theorem dependency checks.
Only propext, Classical.choice and Quot.sound are permitted.
No sorry, admit, native_decide, project axiom or heartbeat increase was added.
Aggregate replay retains the earlier unused-input warning in
InternedFreshOrdinaryClosedCompletion. Each new module's strict output is empty.

Installed readback covers {theorems + 2} public theorem signatures and axioms,
including unchanged H6 and captured rendering, plus {definitions} complete definitions.
Its raw log has {public['bytes']} bytes and SHA256 {public['sha256']}.
Every heavy check runs serially under memory.max/high=4294967296 and swap=0.
Failed draft checks, exact source versions, review cuts and final checks are
retained losslessly in `restart-evidence/20261027-flat-captured-edge`.
The evidence verifier checks manifests, decoded bytes, review source cuts,
installed sources and unchanged historical document bytes.

## Haskell handoff and remaining work

No Haskell source changed in this checkpoint. Root FINDINGS retains every
previous Haskell repair and its evidence. The imported main contains the LPO
repair and the later extraction fixes. Extraction progress and lexicographic
starvation remain open. Do not mark that progress issue fixed by a documentation change.
No native suite rerun was needed for these Lean-only additions.

Next add actual ordinary-sibling traversal. Each sibling must restore the
captured enumeration cache and thread the reached native Caller and full Memos.
Then compose the complete recursive worker and classify its actual outputs.
Derive initial Canonical, semantic request Ranges and allocation bounds from
real construction histories. Prove pruning-policy soundness and enumeration
coverage. Concrete solver and container correspondence, machine bounds,
practical resource limits and unbounded convergence remain separate obligations.
Finite covered completion is not whole-system termination or completeness.
'''
name = 'lean/notes-current-flat-captured-edge.md'
path = root / name
assert not path.exists()
path.write_text(note)
data = path.read_bytes()
documents.append(name)
records.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
(area / 'document-paths.json').write_text(json.dumps(documents, indent=2) + '\n')
(area / 'document-validation.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps(dict(documents=len(documents), note_bytes=len(data), note_sha256=hashlib.sha256(data).hexdigest())))
