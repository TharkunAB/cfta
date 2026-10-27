from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-recursive-output-20261027')
head = (area / 'source-head.txt').read_text().strip()
base = (area / 'published-base.txt').read_text().strip()
aggregate = (area / 'build-aggregate/raw.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', aggregate).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', aggregate).group(1)
public = json.loads((area / 'public-validation.json').read_text())
assert public['status'] == 'pass'

prefix = f'''
## Actual recursive outputs now retain their own invariants and frontier

Source checkpoint: {head}.
Nine new modules certify every emitted flat output, including outputs before
a later stopped branch. The original finite-depth admission derives one
uniform work bound, the same stable old result and its full OutcomeResources.
Each actual output has its own related safe ordered packet, full Post/Memos,
native index correctness at its own heap, resource bounds and actual origin.
The origin theorem also holds at every finite fuel without admission gates.

User-stopped outputs retain the rule that accepted every remaining candidate.
Done outputs have no candidates. Their native pending slots can still contain
recursive boundaries with empty suspended buckets. Done does not imply
Discharged. A checked initial-slot family records this exact boundary.
It is conditional on an actual decoded available closed recursive value.
It does not supply a full source Context or allocation history.

The actual flat native renderer and its complete successful replay are checked.
At an emitted output's own heap, Discharged, actual successful flat rendering
and checked residuals construct a full satisfying assignment for that output.
The entire flat core is unchanged. No successful old render is assumed.
Transport back to the original input language and coverage remain open.
H6 and the earlier conditional captured-rendering theorem stay unchanged.
Audit passes {jobs} jobs and {dependencies} theorem dependency checks.
All nine modules and Audit pass strict checks. No Haskell source changed.
FINDINGS retains every Haskell repair handoff and the extraction-progress limit.

Next preserve assignment meaning through actual recursive steps and callbacks.
Derive the semantic admission histories and state the pruning-policy contract.
Details: `lean/notes-current-recursive-outputs.md`. The full goal stays ACTIVE.

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

note = f'''# Invariants, frontier and rendering at actual recursive outputs

Source checkpoint: {head}.
Published base: {base}.
Imported main: 82258094c2c32bb93e517427bc649a5c7077adac.
The initial formalize pull and main fetch succeeded. Main did not change.
The preceding goal turn made progress. It closed finite-depth flat recursive
execution correspondence and pushed through f92da69a8. The preceding note is
`notes-current-flat-recursive.md`. This turn certifies actual emitted outputs
and constructs their assignments under the explicit rendering conditions.
The full goal stays ACTIVE and incomplete. Preserve the optimized interned
core and every earlier proof, repair, counterexample and marked draft.

## Strongest statements and remaining semantic boundary

The target remains whole-system source-connected correctness. It includes
exact finite-tree language preservation and enumeration soundness and coverage
under explicit solver and pruning contracts.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains unchanged.
For covered closed construction and a valid original guard-allocation history,
each chosen finite budget and round count has derived mathematical width and
fuels. The actual formal node calls complete. The final node remains available.
Its accepted finite trees equal the original accepted finite trees in every
ambient environment. The inherited payload is empty. This is the strongest
global finite-tree language result. Whole Haskell certification remains open.

SourcePruningEnumerationCapturedEdge.diagonal_render_sound_current remains
unchanged. Its actual stable captured completion, original admission,
structural discharge, successful rendering and residual checks construct a
satisfying assignment and derive original edge/parent acceptance and all
suspended constraints. It does not derive existence of discharge or rendering.

The preceding finite-depth correspondence now has an output certificate.
SourceFlatPruningRecursive.run_finite_complete_output_certificates retains
all original inputs: Packet at the full native Memos, Fits, guard carrier,
selector membership and length laws, suspended-mass ceiling and original
finite reservation. One uniform work bound and stable old result precede
every related flat input. Every larger work bound gives an actual related
flat result. The entire old OutcomeResources packet remains available.
Every emitted flat output also has OutputResources and OutputOrigin.
This includes the output prefix of a later stopped result.

OutputResources belongs to THAT output's actual Caller and cache. It retains
the full native Post/Memos, query equality, related original Packet, metadata
shape, native index correctness at that output's heap, Fits and guard carrier.
output_state exposes logical slot and obligation bounds, live-root tests and
class-consistent dependency levels. It does not infer a physical address
bound on every explicitly stored flat-map entry. Related alone does not give
that bound. The original Safe and Stratified witnesses remain available for
semantic consumers at the related old core.

The new output_render_assignment constructs an assignment at the output's
OWN native heap. Its extra conditions are explicit flat Discharged, an ACTUAL
successful flat render and checks of those actual returned residuals. The
result satisfies the output state, gives rendered term = assignment uv and
retains the exact whole flat core. It assumes no successful old render and
no desired assignment or accepted term. It does not yet transport that
assignment through the whole recursive trace to the original input language.
That transport and coverage remain the largest semantic tasks.

## Exact output origin and pending frontier

run_output_origin applies at ALL finite work and recursive fuels. It needs no
native admission, correctness, canonicality or future execution condition.
For an output with metadata, its actual cached restart decision is none.
decision_none_iff supplies the explicit stop rule, a nonempty complete
candidate list and acceptance by that rule of every candidate, including
blocked candidates. For an output without metadata, candidates are empty.
An arbitrary preference cannot produce done from nonempty candidates.
Stuck has candidates and no unblocked candidate. It is a separate decision.

OutputFlow proves output-property transport through the actual callback,
native sibling fold and ordinary wrapper. Both complete and stopped lists
are included. The callback invokes the actual restart continuation. Siblings
run at the actual post-hook Caller/Queries and retain the captured enumeration
cache. The proof does not substitute an identity hook.

RecursiveOutputOrigin derives the actual parked singleton decision at the
same framed core passed to recursion. It then uses recursive-fuel induction
through every runtime route. Its public run theorem supplies the actual
initial decision itself. No smaller-depth completion premise remains.

OutputFrontier derives the native pending frontier from empty candidates,
the genuine same-heap NativeIndex.Correct and related pending realization.
Each graph-bearing pending slot decodes to an available closed recursive
boundary with an empty suspended bucket. Pure equality slots can still carry
constraints. Discharged additionally excludes every pending native handle
and requires every pure equality bucket to be empty.

recursive_initial_counterexample records a concrete initial-slot family.
It has Related, native Correct, pending realization and done while failing
Discharged. It is parameterized by an ACTUAL decoded available closed native
recursive boundary. It does not establish a complete source Context or a
construction/allocation history for that family. This prevents a false
done-to-discharge inference. It establishes no new Haskell repair.

## Actual native rendering and assignment construction

SourceFlatPruningRendering defines expandFragment, expandUVar and render
with direct representative reads and actual native handle lookup. Structural
fuel remains explicit. Fragment fuel exhaustion, unresolved handles, root
rejection, unfinished fragments and recursive markers follow the old renderer.
All residuals are rendered in their original order at the same reached heap.
The renderer does not execute the old evaluator.

RenderingReplay proves complete replay of every successful old root and
residual trace from related input cores. It retains the same term and ordered
residuals. This one-way successful replay does not claim arbitrary low-old-fuel
diagnostic equivalence or that an old successful render exists.

RenderingAssignment constructs an assignment from the original Safe and
Stratified witnesses and explicit flat Discharged. Related cores transfer
the resulting forest and stored-fragment equations. Direct-root read soundness
then identifies the root term and each residual term from the ACTUAL flat
rendering observation. Checked residuals complete the Satisfies predicate.
All successful rendering reads retain the exact flat state. The output
consumer extracts those same safe ordered witnesses from its own packet.

## Verification and preservation

Nine new modules contain 1352 lines and 29 public theorems. Audit adds only
nine imports. Every earlier proof source is unchanged. All nine modules and
Audit pass Lean 4.34.1 with warningAsError and linter.all. Every new module has
empty strict compiler output. Aggregate Audit passes {jobs} jobs and
{dependencies} theorem dependency checks. Aggregate replay retains the earlier
unused-input warning in InternedFreshOrdinaryClosedCompletion.

Installed readback covers 31 full theorem signatures and axiom lists, including
unchanged H6 and captured rendering, and eight definitions. Only propext,
Classical.choice and Quot.sound occur. No elision, sorry, admit, native_decide,
new axiom or heartbeat increase was added. Raw readback has {public['bytes']} bytes.
SHA256: {public['sha256']}.
All heavy checks run serially with memory.max/high=4294967296 and swap=0.

Failed strict inputs and actual reports remain in
`restart-evidence/20261027-recursive-output`. Initial failures concerned
explicit observation/binder types, retained lookup equations, let/match
simplification and strict instance/tactic linters. The resource proof uses
the existing typed hookOutputs projection rather than duplicate inline
dependent matches. No admission condition was weakened to make a proof pass.
The archive also retains original proposals, revised proposals, focused
source cuts, final installed sources, source commits and historical document
bytes. Its portable verifier checks hashes, decoded archives, literal cuts,
current sources and all preserved earlier document bytes.

No Haskell source changed. FINDINGS retains every earlier Haskell repair
handoff for external work and the open extraction-progress/starvation limit.
Main already contains the LPO repair and later extraction fixes. Native tests
were not rerun for these Lean-only additions.

## Next work

Prove assignment preservation back through actual selected prefixes, completed
edges, callbacks and recursive branches. Use the existing captured-edge
soundness theorem only with its genuine Canonical, numeric Ranges, fresh-arity
and retention gates. Derive those initial facts from construction and actual
allocation histories. State which pruning rules can discard an assignment
and which user stops return partial states. Keep stop output semantics and
recursive truncation explicit.

Then prove original-root acceptance of actual rendered completed results and
coverage under the intended policy. Establish discharge or an appropriate
semantic treatment of recursive boundaries where required. Rendering
existence, complete search depth, unbounded convergence, physical Haskell
containers, concrete solver behavior, machine bounds and practical resource
limits remain separate obligations. Do not mark the full goal complete.
'''
name = 'lean/notes-current-recursive-outputs.md'
path = root / name
assert not path.exists()
path.write_text(note)
data = path.read_bytes()
documents.append(name)
records.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
(area / 'document-paths.json').write_text(json.dumps(documents, indent=2) + '\n')
(area / 'document-validation.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps(dict(documents=len(documents), note_bytes=len(data), note_sha256=hashlib.sha256(data).hexdigest())))
