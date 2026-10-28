from pathlib import Path
import hashlib,json
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-render-coverage-20261028')
head=(area/'source-head.txt').read_text().strip();base=(area/'published-base.txt').read_text().strip();public=json.loads((area/'public-validation.json').read_text());assert public['status']=='pass'
common=f'''
## Constructive native rendering with exact original residual checks

Source checkpoint: {head}.
SourcePruningEnumerationRendering.render_complete_models fixes a bound, term, residual list and
final state BEFORE all semantic assignments. Safe, stratified, discharged
storage with a graph-bearing root and graph-bearing stored references gives
an actual successful native render at every larger bound. Every original
satisfying assignment gives that SAME root term and exact original-obligation
residual list. Each returned residual check holds. The full compression frame,
stored state and dependency levels remain. No future render or checked result
is an input to this producer.

ResourceHistory.render_complete_models attaches this result to the SAME
actual output packet, caller heap and cache. Its output-state discharge and
carrier conditions remain explicit. Literal native startup derives root and
reference carriers. Actual shallow and cached child preparation preserve them,
including Mu and Union children. Full recursive history preservation is open.

The checked free_hole_counterexample shows why carriers are necessary. A safe,
canonical, proper, stratified and discharged core can have a graph-bearing
root with an unrenderable free hole. It is an internal-state counterexample.
It does not establish a reachable public Haskell failure or a full Packet.
FINDINGS records this distinction and the prior integrated LPO/KBO repairs.

This closes native rendering existence and exact residual satisfaction under
those structural conditions. It does not prove that every permitted accepted
term reaches a discharged output. Preserve carriers and the chosen original
model through terminal merging and every recursive path. Then prove depth,
stop, frontier, projection and parked-constraint coverage. Public encoding
origins, public APIs, ranking, sampling and physical Haskell correspondence
remain open. Earlier finite pruning preservation, output soundness and the
accepted-head callback theorem retain their scope. Goal ACTIVE.

Eight modules add 15 public theorems. Strict checks and full Audit pass:
4305 jobs and 80372 theorem dependencies. Public readback preserves all
253 prior theorem blocks and five definitions as the exact 1055726-byte
prefix. All 4296 old non-Audit Lean sources, 145 pinned strong modules and
810 tracked Haskell source/evidence files retain bytes. Haskell is unchanged.
Details: `lean/notes-current-native-render-coverage.md`.

'''
findings='''### Haskell rendering and repair handoff

No new public Haskell defect or fix was established. Enumeration.hs uses
expandTermFragWith for nested complete fragments. It raises an error for a
nonrecursive unenumerated hole. expandUVarWith rejects an unfinished
nonrecursive root. The checked two-slot Lean witness proves that the current
storage invariants alone do not exclude such an internal hole. It does not
prove that public native enumeration can reach that state.

The missing formal obligation is graph-carrier preservation through actual
terminal merging and complete recursive histories. Startup and native child
preparation now establish the first steps. The original Haskell code is
unchanged. No Haskell or Cabal edit, Haskell test or benchmark occurred.
The integrated LPO and KBO Natural-weight repair status and their previous
executed witnesses remain below for external review.

'''
note=f'''# Constructive native render coverage

Source checkpoint: {head}.
Published base: {base}.
Main remains d1ca06a1dd0c7488205feda613b529df21a08669.
Previous note: `notes-current-accepted-head-policy.md`.

## Full objective and strongest new claim

The objective remains whole-CFTA correctness. Preserve the optimized interned
core, older constructor and equality work, counterexamples, repairs, drafts
and frozen evidence. The objective includes transformation correctness,
enumeration soundness and coverage, public APIs, ranking, sampling and
physical Haskell correspondence. This checkpoint is PROGRESS. Goal ACTIVE.

SourcePruningEnumerationRendering.render_complete_models now constructs an actual native render
from ORIGINAL Safe, Stratified and Discharged storage, ReferencesCarry and a
CarriesGraph root. It chooses bound, term, residual list and final state before
EVERY language, guard meaning and assignment. At each bound + extra, the same
actual render succeeds with the same result and state. RenderStable, full
Frame and the same dependency levels remain.

For any original satisfying assignment, the chosen term equals its value at
the root. The residual list is exactly the map of ORIGINAL obligations through
that assignment. Every returned residual check therefore holds. The same
assignment satisfies the final state. No future render, successful check,
final-state assignment or model-selected operational witness is an admission.

ResourceHistory.render_complete_models uses the actual final history tag's
own packet. The result retains full final Inventory, Memos and Metadata with
that packet before rendering witnesses. Safe and dependency levels come from
the packet. Rendering uses the SAME output.caller heap and output.cache.
Discharged, ReferencesCarry and the root carrier remain explicit conditions
on this output state. This theorem does not derive them from every history.

## Carrier origin and exact scope

GraphValue means a stored graph restriction or completed fragment.
CarriesGraph says that a variable's equality class contains such a value.
FragmentCarries applies this to every fragment hole. ReferencesCarry applies
it to every stored enumerated fragment and retained residual. These four
predicates already existed. Public readback now prints their full definitions.
No new carrier predicate or alternative native runtime is introduced.

initial_packet_carriers retains the ENTIRE original 1350-byte startup
declaration after theorem rename, grouping and the added carrier observer.
The original producer is called once. Its original Context, Available, closed
root and empty metadata conditions derive the literal startup packet, indexes,
stored root and mass bound. That literal root supplies CarriesGraph at zero.
There are no stored fragment or residual holes at startup.

ShallowChild.prepared_carriers follows the actual preparation action and its
successful row. The fresh slot stores SOME native handle before its hole is
returned. The ordinary branch retains that handle while attaching inherited
constraints. Mu and Union retain their handle with an empty suspended bucket.
Every old carrier and stored reference remains. CachedPrepare.rows_carriers
uses the actual erase_some equation to transfer the same facts to each actual
cached row. No separately assumed final carrier is used.

These are real origin and local preservation steps. They do not prove the
carrier invariant through every native terminal union, assimilation, incoming
winner, child traversal, selected head or recursive history. Those steps remain
the next necessary work. Existing proper storage and safe roots do not imply
this semantic provenance invariant.

## Actual rendering proof

The public expandFragment_bridge and expandUVar_bridge equate SUCCESSFUL
native and generic traces under original union-find Total and Discharged.
They preserve exact fuel, term and full final state. Pending graph-handle
branches are impossible under Discharged. These bridges do not equate all raw
error lists and do not assert graph-language correspondence.

A private constant-empty graph instantiates existing generic finite rendering
lemmas. It has CompleteGraph by constructor cases. Discharged proves Finished
for ANY graph. The original native carrier predicates supply reference
provenance. The private graph supplies no native acceptance fact, carrier
assumption or public graph admission. The proved bridge transfers the exact
constructed success to the actual native renderer.

The completion laws construct root and every residual at a common finite
bound. The three native fuel laws retain the exact result and full final state
at every larger bound. render_model observes a given actual render under the
SAME original assignment. Its four private invariant/soundness declarations
copy 5509 bytes of existing proof text exactly. They contain no runtime
evaluator. They avoid an additional private-name macro dependency and retain
the stronger Total-only observer. There is no new Safe or carrier gate on
this semantic observer.

The combined producer obtains rendering first. A constructively obtained
trivial-language assignment supplies unconditional Frame from the same actual
render. Every genuine original model then supplies the exact root, exact
residual map, all checks and final satisfaction. Operational witnesses precede
all semantic models.

## Checked counterexample and Haskell assessment

free_hole_counterexample constructs a two-slot core. Slot zero is an enumerated
node with a hole at slot one. Slot one is a free equality variable with no
graph restriction. The core is Safe, Canonical, ProperState, Stratified and
Discharged. It has satisfying assignments and a root carrier. The referenced
free hole has no carrier; ReferencesCarry is false. No fuel, heap or marker
can make the actual native render succeed.

The proof gives the free hole two different terms. Both assignments satisfy
the original core. The checked render_model theorem would make any successful
root equal both distinct assigned terms, which is impossible. This avoids an
unbounded low-level evaluator computation and proves failure for EVERY fuel.
Earlier untested low-level drafts are retained as such.

This is an internal-state counterexample, not a full Packet, public startup
history or public Haskell counterexample. Haskell expandTermFragWith raises an
error on a nonrecursive unfinished nested hole; expandUVarWith rejects an
unfinished nonrecursive root. Proving those cases unreachable on the covered
native history needs the carrier invariant. No new Haskell patch is established.
No Haskell/Cabal file changed. No Haskell test or benchmark ran.
FINDINGS records this assessment and retains integrated LPO/KBO repair status
and prior executed witnesses for external review.

## Remaining whole-system gap

The largest gap remains full recursive accepted-output coverage. Preserve
root and reference carriers through actual terminal merging, assimilation,
incoming writes, traversal, residual recording and captured finalization.
Carry them through the SAME ResourceHistory tails. Then the new rendering
producer removes the former assumed successful render and residual checks
from the final coverage step.

Keep the chosen ORIGINAL accepted term and satisfying assignment through
selected, ordinary, parked and callback paths. The preceding accepted-head
theorem already derives callback non-rejection under original pending
refutation, template avoidance and source encoding. Public encoding and initial
pending-policy origins remain necessary. Native acceptance alone does not
supply forbidden-template avoidance or program encoding.

Prove output existence for justified depth and user-stop policies, projection,
parked constraints, Mu/Union and frontier cases. Aggregate zero-output history
invariants remain separate. Finish public API, ranking/sampling and physical
Haskell correspondence. There is no verified completion percentage or date.

Prior exact finite pruning preservation still covers covered closed construction,
original guard-allocation history and empty inherited payload, for each fixed
finite number of pruning rounds with sufficient mathematical width and fuel.
It does not prove convergence or withoutRedundantEdges. Existing startup
rendered-output soundness, proper storage in each emitted cache and chosen
hook invocation or exact earlier hook stop retain their prior scopes.

## Validation and attempted approaches

Eight modules contain 995 lines and 59243 bytes. They expose fifteen public
theorems. All final strict source checks and strict Audit pass. Full Audit
passes 4305 jobs and checks 80372 theorem dependencies. The existing unused
inputs warning is replayed unchanged. No heartbeat or linter suppression,
sorry, tactic admit, custom axiom or native_decide is added.

Final public readback has 268 theorem blocks and nine printed definitions:
{public['bytes']} bytes, SHA256 {public['sha256']}.
All 253 prior blocks and five definitions remain the exact 1055726-byte
prefix. The new appendix is 26105 bytes. Four EXISTING carrier definitions
are newly printed. Only propext, Classical.choice and Quot.sound occur.
All 4296 old non-Audit Lean sources, 145 pinned strong modules and 810 tracked
Haskell source/evidence files retain bytes. Audit only adds eight imports.

All 28 current compiler/build/public commands remain with logs and exact
source snapshots. Nine commands fail: a renamed fuel argument, startup and
write-lemma namespaces, one redundant tactic, a generated matcher conversion,
a joint-import instance collision, two counterexample proof attempts and an
output fragment namespace. Each complete failure diagnostic was read before
repair. Local instance names now differ across the three sibling rendering
modules. No theorem statement changes in that naming repair.

The first public readback passes Lean but permutes previously interleaved
print blocks. Its metadata prefix helper fails. The second readback replays
the exact previous #check/#print command order, then appends this checkpoint.
No proof changes. Both public attempts and the helper's prior version remain.
The inherited prior-public-readback receipt is separate from the 28 current
commands. All compiler work is serial with measured 4 GiB memory.max/high and
zero swap. No native Haskell execution occurs here.

## Restart and portable evidence

Read NEXT-PROMPT.md, HANDOFF.md and FINDINGS.md. Continue actual native carrier
preservation through terminal and recursive history paths, then accepted-term
forward coverage. Keep all original full contracts and fix resource witnesses
before semantic models. Preserve stopped, rejected and empty outcomes.

Evidence: restart-evidence/20261028-native-render-coverage/. The verifier checks
stored/decoded bytes, installed proofs, source identities, literal cuts, exact
review seals and inverse document insertions. Use --committed after the evidence
commit. Whole older document bodies and earlier failed/untested drafts remain.
Publication receipts stay outside the frozen TEMP and archive. Reviews read all
new sources, complete new public text, whole new note and exact insertions;
they do not claim to reread giant historical document bodies.
'''
paths=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/API-COVERAGE.md','lean/COVERAGE.md','lean/README.md','lean/SYSTEM.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md'];records=[]
for name in paths:
 old=(area/'prior-documents'/name).read_bytes();p=root/name;assert p.read_bytes()==old
 offset=old.index(b'\n')+1;extra=(common+(findings if name=='FINDINGS.md' else '')).encode();data=old[:offset]+extra+old[offset:];p.write_bytes(data)
 records.append(dict(path=name,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),offset=offset,inserted_bytes=len(extra),old_bytes=len(old),old_sha256=hashlib.sha256(old).hexdigest(),whole_old_body_preserved=True))
name='lean/notes-current-native-render-coverage.md';p=root/name;assert not p.exists();p.write_text(note);paths.append(name);records.append(dict(path=name,bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(area/'document-paths.json').write_text(json.dumps(paths,indent=2)+'\n');(area/'document-validation.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(dict(documents=len(paths),old_bodies_preserved=9,note_bytes=p.stat().st_size)))
