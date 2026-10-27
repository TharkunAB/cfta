from pathlib import Path
import json,subprocess
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-rendering-20261027')
base=(area/'base.txt').read_text().strip();checks=json.loads((area/'verified-checks.json').read_text())
docs=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/COVERAGE.md','lean/API-COVERAGE.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
block='''## Actual native rendering constructs the assignment for captured-slot soundness

Main `c168a952d` is integrated by `646a9af8d`. This adds the sorted e-graph,
cost-ordered term APIs and a new flat member-set union-find. Both changelog
entries remain. Existing proofs and the optimized interned core remain intact.
Diagonal completion and structural history: `57a10ab95`.
Actual recursive consumers and callback Canonical: `c38c3a68d`.
Native rendering and captured-term acceptance: `51331a044`.
The full goal stays ACTIVE. H6 remains the strongest system language theorem.

CapturedEdge.diagonal_render_sound_current now derives native edge and parent
acceptance of the actual rendered captured term. It constructs an assignment
from the stored fragment equations and checks the actual rendered residuals.
It derives final-cache Safe and dependency order from the same completed
native producer. No final Satisfies, final Safe or final order is an input.
The full original pending language and every original suspended Holds follow.

The original current admission and semantic gates remain explicit. The
completed observation is an actual stable diagonal family. Initial Canonical,
initial Stratified, ordinary no-terminal status, fresh own arity, structural
child retention and numeric Ranges remain. Discharged requires every remaining
pending slot to have no native handle and no suspended restriction. The actual
render must succeed, and its returned residuals must hold. Scheduler done does
not imply Discharged. Rendering existence, recursive truncation, arbitrary
partial outputs, selector coverage and forward completeness are still open.

Recursive consumers now derive allowed arity and actual projection from their
completed observations. The actual callback producer retains its complete old
result and adds Canonical at the same returned core. Resource-only recursive
receipts do not yet derive semantic Ranges. Preserve that gap explicitly.

All six new modules and Audit pass strict checks. Aggregate Audit passes
3978 jobs and 78052 theorem dependency checks. Installed public readback covers
eight new theorems, unchanged H6 and four complete native renderer definitions.
Only permitted axioms occur. All earlier proof sources except Audit imports
remain unchanged. Core tests pass 341 examples. Specftacular library and CLI
build in Nix. Fourmolu and both changed Cabal gild checks pass.

A new Haskell defect is verified: constrained EGraph.extract can return Nothing
for a nonempty class. The focused example returns an accepted cost-5 term via
termsByCost while extract returns Nothing. No repair is applied. FINDINGS has
the exact reproducer, evidence and cost-contract caveat for external repair.
The new union-find also needs a representation bridge: the existing Lean model
still uses path compression. New e-graph and cost-order APIs are not certified.
Details: `lean/notes-current-pruning-native-rendering.md`.

'''
findings='''### Verified constrained EGraph.extract failure after main integration

Upstream `c168a952d779a72294c34d9c8fd5afd0e308c5ab` is integrated at
`646a9af8d543e53efbb08677840a15381afab8cc`. EGraph.extract promises the cheapest
term of an e-class. Its current implementation first computes unconstrained
least costs, builds only cheapest children, and then checks the parent path
equalities. It does not try a more expensive child after a failed equality.

Verified finite reproducer: merge g(a) and h(b) into C. Add p[C,b] with the
equality at paths [0,0] and [1]. Give h cost 2 + sum(children), and every other
symbol cost 1 + sum(children). The cost is monotone and exceeds each child.
Native extract returns Nothing. Native termsByCost returns p(h(b),b) at cost 5.
Native classAutomaton accepts that term and returns Right True. The cheaper
unconstrained child g(a) fails the equality. All 341 existing core tests pass.
The existing extraction property generates plain terms, so it misses this case.

External repair is pending. Preserve this example as a regression. A repair
must search beyond unconstrained minimum children when constraints reject them.
Do not substitute termsByCost without reviewing the public cost contract:
termsByCost requires monotonicity in child costs, while extract currently states
only strict increase above each child. The reproducer satisfies both conditions.
No Haskell repair or regression-suite change is applied in this checkpoint.

Reproducer and complete native receipt:
`lean/restart-evidence/20261027-recursive-rendering/extract-constrained-repro.hs`
and `native-constrained-extract-1/raw.log.gz`. The decoded 71-byte output has
SHA256 `5ba63849d82a51db3bb8b99e7cc5c038d2f4c7d948704f67afec7b4ac70d80af`.
Run the reproducer in the project Nix shell with cabal exec and runghc -package=cfta.
The original proposal comments remain in the evidence. The actual execution
and results above supersede its original unexecuted status.

The upstream union-find is also a real representation change. It stores each
root's member IntSet and points every losing member directly to the winner.
find returns the same forest. Existing Lean UnionFind still models parent
chains, path compression and a link of the losing root. Weighted winner and
tie rules agree, but exact returned-forest correspondence needs a new invariant
and representation relation. No valid-input native union-find defect was found.
New EGraph, termsByCost and opt-in Specftacular e-graph pruning add open proof
scope. They are not covered by the new rendering theorem or unchanged H6.

All six earlier merged Haskell repairs, the merged Sized documentation repair,
earlier reproducers and pending parallel-decision suffix-exception/cancellation
findings remain below. Record future verified Haskell repairs here.
Details: `lean/notes-current-pruning-native-rendering.md`.

'''
note='''# Current native rendering, recursive consumers and upstream integration

Published base: f4375cd2dc1c1afa410c5f5faea5408304a788ac.
Imported main: c168a952d779a72294c34d9c8fd5afd0e308c5ab.
Integration: 646a9af8d543e53efbb08677840a15381afab8cc.
Diagonal completion: 57a10ab95d158a2fcac8a3e37cb1491cb478af6c.
Recursive consumers: c38c3a68dca6b52396c64f29dcfb338a99d00bae.
Native rendering: 51331a044a9bae75a9a1c683a39201e9798bdc2f.
The goal stays ACTIVE and incomplete. Preserve every older proof, counterexample,
repair and marked draft. Keep the optimized interned core as the primary model.
Keep the older constructor and equality work as secondary targets.
The preceding checkpoint is lean/notes-current-pruning-captured-soundness.md.

## Strongest claims

SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
system language theorem. Under formal guard/entailment semantics, covered closed
construction and valid constraint-allocation history, any chosen finite number
of modeled node-processing calls with the empty inherited payload can complete
at derived mathematical width and fuels. The final available node accepts
exactly the original finite trees in every ambient environment. Its source is
unchanged at SHA256 e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5.
This is a theorem about the explicit model, not verified extraction of all
current Haskell code or the newly changed union-find representation.

The new local theorem is CapturedEdge.diagonal_render_sound_current. Under its
actual completed family and current admission, the real native heap renderer
and checks of its actual returned residuals imply that its term belongs to the
original selected edge and parent. It also constructs an assignment satisfying
the complete original state and every original suspended constraint at the
rendered term. The returned filled fragment is that term. The actual cache
before rendering and its actual returned core both satisfy the assignment.
The rendering retains a complete compression Frame at the same native heap.

No satisfying final assignment is supplied. No final Safe or final dependency
order is supplied. The actual completion producer derives the latter facts.
Initial Canonical, initial Stratified, current Context, Ready, actual stored
pending slot, native realization, selected-edge membership, correct indexes,
pending references, inherited arity, projection and numeric Ranges remain.
Ordinary no-terminal status, fresh own arity and structural child retention
remain explicit semantic gates. Stable diagonal completion and actual successful
rendering remain observations. This does not prove either observation exists.

Discharged requires every stored pending slot to be .unenumerated none [].
It excludes every remaining native handle and every remaining suspended bucket.
The native scheduler can report done with a pending recursive Mu/Union and an
empty bucket. It does not derive Discharged. Canonical validates tries; it does
not derive empty buckets on pending pure equality slots. A partial stop can have
no completion. These are separate theorem domains, not new runtime defects.
The actual rendered residuals must satisfy the formal guard predicate.

## Diagonal receipts and actual recursive consumers

The recursive worker uses one common work fuel. Its receipts retain completion
at (bound + extra) in all five fuel positions. The previous semantic theorem
required independent r/n/k increments and lower bounds for P/H. A diagonal
observation by itself cannot establish that stronger statement.

stable_complete_of_diagonal invokes the existing genuine Captured.complete
producer. It compares that producer's result with the actual diagonal receipt
at one common w above every bound. Full Result equality identifies the fragment,
Caller, query table and enumeration cache. It then returns the producer's
independent family. diagonal_complete_sound_current uses that actual family.
diagonal_complete_safe_order uses complete_with_history and the same alignment.
It derives Safe and the actual dependency-order advance at the exact final cache.

Recursive.completed_head_canonical consumes an actual fixed-bound completed head
and the original Packet. It derives allowed arity and a present projection by
excluding impossible rejected/unhandled observations. It uses the packet's
actual full Context, realized slots, paths, counts and flags. It needs initial
Canonical but no Ranges. Recursive.completed_head_sound_current consumes the
actual diagonal completed family. It keeps explicit Ranges and semantic gates.
It derives pending input facts from the packet and actual stored slot.

Recursive.callback_complete_canonical runs the old callback producer once.
It retains that producer's complete existential result, metadata, stable read,
Frame, raw singleton and all larger-fuel continuation equations inside one
conjunction. It adds Canonical at the same actual callback core by Frame.values.
The original declaration and every original caller remain unchanged.

FiniteHeadResource uses Fits, reservation and guard-heap admission rather than
exported SelectedEdge.Ranges. No implication from those inputs to the required
universal semantic Ranges is claimed. The legacy NativeOrdinary identity-hook
law also cannot certify a nonidentity hook scan: recursive native effects can
change the endpoint for the next sibling. A stopping hook's current receipt is
outside processed and requires its own receipt certificate.

## Actual native heap rendering

SourcePruningEnumerationRendering defines Discharged, expandFragment, expandUVar
and render. Fragment/root rendering reads getValue at the actual enumeration
state. A pending handle is decoded with lookupNode at the supplied native heap.
Mu and Union boundaries produce the source marker. A missing handle retains an
explicit unresolved-reference failure. Other unfinished nested slots fail;
other unfinished roots reject. No fabricated Graph is constructed.
The functions model Enumeration.hs:1049-1075 and the existing native handle
convention. They do not prove native NodeId/container extraction. They retain
the existing abstract enumeration forest operations. The flat upstream union-find
requires a separate representation bridge.

The private read proof retains totality, complete stored-slot equations,
Discharged and the actual Frame. The fragment/root proofs follow the actual
ordered child traversal and reached read cores. Under Discharged the pending
Some branch cannot occur. Marker output receives no native acceptance claim.

render_assignment uses EnumerationAssignment.stratified_assignment to construct
one assignment from Safe, initial dependency levels and Discharged. It proves
exact root rendering and exact residual pairs with the residual predicate True
for the intermediate equations. It then uses checks of the actual returned
pairs to establish all original residual predicates. Native Satisfies follows
at the input and actual output core. This uses no supplied final Satisfies.
No Safe-after conclusion is inferred merely from Frame.

CapturedEdge.diagonal_render_sound_current derives Safe and dependency order
at the actual captured final cache, applies render_assignment at that cache and
its own reached heap, then passes the constructed PRE-render Satisfies to
backward captured soundness. It substitutes the actual term/assignment equation.
It does not retarget the theorem to a sibling cache or a later native endpoint.

## Main integration and external Haskell repair

Main adds sorted e-graphs, constrained e-nodes, matching, analyses, saturation,
class extraction and cost-ordered terms. Specftacular has opt-in e-graph law
pruning; its default remains off. These APIs are additional open proof scope.
Lattice.latticeImplies exposes the old pure decision body without changing
its retries or Yes/No/Unknown result. Existing Enumeration and interned source
bodies stay unchanged across the upstream revisions; their union-find changes.

UnionFind now keeps Root(size,member IntSet), redirects every losing member
and uses one parent lookup for root. find leaves the representation unchanged.
For unions (0,1), (2,3), (2,0), the old model can retain 1->0->2, while the new
source points 1->2. Weighted winners and ties agree. A new flat-parent/member
invariant and refinement relation are required for exact source correspondence.
The old path-compression proofs remain valid statements about their definitions.

The new constrained EGraph.extract defect is verified in the exact integrated
library. Merge g(a) and h(b). Add p[C,b] with [0,0]=[1]. Cost h is 2+sum; other
symbols cost 1+sum. extract returns Nothing. termsByCost returns p(h(b),b) at
cost 5, and classAutomaton accepts it. The current extract chooses only the
unconstrained least-cost children and never tries the more expensive valid one.
Existing core tests pass 341 examples and miss this constrained extraction case.

FINDINGS records external repair as pending. No runtime repair is applied.
A constraint-aware extraction search must respect sufficient cost assumptions.
Do not blindly use termsByCost: its monotonicity requirement exceeds extract's
current documented strict-child-cost condition. The example satisfies both.
All six earlier merged repairs, Sized documentation repair and pending parallel
suffix-exception/cancellation findings remain. Preserve all earlier reproducers.

## Checks, attempts and evidence

All six new modules and Audit pass strict warnings-as-errors and all linters.
The installed aggregate Audit completes 3978 jobs and checks 78052 theorem
dependencies. Public readback contains eight new theorem signatures, unchanged
H6 and four complete renderer definitions. It has 694 lines and 48039 bytes,
SHA256 17a8011f1eb9ca899a406f7393743fc5eb2c8907e069207bfc35c02130b896de.
Only propext, Classical.choice and Quot.sound occur. The old dependency's unused
inputs warning remains. No new proof uses sorry, project axioms, native_decide
or an increased heartbeat setting.

Native core tests pass 341 examples with seed 20261027. The constrained-extract
reproducer runs in Nix and prints the exact three results above. Specftacular's
library and CLI compile. Fourmolu checks all integrated Haskell files; gild
checks both changed Cabal files. All heavy checks use serial 4 GiB cgroup caps
with no swap. These checks do not prove whole native runtime correctness.

Retained attempts include the initial native check launched from lean rather
than the root (no shell.nix), four renderer elaboration failures, and Audit
before the final rendered module was installed. The native check was rerun
from the root. Renderer fixes add explicit binders, the existing state-read
namespace, explicit substitutions and the residual action's effect type.
All three rendering function bodies stay byte-identical across those strict attempts.
Audit passes after the already checked final module is installed. A pin-reader
check also exposed differing declaration-span trailing-LF conventions. The
original pins remain. A separate correction states each exact convention and
literal byte identity. No source hash or theorem result changed.

Evidence: lean/restart-evidence/20261027-recursive-rendering.
It retains plans, marked drafts, every failed snapshot and raw log, native
receipts, public readback, exact final sources, whole source pins, focused
source spans, independent reviews, integration stages and proof-change.patch.
Raw logs are losslessly compressed with decoded lengths and hashes. The
manifest covers every payload. Exclude only this exact evidence patch path
from the staged whitespace check. Do not rewrite old evidence or reports.

## Next work and full scope

Connect Canonical through actual selected prefixes, narrowing, ordinary entry,
nonidentity hook histories and recursive outputs. Append completed-head validity
to the existing finite head producer from its actual diagonal observation.
Retain checked fresh-arity origins through reconstruction. Bridge genuine
resource/reservation admission to semantic Ranges or prove a resource-backed
neutral semantic producer. Do not assume future callback success or Ranges.

Connect backward captured semantics through the same actual recursive trace,
including sibling cache restoration and each reached native endpoint. Derive
the structural discharge predicate where the source can establish it. Treat
recursive truncation and early partial stops with their own precise output
semantics. Rendering existence needs structural carriers; discharge alone does
not make a free root render. Selector coverage and forward completeness remain.

Prove the new flat union-find representation relation and the new public e-graph
and cost-ordered APIs. The global objective also includes full typing/pruning,
withoutRedundantEdges, concrete solver correctness, physical containers, machine
integers, practical capacity adequacy and unbounded progress. H6 does not cover
these. The full objective has not been narrowed to the local rendering result.
'''
marker='## Actual captured-slot expansion now restores the original pending language\n'
for rel in docs:
 p=root/rel;s=p.read_text();assert s.encode()==subprocess.check_output(['git','show',base+':'+rel],cwd=root)
 assert s.count(marker)==1
 s=s.replace(marker,block+marker,1)
 if rel=='FINDINGS.md':
  fmarker='### Captured-slot soundness restores the original pending restriction\n';assert s.count(fmarker)==1
  s=s.replace(fmarker,findings+fmarker,1)
 p.write_text(s)
path='lean/notes-current-pruning-native-rendering.md';assert not (root/path).exists();(root/path).write_text(note)
content=dict(docs=docs,block=block,findings=findings,note_path=path,note=note)
for rel in docs+[path]:
 data=(root/rel).read_bytes();assert data.endswith(b'\n') and all(line.rstrip()==line for line in data.splitlines()),rel
(area/'handoff-content.json').write_text(json.dumps(content,indent=2)+'\n')
