# Current constrained outer progress: next proof domain

Read-only source audit. Current core source is `c0cc8a05`. This review did
not run Haskell, Lake, Git, or new source tests. The separate small Lean
boundary probe was requested by root after the initial read-only finding.
It is an external evidence file, not a production module.

## Result

General constrained outer completion remains open. The current endpoint
guard blocks specific dangerous unfolding patterns, including the preserved
ancestor-cycle fixture. It is not a check of all evaluating outer keys.
No inspected theorem derives a well-founded relation for every current
returned child request. Absence of repeated keys would also not exclude an
infinite sequence of fresh allocated node and inherited-constraint keys.

The strongest small next implementation is a CURRENT checked completion
theorem for the existing equality-free ordinary `Region`, with arbitrary
ready inherited payloads. It must use an internal active-frame rank
invariant. A top-level endpoint can derive that invariant from empty outer
result tables while retaining all lower warm tables. A stronger warm outer
endpoint needs a structural returned-edge certificate as well as `Sound`.

A useful next constrained extension is the finite ordinary-tree fragment
with arbitrary normalized equalities and no Mu/reference/union values.
This needs new actual checked height/shape laws. The historical cold merge
height theorem alone does not supply them. Neither extension proves general
constrained completion.

## Exact current source guards

`cfta/src/Data/CFTA/Equality/Operations.hs:76-91` keys the node memo by
inherited equalities and node, stops at Mu and union, and traverses ordinary
rows. Lines 93-96 recurse into the RETURNED edge's children after combining
inherited constraints with its own equalities. Lines 143-145 erase on
contradiction or descend the payload once for each indexed child. The edge
memo is a separate family at lines 149-168.

Lines 207-224 first use the combined contradiction check. They partition
ORIGINAL classes by the primary gate. A refused class can erase the forest
only after a false secondary gate and a true `provablyEmpty` result. Lines
226-244 require selected paths and then perform the right class fold. Each
class captures the current forest. Its targets read the other paths, merge
their alternatives, and intersect them at the edited path.

The primary and secondary tests at lines 255-271 have these boundaries:

- A bare reference or explicit union blocks a path.
- A closed constrained Mu blocks the primary gate at its endpoint. It does
  not block the secondary gate at that endpoint. Its interior still blocks.
- An ordinary endpoint blocks when it is open, or, for the primary mode,
  when `reachesConstrainedMu` holds.
- A closed unconstrained Mu returns false without checking its remaining
  suffix. The required/projection stages can expose it later. An open
  unconstrained Mu is followed through its unfolding.
- A closed record with no nested Mu returns false immediately. Missing
  child positions return false. Path existence is handled separately.

`Enumeration.hs:529-550` defines `unconstrained` over ALL reachable equality
and residual guards. `reachesConstrainedMu` stops at an unconstrained Mu and
visits ordinary children and union members. None of these tests receives
the outer memo's evaluating cells or a candidate inherited memo key.

`Enumeration.hs:588-644` gives the current bounded conjunction emptiness
check. Open or unadmitted/budget-limited conjunctions are optimistic. False
is not a proof of nonemptiness or progress. The secondary query's result is
used only for erasure; it is not installed in the child forest. This avoids
the refused-class narrowing path. It does not prove descent of every class
that the primary gate accepts.

The source itself states the remaining scope at `Operations.hs:119-142`:
it describes the no-unfolding case and the case where endpoint narrowing
introduces no constraints. It leaves other single-pass inputs and repeated
passes unproved. Unequal path lengths can move a constrained node into an
unconstrained Mu's unfolding at a greater depth.

## Preserved cycle and candidate obstruction

`lean/repro/OuterCallerCycle.hs:22-37` constructs the closed `plain`,
`next`, `constrained`, and wrapped root values. The historical local result
has two `wrap root` children and empty inherited payloads. The associated
kernel result is `SourceEqualityOuterCallerCycle.cycle` and
`.not_wellFounded` at lines 130-160. Its observation at lines 78-106 invokes
the HISTORICAL `SourceEqualityGuardedEdgeWorker`. The worker and memo-cycle
companions preserve that same historical policy.

The CURRENT gate sees `wrap constrained` at the endpoint. Its primary
`reachesConstrainedMu` test is true. The class is refused rather than used
for a class edit. The current regression is
`cfta/test/Data/CFTA/EqualitySpec.hs:512-551`; the bare endpoint variant is
at lines 461-486. The old fixture is not a new current-source divergence
counterexample. It was not rerun in this audit.

A remaining candidate family has a non-prefix unequal-length class such
as `[0] = [1,0]`. Put a finite constrained ordinary subtree `C` at `[0]`,
where `C` reaches no constrained Mu. Put a closed unconstrained recursive
tree automaton `U` at child 1. The current primary gate permits the path
through `U`, and `requireAll` can expose it. A class edit can install an
intersection containing `C` in that exposed prefix. This is a concrete
shape for testing constraint-depth migration, not a certified cycle or a
claimed source defect. A true counterexample must retain exact returned
guards, inherited descent, selected order, merge results, and physical
node/equality identities at every step. It must show either an evaluating
key is demanded again or an infinite fresh-key chain. The source's
congruence normalization can reject candidate cycles when inherited paths
force a path equal to its strict extension (`Constraint.hs:386-392`).

## Context does not exclude active owners

`SourceCurrentAllocatedPartialInvariant.Context:25-35` carries readiness,
admission, sound warm cells, merge/fourth/global validity, and ProbeHeap.
`PartialMemoSound.NodeGood/EdgeGood:49-69` deliberately retain valid inputs
in ALL phases; only returned phases need a result law. Thus `Context` does
not imply idle outer result families.

`PartialCallSteps.node_start:35-50` preserves Context after an ACTUAL
evaluate observation and retains the exact owner cell. `PartialState` uses
the inherited allocated identity plus the node/edge identity as its keys
(lines 27-49). `beginNode_busy:156-162` and
`PartialWorker.nodeCall_busy:188-193` show that the same running key cannot
complete at any bound. `PartialWorkerRanges.nodeCall:38-44` is True on this
busy observation. The ranges are checks, not a completion certificate.

`progress-boundary-probe.lean` proves this from a fresh missing key, actual
publication, and legitimate initial Context/ready/resident input. It derives
the running Context, exact published key, exact evaluating cell, and the
busy failure for EVERY ten-bound tuple. It does not assume an arbitrary
busy observation. Direct pinned Lean returned exit 0 in
`progress-boundary-probe-5.log`; one axiom/signature pair has only propext,
Classical.choice, and Quot.sound. Logs 1-4 retain the corrected elaboration
attempts. No production source was changed.

This is a boundary of the proposed theorem premises, not a Haskell bug.
Top-level idle outer tables can discharge the initial frame condition.
Recursive calls need an active-frame exclusion invariant, not a fresh idle
premise: the parent is evaluating during those calls.

## Useful existing finite results and their limits

| Actual result | Exact reusable endpoint | Limit for outer completion |
| --- | --- | --- |
| Historical equality-free region | `SourceEqualityPartialInheritedPlainCompletion.complete:20` and `...InheritedPlainSource.region_exact:21` | Old NativeState/graph/policy. Reuse the structural argument, not a current execution transfer. |
| Empty-own local shape | `SourceEqualityPartialInheritedPlainPass.precheck_cases:20`, `.complete:50`; `...Prefix.complete:22` | Old graph. It explains why arbitrary inherited payloads still give original or erased children and no native request. Port this shape to the current literal local stages. |
| Current finite gates | `SourceCurrentClassGateCompletion.primary_class_complete:37`, `.secondary_class_complete:62` | A finite path/class computation, not a recursive outer rank. |
| Current required execution | `SourceCurrentRequiredComplete.node_complete:133`, `.requireAll_complete:199`, `.primary_complete:247` | Trie size descends on a path-local support domain. Rebuilding can expose more ordinary structure than the original caller. |
| Current native intersection | `SourceCurrentAllocatedNativePhysicalTraceCompletion.initial_complete:535` | Derives its own independent request schedule from closed original operands, Good, idle native cache, and WordRanges. It is not a rank for generated outer inputs. |
| Current local/parent | `SourceCurrentAllocatedLocalWorkerActual.finite:121`, `...ParentWorkerActual.resident_finite:182` | Constructs finite lower execution and same actual state from initial facts and reached machine ranges. It does not complete descendants. |
| Current outer worker from a graph | `SourceCurrentAllocatedPartialWorkerCompletion.nodeCall_complete:355` and the other seven endpoints | Assumes a finite actual outer graph. It derives ten stable bounds; it does not construct that graph. |
| Current outer success receipts | `SourceCurrentAllocatedPartialWorkerActual.nodeCall_verified:348`, `.root_exact:484` | A supplied successful literal observation derives its own graph, strict reads, Post, and language law. No existence conclusion. |

`MergedOrdinaryHeight.child_lt:50` gives ordinary proper-child descent.
`EqualityMergedTargetHeight.Tree:18` and `.merge_height:351` prove a useful
height law for the historical cold finite ordinary-tree merge worker.
They do not cover arbitrary recursive intersections or arbitrary warm
cached results. `SourceEqualityPartialHeightBoundary.actual_heights:79`
records a historical-policy increase `(parent, child, narrowed)=(2,1,3)`.
The current guard blocks that fixture's constrained-Mu descendants. It
therefore refutes transfer of the old unrestricted height argument, not a
current height theorem under a new no-unfolding domain.

## Minimal next theorem and missing measure laws

For the small current Region port, use a tagged request rank:

- Node request: `(MergedOrdinaryHeight.height value, 1)`.
- Edge request: `(MergedOrdinaryHeight.edgeHeight edge + 1, 0)`.

Use lexicographic order. A node's edge call is below the node, including
when their first components coincide. An original-or-erased returned
edge's child node is strictly below that edge rank. List suffixes use their
own structural length. Inherited payload identities need no rank bound in
this fragment. Empty, Mu, and union node bodies terminate directly; the
existing `SourceCurrentAllocatedMuRebuild.resident_rebuild:143` handles the
actual Mu cleanup from Context's ProbeHeap.

The internal invariant must require all evaluating owners to be above the
current request rank. It must identify the first stored owner through
coherent resident keys, survive literal begin/finish, retain other active
frames, and restore the caller bound after a return. The existing
`PartialFrames` lifecycle lemmas preserve these cells, but do not prove
that a new candidate is below them.

For arbitrary WARM outer edge tables, also require or derive a causal
plain-edge result certificate: for an empty-own Region edge, its stored
returned children are the original list or its erased list. `EdgeLaw`
alone is insufficient. As a logical example, an unproductive closed
unconstrained Mu `U` makes `N = Node [Edge "a" [U]]` empty. A semantically
sound warm entry could map this edge to `Edge "a" [N]`, also empty. Both
records can be resident in a grown heap. Traversing that returned edge can
demand `N` again. This is excluded by actual empty-own computation, but not
by the present semantic `Sound` alone. It is not a reachable-source cache
bug claim. Cold outer tables, or a proved actual history/shape invariant,
avoid this gap without resetting lower caches.

For the constrained ordinary-tree extension, prove CURRENT checked
projection/required/edit/merge/native returned-tree and height bounds,
including stored warm result bounds or their causal-history derivation.
Then derive the local returned-child height bound before recursive calls.
Do not assume that bound as a callback or future local result premise.

For general recursive constrained inputs, an additional independent
constraint-location/recursion measure is still needed. It must survive
unequal-length path substitution, actual native intersection and merge,
right-fold class edits, equality combination/normalization, and inherited
descent. It must decrease for every actual recursive node/edge request and
be invariant under coherent key aliases. No such global law was found.
Neither language narrowing nor a finite per-call native input model proves
this law. Initial finite heaps, bounded emptiness worklists, WordRanges,
and finite completed prefixes do not give a finite future outer key carrier.
Repeated `fixUnbounded` convergence and GHC demand/publication behavior are
separate remaining targets.
