# Recursive selected-narrowing source boundary

Reviewed at 2026-10-17 00:34 CEST. Current core source matches the opening
snapshot. No Haskell behavior defect was established. No production file changed.
The Haskell slot is released. The final isolated Nix probe exited zero.

## Actual schedule and recursive boundaries

Equality/Operations.hs:81-91 memoizes by inherited constraints and node. Empty
and explicit union return directly. Mu rebuilds through its bidirectional
pattern; it is not a literal identity expression. Interned/Type.hs:630-700
shows cached probe reuse and smart cleanup. A raw Rec at the outer caller is
an error. Bound RecInt references inside a Mu body are a different case.

Equality/Operations.hs:93-97 first reduces each original parent edge, then
traverses THAT returned edge's children. The inherited payload is the left
operand of combineEqConstraints. Descents use literal child indices.
The original row suffix remains the suffix of the original input list.

Equality/Operations.hs:207-241 checks combined contradiction first. Primary
refusal partitions the ORIGINAL own class order. The refused-class any check
runs before requireAll or the selected class fold. A refused class only calls
its seeded intersection and provablyEmpty when secondary refusal is false.
If that check proves empty, every child becomes Empty and the selected suffix
is not required or edited. Otherwise all selected paths are required, then
foldr reduces classes from the tail. One class captures its incoming forest.
Its ascending paths each get a target made from the OTHER captured paths,
merged separately, then combined by the literal seeded right fold.

Equality/Operations.hs:259-270 distinguishes these cases:

- Rec and explicit InternedUnion refuse before metadata or path tests.
- A closed unconstrained Mu returns false in either mode, including midpath.
- A closed constrained Mu at the exact endpoint refuses in primary mode
  and passes secondary mode. The selected edit does not enter it.
- A constrained Mu inside a path, or an open constrained endpoint, refuses.
- An open unconstrained Mu unfolds and repeats the same remaining path.
- At an ordinary endpoint, free references refuse in both modes. Reaching a
  constrained Mu below a closed endpoint refuses only in primary mode.

This gate is a constraint-safety filter. It is not a general progress theorem.
The fast depth/free metadata branch depends on the interner metadata invariant.
Enumeration.hs:533-549 defines unconstrained over ALL reachable guards: both
empty equalities and residual=false are required. It is stronger than an empty
own equality field and stronger than the proved PlainRegion predicate.

Equality/Operations.hs:292-303 requireNode returns at an empty requirement trie.
A nonempty trie unfolds Mu or union through nodeEdges, then filters too-short
ordinary rows and rebuilds their required children. editNode:329-334 invokes
an EditAt callback at ANY node, including Mu or Empty. EditBelow unfolds Mu or
union before following rows. It fails on an unresolved Rec. These lower calls
can therefore do real recursive work even though the OUTER Mu branch stops.

Interned/Operations.hs:787-814 getPath returns a node unchanged at the empty
path. Below a constructor it forms union of selected children. union:686-693
turns even a singleton closed Mu into Node(nodeEdges Mu). Thus a projected
endpoint can expose an ordinary layer without changing its language.
nodeEdges:163-181 uses cached unfolding and finite closure for recursive/union
boundaries. The focused family below excludes epsilon-only and open schemes.

The native intersection at Interned/Operations.hs:480-548 handles empty,
closed-domain reset, closed self, canonical swap, seen pair, Mu, union, and
bound reference in that order. Mu binds original identities and records the
pair before recursing on stored bodies. A repeated pair returns RecIntersect;
optional Mu binds that marker only if it survives. The edge worker:564-578
rejects unequal arities before conjoining full guards and zipping child calls.
These seen pairs control recursive native queries. They do not prove that an
outer reduction cannot demand its own separately memoized pending result.

## Focused executable results

The final command is:

    nix-shell --run 'export PATH=/usr/bin:$PATH; timeout 90s cabal exec -- runghc -Werror -package=cfta /tmp/mcfta-recursive-selected-progress.hs'

The preserved source is recursive-selected-progress.hs. Final log4 has no
warnings or errors. Each check has a ten-second internal timeout.

1. A nonempty equality class at an ordinary root selects two DISTINCT closed
   recursive languages a|f(self) and a|f(f(self)). The pass really narrows the
   first child, produces equal children, completes, and preserves bounded
   term sets through depths 0..5. This is neither PlainRegion nor an opaque
   Mu-root smoke test. It executes recursive intersection below a selected class.
2. Paths [0,0,0] and [1,0] into two closed a|f(self) inputs complete. The exact
   returned children are f(f(projected)) and f(projected), where projected is
   Node(nodeEdges Mu). The root's ordinary height grows 1 to 4; child heights
   are 3 and 2. The pass preserves the same bounded terms and is unchanged by
   one further pass ON THIS SAMPLE. No general convergence claim follows.
3. intersect Mu (f Mu) returns f Mu. Its ordinary height is 1, greater than
   min(0,1). The finite ordinary min-height certificate cannot extend to Mu.
4. One fixed own constraint with maximum path depth 4 gives inherited depths
   [0,3,4,5,6,7,8,9] under repeated combine-then-descend. This checks a payload
   recurrence, not a completed diverging outer root. A finite future payload
   inventory cannot be inferred from the own payload alone.

Probe1 was sandbox-blocked by the Nix store lock. Probe2/3 used an incorrect
physical expected shape that omitted singleton-union exposure; their raw
sources and failures remain. Bounded language equality already held in probe3.
Probe4 corrects that expectation from the literal source and passes -Werror.
This was a probe error, not a Haskell repair.

Existing EqualitySpec.hs:431-459 tests inherited constraints and three active
recursive children. Lines461-555 cover constrained endpoint rejection and the
ancestor cycle repair. Lines624-650 cover unequal-depth recursive paths and
epsilon-union inputs. These tests were READ, not rerun as full suites here.
The retained OuterCallerCycle.hs corresponds to the already merged endpoint
repair in FINDINGS. RawClosedSelfRequire.hs uses createMuDontCleanup id, the
exported raw/test constructor; smart createMu id cleans this case to Empty.
Its timeout assertion is historical and was not rerun here. In particular,
current nodeEdges has finite closure through visited recursive identities.
No present divergence is inferred from that retained assertion. It is not
evidence of a new defect in smart constructor inputs.

## Concrete next supported family and proof stage

A useful first theorem family has a finite ordinary constrained cap over
closed, constructor-guarded regular Mu atoms. Atom bodies are finite ordinary
schemes with bound references under constructors, no explicit union, and no
reachable equality or residual guard. Each endpoint selected by an OWN class
must denote a hereditarily unconstrained subtree of that initial finite scheme.
The cap may have nonempty classes of unequal path lengths. This is stricter
than saying only that every Mu is unconstrained: an endpoint can still contain
a constrained ordinary node, which could migrate into an unconstrained loop.
No general theorem for this proposed family is claimed in this review.

The first additive producer should prove, for SAME actual native traces,
closed hereditarily unconstrained operands yield a hereditarily unconstrained
result and preserve that property in captured memo owners. Merge and Required
need the corresponding actual-read closures. Next derive a positional class
invariant: edits replace only selected unconstrained suffixes, so every
constraint remains in the original finite cap. Derive this invariant from
initial syntax/path conditions, not a desired callback or future endpoint law.

A global ordinary-height rank is refuted by the probe. A suitable progress
candidate is lexicographic: finite distance to the deepest constrained cap
edge, then ordinary height inside an unconstrained suffix, with node/edge
phase separation. Native query may grow the second component when it enters
an unconstrained suffix, but the first component decreases to zero. At zero,
actual returned unconstrained regions can use the existing PlainRegion
completion because Parent introduces no own class. The active-owner invariant
must use this new measure; current nodeRank can put the generated child above
its pending constrained ancestor. Whole-owner readback must transport the new
measure through warm cache hits. No finite future-key or result-law oracle is
needed for this design, but these closure and active-order proofs are new work.

## Current Lean reuse and exact remaining gaps

SourceCurrentMuEndpoint.lean models the actual primary/secondary split, including
open unfolding and closed constrained endpoints. GateWorker.primary_graph and
secondary_graph link literal bounded calls to their actual graphs. Strict
primary Reads retain the queried endpoint; the historical unanchored receipt
must not be used to infer admission for a different input.

SourceCurrentAllocatedNativeInventoryState.query_complete:85 and
SourceCurrentAllocatedTargetQuery.finite:78 ALREADY construct a general closed
checked query with computed next inventory and exact language, under legitimate
Ready/At/availability/closedness and explicit reached WordRanges. The scoped
initial_complete:650 derives semantic completion from actual Original inputs;
coherent current closed roots can be admitted by the inventory machinery.
It is inaccurate to say all recursive query completion is missing.

The new initial-only word, Work, profile, and outer resource Plan results use
FiniteOrdinaryDomain. They do not discharge recursive seen/name/domain packing,
recursive query resource bounds, the new hereditary-unconstrained result law,
or the lexicographic outer owner order. PlainNode.finite:117 admits Mu/union as
opaque stops, but does not cover the active selected narrowing demonstrated
here. Existing supplied-success PartialWorker soundness retains semantics; it
does not turn arbitrary recursion bounds or a busy result into completion.

The serial Lean model also does not prove GHC lazy forcing or concurrent memo
correspondence. FlatMemo.hs:29-44 publishes a lazy first winner; Memo.hs:14-19
also stores a result thunk before forcing it. Data.IntMap.Strict.foldrWithKey forcing,
observational error order, host signed indices, quantitative width for recursive
products, repeated-pass convergence, and full-library completion remain open.
No new FINDINGS repair entry is needed because no source defect was established.
