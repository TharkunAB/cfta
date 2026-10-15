# Projection through an open ordinary Mu unfolding

Source main remains `525d722e`. The starting checkpoint is `fd279a46`.
The checked proof checkpoint is `00b4806e`, pushed to origin/formalize.
The [refused-class query note](notes-source-refused-class-query.md) records
the earlier semantic result and its open Mu counterexample. This work removes
the whole-input closedness premise for one ordinary Mu exposure. It does not
establish the general gate-to-projection correspondence.

## Actual open head reconstruction

`SourceEqualityOpenOrdinaryHead.unfold_complete` completes a single actual
stored unfolding for any available value in a semantic-ready cache. It
derives readiness, availability, growth, physical history, and exact
independent guarded language. The input can contain free references.
The proof composes the existing stored compiler, completion, and semantic
heap theorems. It does not assume a final semantic result.

`node` reconstructs an ordinary node from resident rows without requiring
closed children. It retains the same cache properties and derives an
available ordinary result. `ordinary` combines the actual unfolding and
makeNode operations with the literal zero-bound Head graph. It derives the
same independent language for every guard interpretation and ambient
reference environment. It does not assert that the result is closed.
`verified` transports this result to any completed Head receipt by exact
head uniqueness. `ordinary_heap` preserves every physical edge-annotation
predicate through unfolding and reconstruction.

The source branch is `getPath p n@(Mu _) = getPath p (Node $ nodeEdges n)`
in `cfta/src/Data/CFTA/Interned/Operations.hs`. The gate unfolds a Mu with
unfoldOuterRec. The projection exposes rows and reconstructs an ordinary
node. The proof retains these distinct operations and their returned heaps.

## Selected path completion

`SourceEqualityProjectionPathComplete.node_complete` and `forest_complete`
derive finite actual projection in the existing NodeClosed and ForestClosed
domains. Ordinary steps visit only selected children. The induction reduces
path length. Ordered row traversal threads each actual returned cache and
joins the closed selected results with the source union. Mu and union cases
inside this existing domain use the earlier closed-input completion theorem.
The domain remains explicit and is not a gate result.

`SourceEqualityProjectionOpenOrdinary.complete` first performs the actual
open Mu exposure. It applies the selected domain to the actual rebuilt head,
not to the original Mu. It then derives finite source projection, both
histories, semantic readiness, and a closed resident result. This removes
the completed-projection premise for that case. Actual single unfolding to
an ordinary node and the rebuilt selected path domain remain premises.

`effects`, `included`, and `heap` apply to every completed projection of
this input. Head uniqueness identifies its actual exposure with the proved
ordinary reconstruction. The proofs retain a selected accepted subtree and
physical annotations. They do not infer closedness of unrelated siblings.

## Retained open Mu example

`SourceRefusedClassOpenHeadBoundary` runs the actual stored unfolding from
the heap returned by the primary gate. The sequential secondary gate leaves
that heap unchanged. The unfolding returns an ordinary node. Actual makeNode
returns that same complete value and heap. `head_receipt` records the literal
row read and reconstruction.

The rebuilt head still has the free reference `.uninterned 999`.
`rebuilt_domain` proves its selected path [0] satisfies NodeClosed.
`original_domain_fails` retains the opposite result for the original Mu.
`exposed_class_domain` also checks every original class path after replacing
only the first forest value with its actual ordinary head. This replacement
is a domain comparison. It is not a change to the source caller.

The example asserts no SemanticReady native state or completed whole caller.
The general theorems retain readiness and availability as explicit premises.

## Remaining obligations

The caller checks every class path before the seeded query. General proof
must transfer those gate receipts to later projection calls in the evolving
constructor cache. Repeated open Mu exposure, union heads, metadata shortcuts,
and the exact current memo tables remain in that transfer. Do not assume a
gate result supplies the old static path domain.

Then compose the ordered primary partition, secondary scan, seeded query,
fallback, and whole caller. Progressive lazy row demand, original child
forcing, checked native transfer, machine bounds and identities, and general
native/exploration/caller completion remain separate obligations. Preserve
waiting-count and template-exclusion targets, broader API/runtime bridges,
the optimized interned core, and every separate exact Sized contract.

## Validation and preservation

The full pinned audit passes 2,031 jobs and 51,878 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. No new warning occurs.
Log: `/tmp/mcfta-open-head-audit-20261015.log`. The eleven general public
theorems and all twelve boundary theorems also pass focused axiom checks.
All earlier Lean definitions remain byte-identical except two additive
Audit imports. All four Haskell package trees match `fd279a46`.
Their unchanged checks were not repeated.

Starting snapshot: `/tmp/mcfta-refused-query-checkpoint-20261015-1853/`
(2,691 files). Closing snapshot:
`/tmp/mcfta-open-head-checkpoint-20261015-1910/` (2,696 files).
Script: `/tmp/mcfta-preserve-open-head-20261015.py`.
All prior proofs, repros, marked drafts, external drafts, stashes, and other
worktrees remain. The new boundary probe and focused logs are also retained.
