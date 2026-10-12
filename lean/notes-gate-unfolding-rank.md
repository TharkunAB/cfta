# Same-path unfolding in the current equality gate

The source gate in `Equality/Operations.hs` unfolds an open unconstrained
`InternedMu` without consuming a path index. Closed unconstrained binders
return false. References and stored unions return true before metadata
shortcuts. The source checkpoint for this work is `microcfta` at `de910ea`.

`RankedGateCompletion` proves that any supplied `UnfoldingRank` gives a
finite successful instrumented run for every path. Every larger fuel
amount returns the same result as the unbounded worker. The proof combines
finite child lists with the lexicographic path-length and unfolding-rank
measure. It does not treat exhausted fuel as a Boolean source decision.

`LexicalGateRank` derives such a rank for `InternedSubstitution.run`.
The rank counts consecutive root binders. It stops at a constructor,
reference, empty shape, or alternatives list. A root binder chain that
ends at a free reference has exactly that one free name. An open outer
binder therefore cannot replace its own reference at that head.
Fresh nested reconstruction and cleanup cannot increase the remaining
head rank. This proves strict decrease on every open binder unfolding,
independently of its constraint predicate. The concrete `ranking` has no
caller-supplied termination premise. `eventually_exact` proves finite fuel
completion for this adapter. `ranked_unfold_exact` connects the same
unfolding operation to the complete open least-language equation.

The lexical result includes nested binders and arbitrary constructor
children. Its union representation retains an alternatives list after
root self-reference removal. That detail prevents direct transfer to all
source interned nodes.

`InternedGateRank` proves the relevant source smart-constructor facts from
the existing coherent cache executor. `makeNode_rank` includes removal of
empty-child edges, canonical edge identities, and cache hits. It returns
rank zero. `ordinary_unfold_decreases` therefore supplies the actual final
substitution branch decrease for an ordinary binder body. Rebuilt children
need no rank premise. They may contain arbitrary open or closed binders.

`makeUnion_rank` gives the exact source result. Flattening and identity
deduplication produce either a singleton, whose rank is retained, or a
rank-zero result. `union_unfold_decreases` covers every nonsingleton result.
The kernel fixture `filter_can_expose_binder` constructs a recursive operand
through the actual constructor executor. Root self-reference removal then
changes head rank from zero to one by returning the remaining operand.
Thus the lexical list-filter rank equation is not a source rank equation.

The remaining general source obligation is a construction invariant for
normalized singleton unions and rebuilt nested binders during substitution
of the outer binder itself. These modules do not assume that invariant or
claim complete termination of the source gate. They also do not prove
termination of repeated equality reduction.

The temporary source probe `/tmp/mcfta-gate-head-rank.hs` runs inside the
project Nix environment. It checks 10,000 generated constructor expressions
of depth six. Of these, 3,417 roots are open unconstrained binders. All of
those unfoldings strictly decrease the actual stored head-binder count.
The concrete nested open example has ranks 2, 1, and 0. A raw closed own
reference binder unfolds to itself, which confirms why the source closed
check matters. The source root-filter example has ranks 0 and 1. These
finite checks do not establish the remaining general invariant.

The pinned Lean 4.34.1 build of `MicroCFTA.InternedGateRank` completes 134
jobs. The source probe log is `/tmp/mcfta-gate-head-rank.log`. No Haskell
source changed.

The source reconstruction invariants now extend beyond that first
checkpoint. `InternedUnionSeparation` proves that identity deduplication
retains a representative of every operand. Two different surviving
identities prevent singleton collapse. Cached Mu depth is monotone along
actual semantic child paths. A nested binder whose body retains an outer
binder has strictly greater cached depth, so the two canonical identities
differ. Stored Mu probes do not participate in that child-path proof.

`InternedEdgeResidency` adds the required link from each stored ordinary
node's edge payloads to the canonical edge table. It derives exact edge
and child readback on node-cache hits. It proves retention below a live
edge through empty-child removal, ordering, identity deduplication, and
cache readback. `InternedUnionRetention` proves that a Mu operand survives
union reconstruction as an actual stored descendant. That operand prevents
the all-ordinary merge. Singleton return and existing union-cache hits are
included.

`InternedNestedFacts`, `InternedNestedRequestFacts`, and
`InternedNestedProvenance` derive these record invariants from the complete
`InternedNestedConstruction.Syntax` executor. The proof covers ordinary
nodes, unions, lexical variables, dynamically nested binders, both probes,
identity reservation, body construction, first-writer completion, and raw
or smart cleanup. `closed_verified` starts from empty tables and an empty
environment. It supplies coherent records, complete child provenance,
outgoing edge residency, table growth, and issued-reference history. A
successful result is available in its actual final state. A pending-key
outcome preserves the invariants at its actual stopping state. The theorem
does not assume that pending outcomes are impossible.

`InternedGateReconstructionExamples` executes an open nested union from
these constructors. Its head ranks are 2, 1, and 0. Its cached maximum Mu
depths are 2, 3, and 3. Thus cached maximum depth cannot replace head rank.
The same trace is checked with actual Haskell `unfoldOuterRec` in the
temporary probe. The Lean example reapplies the scoped constructor body;
it does not prove general stored-plan substitution equivalence.

These additions derive source trace inputs for the separation laws. The
general rank still requires occurrence preservation through all normalized
reconstruction branches and exclusion of collisions between distinct
rebuilt operands. No complete source `UnfoldingRank` is claimed yet.

The combined reconstruction target builds 147 jobs. Its isolated axiom
audit is `/tmp/mcfta-gate-source-provenance-audit.lean`. The focused build
log is `/tmp/mcfta-gate-source-provenance-build.log`.

`InternedNestedCoverage` proves payload coverage for every successful
nested execution. The theorem allows arbitrary earlier pending keys.
Reservation adds the binder's actual key. Successful completion installs
that payload and removes only the extra allowance. A completed empty-table
run has `Covered []`: every installed identity has a complete record.
This is conditional on successful return. It does not exclude pending
outcomes or replace the separate first-run completion proof.

`InternedHeadReference` proves the head-chain free-name facts directly on
actual stored `Value` metadata. An open stored Mu cannot have its own
reference at the end of its head chain. The statement includes raw unused
binders. `InternedBinderRetention` proves that smart cleanup cannot erase
an actual Mu descendant from its body. The source root filter also cannot
collapse a union that retains both an outer Mu and a deeper Mu containing
it, because those actual resident identities differ.

`InternedLiveEdges` derives the source empty-child invariant for every
nested execution, including a pending outcome. Each stored ordinary edge
has no EmptyNode child. It starts from empty tables and needs no assumed
final liveness property. `InternedUnionDescendants` combines that result
with canonical edge readback. Every source union branch preserves an
actual Mu descendant from an operand, including the all-ordinary edge
merge. Current root self-reference removal also preserves every actual Mu
descendant, including those below constructors. These results remove the
earlier restriction to a Mu at the root of a union operand.

The remaining substitution proof must derive nonempty and free-name
preservation while rebuilding children. It must also exclude collisions
between distinct rebuilt operands when no directly retained outer Mu
separates them. The general source gate rank remains open.

A broader temporary Haskell probe adds raw binders, public unions, multiple
ordinary rows, and depth-eight expressions. It checks 20,000 expressions.
Of these, 11,921 roots are eligible open binders. Every checked source
unfolding decreases head rank. Its log is
`/tmp/mcfta-gate-head-rank-broad.log`. This is finite evidence only.

The descendant-retention target builds 149 jobs. The combined isolated
axiom audit checks 7,106 theorem dependencies with only the three allowed
foundational axioms.
