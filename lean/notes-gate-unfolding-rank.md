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

`InternedNormalizationFree` proves the source free-name equations through
actual normalization. Canonical ordinary nodes retain exactly the names
from their surviving children. Live ordinary edges retain all input child
names. Every source union branch retains exactly its operands' names,
including identity deduplication, singleton collapse, ordinary edge merge,
and canonical cache readback. Root self-reference filtering preserves each
other name. Smart cleanup preserves the exact free-name list. Their
composition preserves each completed binder's external free names. A
retained free name excludes EmptyNode; this statement does not imply an
inhabited term language.

These equations use the coherent records, actual edge residency, and live
edges already derived from the nested executor. They do not assume the
final normalization equations. The general substitution worker still needs
to derive the corresponding name relation between its input and output.
The focused target builds 150 jobs. The expanded isolated dependency audit
checks 7,126 theorem dependencies.

`InternedUnionHeadGuard` proves that ordinary constructor guards survive
every source union branch, including singleton collapse. Its template
theorem permits an arbitrary recursive replacement below those guards.
`InternedPreparedSubstitution` prepares the source closed-record shortcut,
reference lookup, ordered child plans, edge reconstruction, and source node
and union reconstruction directly from stored values. An open nested Mu
returns `none` to mark the unsupported adapter branch. This is not a source
error or a fuel limit. Closed Mu records use the actual closed shortcut.
Actual cached depth zero proves that preparation succeeds.

`InternedUnionNormalForm` derives flat immediate union members from the
complete nested executor. It covers successful and pending outcomes. It
starts from empty caches without a final-shape assumption.
`InternedNormalizationDepth` proves bounds on actual cached depth through
ordinary edge removal and all source union branches. The current root
self-reference filter cannot increase this depth. These are normalization
equations. They do not make cached maximum depth an unfolding rank.

`InternedShallowGate.normalized_unfold_decreases` combines these results.
For an open body with cached depth zero, the actual source self filter
derives the required guard and preserves depth zero. Preparation therefore
succeeds, and the resulting source constructor computation has head rank
zero for every available replacement. The caller supplies no result-rank,
plan-success, singleton, or guard hypothesis. Flatness and record
availability come from the complete source executor.

This theorem starts at the actual callback body and executes its source
self filter. General stored-Mu unfolding still needs the stored-body
normalization invariant and the open nested-Mu substitution branch. It does
not yet instantiate a complete source gate `UnfoldingRank`.
The shallow target builds 156 jobs. Its isolated audit checks 7,235 theorem
dependencies with only the allowed foundational axioms.

`InternedStoredSelfFilter` and `InternedStoredBodyInvariant` close the
stored-body normalization boundary for this shallow fragment. The complete
nested source executor derives the body property for every stored Mu,
including records completed before a later pending outcome. It uses the
actual self filter on both probes and on the allocated callback body.
`stored_unfold_decreases` now starts with a stored open Mu whose actual
body has cached depth zero. It derives the guard from the source cache
invariants, derives preparation success, and proves strict head-rank
decrease for substitution of that very Mu into its stored body.
`built_record_unfold_decreases` discharges all representation premises
for every completed record of an empty-cache source execution.

A closed constructor expression contains an open inner Mu with actual
head ranks one and zero. `fixture_actual_ranks` checks that expression in
Lean. The same stored-inner-body trace passes against Haskell
`unfoldOuterRec` in `/tmp/mcfta-gate-stored-shallow.hs`. Its observed body
depth is zero and its inner free-variable set is nonempty. This is a
nonvacuous instance of the source fragment.

The stored-body target builds 158 jobs. The combined isolated audit checks
7,350 theorem dependencies. The remaining general case has open nested Mu
records in the substituted body. Their preparation, normalized
reconstruction, and possible operand identity collisions remain separate
obligations. No complete source `UnfoldingRank` is claimed yet.

`InternedStoredSubstitution` adds an executable adapter for the remaining
open nested-Mu preparation branch. It traverses actual stored records.
Closed records become immutable captured inputs. Reference leaves use the
actual optional replacement map. Open Mu records become smart nested
constructors with the original binder reference mapped to the nearest
local slot. The adapter uses the existing complete constructor executor.
It derives cache histories, record provenance, flat unions, and stored
self-filter invariants. A reported pending outcome names an actual missing
canonical payload. Repeating a successful binding in a later state returns
the same record without allocation.

`InternedStoredSubstitutionScope` proves that every encoded input slot is
in bounds. Canonical lookup returns the exact original immutable record.
It proves the closed no-effect shortcut, external optional replacement,
nearest local binder lookup, and ordered child and edge lengths.
`InternedStoredSubstitutionBindings` derives the source environment
restriction from actual cached free metadata. Equal relevant free bindings
give the same complete execution. Restriction to the original free set
preserves all constructor effects and pending outcomes. Together with
successful replay, this proves the two properties used by the source
per-binder substitution memoization optimization.

The nested example now prepares each actual stored body after the previous
unfolding. Its head ranks remain two, one, and zero. Its cached maximum
depths remain two, three, and three. This removes that example's earlier
dependence on reapplying the original source callback syntax.

The binding-restriction target builds 164 jobs. The combined isolated audit
checks 7,611 theorem dependencies. The adapter's full language theorem and
the general strict rank for open nested reconstruction remain unproved.
