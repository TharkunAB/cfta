# Compact equality edge ranks

`MicroCFTA/CompactEdgeRanks.lean` models `buildEdge`, `addGroup`, and `rankEdge`
in `cfta-generator/src/Data/CFTA/Gen/Internal/Automaton.hs`.
It uses the actual parser and merge-fold layout from `CompactGroups` and the
actual association builder and inverse group reader from `CompactChildSlots`.

## Local inputs

Each compiled child intersection supplies an `Index`: its finite count,
direct selector, and inverse. `Correct` requires total selection below that
count, rejection outside that count, and both inverse directions. These are
local induction inputs for child compilers. They are not desired whole-edge
correctness assumptions.

The edge layout is the actual `childGroups arity classes`. The normalized
classes must pass the direct-child parser's bounds. These inputs derive
nonempty groups, distinct complete child positions, and all reconstruction
preconditions. The semantic theorem additionally requires each group index
to describe exactly the intersection of its child-position domains.

## Actual decoder and inverse

`plan` folds `addGroupPlan` from the one-member `pure []` plan. Each step
multiplies the prefix cardinality by the new child count. Its direct selector
uses quotient and remainder with the new child count. It appends the selected
group value to the group list. `slots_snoc` proves that applying the actual
association fold afterward gives precisely the source `addGroup` operation.
The first group is the most significant digit.

`Decoded` records the finite sequence of those source steps. `select_decoded`
and `decoded_select` prove exact correspondence with the direct plan.
`plan_total`, `decoded_bound`, and `plan_count` prove its complete interval and
product cardinality. The operational plan does not enumerate child terms or
all earlier ranks.

`assignment_agrees` derives a child assignment from distinct group positions.
`construct_generated` composes that result with the actual packed
`Term.fromAssocs` proof. `construct_original` proves reconstruction of any
existing child list accepted by the group readers. The packed and ordinary
term representations are connected by the existing pack/unpack theorem.

`rankFold` is the source `foldM addGroupRank 0`. It uses `selectedGroup`, which
scans the concrete children in index order, rejects an empty read, and checks
that all selected children equal its first child. It then calls the child
inverse and appends that digit with `pairRank`. `rankFold_sound` derives a
decoder derivation and slot agreement from a successful inverse. The reverse
proof reconstructs every original digit from the actual generated children.

`rankEdge` first checks the root symbol and declared arity. `edge_inverse`
proves both inverse directions for the whole reconstructed term.
`edge_injective` proves distinct ranks select distinct terms. `edge_rejected`
proves that inverse failure means that no rank selects that term.
`edge_rank_interval` proves successful selection exactly at
`0 .. product(group counts) - 1`.

The empty product has one nullary constructor at rank zero. A zero-count
child intersection makes the whole edge count zero and rejects every rank.
These cases are included in the proofs. The source `pay` changes size metadata
only; it does not change this edge count or rank order.

## Complete edge language and alternative composition

`rankFold_language` composes the actual group readers with
`groupSelections_exact`. It proves exactly the original child domains and
direct-child equalities. `edge_language_exact` adds the root and arity checks.
`compiledEdge_correct` packages all operational index obligations for use in
an induction over the parent compiler.

`outputs` is a finite proof witness obtained from valid ranks. The operational
selector does not construct it. `outputs_nodup`, `outputs_count`, and
`outputs_select` prove that it has exactly the source cardinality and rank
order, with no duplicate removal. `edgeIndex` therefore supplies the exact
distinct index for the edge language.

`positionDomain` reads the exact child state at a child index.
`all₂_positions` connects that read to ordered child-language membership.
`source_outputs_exact` gives the exact output-language premise used by
`AutomatonAmbiguity.compactIndex`; `outputs_nodup` supplies its uniqueness
premise. The remaining local adapter is the parsed direct-child guard law:
on a correctly sized term, the stored edge guard must be exactly its compiled
equalities. This is a guard adapter, not an assumed edge-decoder theorem.
The compact alternative overlap gate and offsets are separate modules.

The whole `buildNode` cache driver, its acyclic recursion over group
intersections, symbolic fallback, and construction failures are not proved
here. This module supplies its complete local compact-edge compiler step.
Ranks use natural numbers after the source range check. Machine arithmetic
and host resource limits remain outside this model.

## Validation

Lean 4.34.1 checks the module with
`lake -d lean build MicroCFTA.CompactEdgeRanks`.
Kernel-checked examples cover mixed-radix rank 5 over group counts 2 and 3,
nonconsecutive repeated slots `[0, 2]`, unequal repeated children, wrong
constructor, wrong arity, and an empty group domain.
No Haskell file changed. No Cabal build ran. Validation date: 2026-10-12.
