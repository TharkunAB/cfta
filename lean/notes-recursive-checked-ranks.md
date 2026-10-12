# Recursive checked-rank producers

`MicroCFTA/RecursiveCheckedRanks.lean` extends the finite and composite flag
models. It proves local product, ordered choice, and pay certificate laws.
It also proves the complete public inverse for one infinite recursive family.
It does not assume a whole callback soundness or completeness law for that
family.

## Source correspondence

The source sites are:

- `Gen/Internal/Recursive.hs`, `staticTerms`: convert finite ranks with
  `planPosition`, retain flags, and sort class positions.
- `productTerms`: combine flags with conjunction and positions with
  `productPosition`. Sort the result.
- `choiceTerms`: add counts of earlier alternatives at the same size. Retain
  the branch wrapper for whole terms. Sort the result.
- `payRecursive`: add one to each position's size. Retain its class rank.
- `labelRecursive`: require the exact stored symbol. Read its children with
  `LabelledView`. Add one to the size through `payRecursive`.
- `Gen/Internal/Recur.hs`, `tiedPositions`: require a private `Recursion`
  root. Pass its sole child to the body's whole-term callback.
- `recursivePositions`: add the counts of all earlier sizes.
- `boundedStatic.boundedRanks`: discard candidates above the bound. Preserve
  the global rank of each remaining candidate.

`product_checked` derives exact application replay from each child's local
class bound and certificate. It uses the proved source product split inverse.
`product_complete` proves that each certified pair is emitted. `choice_checked`
uses the actual ordered choice split inverse. `pay_checked` proves exact replay
after the size shift. These are constructor laws. They retain local child
contracts because an arbitrary callback is not necessarily correct.

## A complete guarded recursive family

The body has an empty `pure` alternative at branch zero. It has `arity` unary
alternatives after that branch. Alternative `branch + 1` labels the recursive
occurrence with `label branch`. A label pays one size unit. Every occurrence
retains its private `Recursion` wrapper. This corresponds to an equal-weight
`oneof` of `pure` and the labelled recursive occurrences.

The model permits repeated user labels. Private branch wrappers still
separate the members. It therefore does not assume that user labels or decoded
values identify engine members.

`classCount` is the actual choice sum recurrence. `class_count` proves that
size `n` has `arity ^ n` members. `unary_choice_offset` proves that the source
choice offset reduces to `branch * classCount arity n`. `unary_label_term`
proves the concrete label and recursion wrapper shape.

`sourcePositions` implements the composed source callback. It checks the
private recursion root, private branch, stored user label, and sole child.
It descends into that child and applies the source size and choice offsets.
`source_positions_eq` proves that this recurrence computes the exact branch
word position. `source_sort_identity` proves that sorting leaves its empty or
singleton result unchanged. `source_views_complete` and `source_views_checked`
prove completeness and certificate soundness in whole, spine, and labelled
views. All three see the recursive root as one opaque term.

`selectWord` uses the requested class size and quotient/remainder operations.
It does not construct a class's member list. The proofs establish both inverse
laws, strict class bounds, decoder totality, and unique word ranks.
`positions_exact` equates the actual candidate position with direct replay.

`rows_through_checked`, `rows_through_complete`, and `rows_through_ordered`
prove the bounded callback. `bounded_rank_interval` proves that selection
succeeds exactly at `0 .. total - 1`. `bounded_rank_unique` proves that two
ranks cannot select the same complete private term. `bounded_language_exact`
proves that these terms are precisely the valid branch words within the size
bound.

For positive arity, each size has a positive finite count. A rank's own size
prefix must contain that rank. `select_global_total` derives finite selection
from this fact. `global_checked`, `global_complete`, and `global_ordered`
derive the actual recursive callback contracts. `public_rank_exact`
instantiates `CheckedRankQueries.rankOf_exact`, including signed rank rejection
and the checked-symbol shortcut. No whole callback law is a premise.

The binary kernel example has 256 members at size eight. The branch word
`[1, 0, 1]` has class position `(3, 5)` and global rank 12. Another kernel
example retains ranks 1 and 2 when both unary alternatives use the same user
label.

## Efficiency and remaining boundary

The callback inspects the requested term. Class decoding uses counts and
integer division. The rank offset uses only coefficients before the requested
size. No operation in this model enumerates all earlier terms.

`selectGlobal` uses a finite sufficient prefix to prove termination. It is a
semantic model of successful lazy size-class search. It is not a cost model
for Haskell evaluation or its cached sparse tables. The Lean list prefix can
be larger than the prefix forced by Haskell. The module makes no asymptotic
runtime claim.

General recursive products and ordered choices still need a shared induction
that connects each arbitrary tied body's value index, term index, and callback.
The new constructor laws identify the needed local facts: matching class
counts, valid returned positions, and exact selected child terms. The family
proof derives those facts for its whole recursive knot. It does not establish
them for arbitrary `recur` bodies, keyed recursion, recursive joins and chains,
imports, or all finite `planPosition` constructors. Existing `SizedRank` proofs
still state their separate shared/sized plan and concrete table boundaries.

All counts and positions here use natural numbers. Source signed input rank
rejection is included. Machine `Int` choice indexes and host resource behavior
remain outside this model. This work found no new production defect.

Validation on 2026-10-12:

- Lean 4.34.1: `lake -d lean build MicroCFTA.RecursiveCheckedRanks` passed.
- Kernel evaluation checked the two examples.
- No Haskell file changed. No Cabal build ran for this module.
