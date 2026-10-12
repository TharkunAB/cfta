# Finite plan positions and recursive term conversion

`SourcePlanPositions` models every constructor case read by
`Ranked.Internal.Size.planPosition`. It erases values because that operation
reads counts and sizes. Select and on-demand select have size one. Pure has
size zero. Pay adds one to the selected size and preserves its class rank.
Shared and mapped plans delegate to the inner plan. Choices add earlier
class counts. Products use the actual mixed-radix split and class offsets.
Sized plans use the checked finite class table from `PlanVariants`.

`position_complete` proves that every ordinary rank below the derived count
has a position. `position_none` rejects every other natural rank.
`position_exists_iff` therefore validates the source's outer cardinality
check as well as its constructor dispatch. Public signed-rank rejection is
in the separate query model.

`position_replay` proves that every returned position reads exactly its
original ordinary rank from an independent compositional class list.
`position_injective` prevents two ordinary ranks from collapsing to the
same class position. `class_rank_bound` also proves that every rank stored
in any class is valid, including entries not reached through that first
conversion theorem. `every_class_selection_total` thus excludes the
`staticTerms` impossible-outcome error when the original finite selector is
total. It derives the rank bound rather than assuming index validity.

`convert` follows the source checked-rank list comprehension. It retains
the flag and filters only failed position conversions. `sorted` then uses
the source lexicographic size, rank, and flag order. `sorted_member` and
`sorted_valid` retain every valid occurrence and derive its class bound.
`sorted_checked` transports a local finite callback certificate to the
recursive term index. `sorted_complete` retains every certified member.
These last two theorems retain the original callback's local certificate;
the finite and composite callback modules establish those separately.

The source n-ary choice is represented by right-associated ordered binary
choices. Its count and class prefixes use the same sums. Sized rows use
bounded class lists; zero-row omission and offset replay are proved in
`PlanVariants`. Runtime `PlanShared` cached counts and class fields must
agree with their inner plans. The source constructors establish these
fields, but this module does not model arbitrary manually inconsistent
internal records. Physical arrays, sparse-table construction, and lazy
sharing remain representation interfaces.

The independent class lists specify index contents. The source position
worker follows one rank and uses child counts. This module makes no claim
that the source materializes those lists, and gives no new runtime bound.
Kernel examples cover pure, paid alternatives, and paid products.
The pinned Lean build passes. No Haskell source changed.

`SourcePlanPartition` closes the reverse direction. `member_position` derives
the size of every independently listed member. `class_size_unique` excludes
membership in two size classes. `class_nodup` excludes repeated ranks within
one class. `position_class_lookup` then proves exact conversion from every
stored class position back to itself. `position_iff_lookup` exposes both
inverse directions without an assumed partition invariant.

`maxSize` computes a structural finite upper bound. `class_size_bound` proves
that no nonempty class occurs above it. `allRanks_perm` proves that traversing
all classes through that bound gives a permutation of `List.range (count
plan)`. `class_count_total` derives equality of the complete size-count sum
and the original count. Empty classes and zero-size members are included.
The example `[1, 0, 3, 2]` checks the distinct size-major order of a product.
