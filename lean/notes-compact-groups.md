# Direct-child equality grouping and slot construction

`CompactGroups` follows `Automaton.childGroups`. It starts with one group
per child position. Each input equality class selects all groups that it
touches. The source concatenates those groups, retains the others, and sorts
the result by the first position. Empty classes make no change.

`merge_positions` and `fold_positions` prove that this algorithm preserves
the complete multiset of child positions. `childGroups_positions` and
`childGroups_nodup` derive that every position from zero to arity minus one
occurs exactly once. `merge_exact` proves that a merge adds exactly its
class equalities. `childGroups_exact` proves the complete fold's equality
condition. Overlapping classes are handled by the actual merge algorithm.

`childIndex_exact` models the signed path check: exactly one nonnegative
index below the arity. `parseClass_exact` preserves position order.
`parseClasses_valid` derives the bounds required by the grouping proofs
from successful source parsing. Valid classes cannot create an empty group.
Thus `buildGroup` does not fail because grouping lost its child positions.
An empty intersection can still correctly remove an impossible edge.

`compiled_groups_exact` proves the factoring step. Selecting one term from
the intersection of each group's child domains and duplicating that term
gives exactly the child assignments that belong to all original child
domains and satisfy every parsed equality. The proof does not assume a
partition-preservation or equality-enforcement law for the source fold.

`CompactChildSlots` follows the source `addGroup` fold. Each new group
prepends its associations. The resulting list has reversed group order.
`slots_permutation` proves that this list still contains every indexed child
exactly once, with its selected value. `fromAssocs_exact` then invokes the
proved source fast paths for arities zero through three and the generic
indexed builder. No unwritten child slot remains.

`readGroup_member` models the inverse's scan of existing children in index
order. `selectedGroup_exact` proves its head-and-all-equal check.
`childGroup_read` derives exact readback for every parsed group. The
nonempty-group theorem also proves that two different selected group terms
cannot become equal through duplication into the same child slots.

Kernel examples cover overlapping classes, invalid signed paths, a nullary
edge, reversed association order, and unequal child rejection. The pinned
Lean module builds pass. No Haskell source changed.

The source normalization of the original equality constraints has its own
proofs. This adapter starts at that operation's ordered class list. The
intersection compiler and the mixed-radix fold over group ranks remain
separate components. Whole compact callback composition and runtime plan
sharing are not established by the slot theorem alone.
