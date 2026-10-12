# Repeated open keys and heterogeneous integer groups

`OpenGroupComposition` connects source key grouping, finite static merging,
point closure, parent label callbacks, and retained integer mass. It has no
shared-width premise for all alternatives. Each group uses its own width,
formula, and point table.

The concrete original fragment is `OpenIntegerSource.Recipe`: pure values,
integer leaves, maps, pays, and bare applicative spines. Each successful
bare-spine compilation has one original static outcome. `compileOriginal`
executes that compiler and retains its actual keys. `original_width` derives
the typed private term's placeholder count from the successful compilation.
It does not assume a codec inverse or a declared template width.

`Signature` keeps the observation identity, coordinate width, formula, and
optional point count. The observation identity is an opaque natural token.
Its equality represents equality of the source observations. The existing
`GroupPositions` proof handles the separate first-position table. The source
comparator is a parameter because count and mass preservation do not depend
on which order it gives the groups.

`groups` executes the existing source-order key partition and group sort.
`groups_perm` retains each input occurrence. `groups_homogeneous` derives the
complete common key of each nonempty group. Repeated recipes and repeated
keys do not collapse original occurrences. `selected_width` derives the
common width inside each group from its actual member keys.

The static term model follows `mergeBucketGroup`. A positive singleton keeps
its original template. A multi-original group uses `frequencyStatic` with
local `Choice` indexes. These indexes belong to the merge, rather than to
the outer choice's unfiltered branch list. `frequencyCandidates` follows the
source callback dispatch in all three views. `candidates_complete` proves
that every original is still discovered after integer filling. Positive
incoming masses are the source-success condition for this merge. The term
lemmas also hold for the same mathematical templates outside that condition;
they do not turn an invalid mass into a successful Haskell merge.

`pointCandidates` implements `pointsStatic` over the merged source.
`group_ranks_exact` gives all and only the original-member × point ranks.
`grouped_ranks_exact` derives its key and dimension premises from the actual
partition. `points_rank_bound` rejects any rank outside that product count.
Each group can have a different product radix.

`parentCandidates` models `labelOutcomeTerms`: it checks the parent symbol
and asks the inner source for `LabelledView` children. `parentSelected` uses
the actual `SupportTerms.labelTerm`. The existing projection proofs derive
its shape and coordinate count. `parent_points_complete` and
`parent_points_sound` cover closure after `labelStaticMatching`.
`parent_integer_match` uses the real `exactLabel_matches` theorem.
Successful source label substitution remains explicit. No arbitrary
matcher-completeness premise is hidden as an assumed codec inverse.

`settleOne` and `settleAll` execute the finite one-open-child settlement
query, source-order traversal, first-error propagation, and zero-count drop.
The query is the renamed child formula conjoined with translated parent
formulas. The model uses `LatticeAPI.points`. It leaves the source's
`GenError` wrapping and readable-name diagnostic retry to the existing
counter boundary. A retained record stores the actual returned point table.
`settleOne_fields`, `settleAll_sound`, and `settleAll_complete` prove that
provenance. `empty_settlement` proves that dropping a zero table removes no
replay member or mass. `settleAll_stream` includes the drop case in the
complete weighted stream equation.

`settled_ranks_exact` derives all group and counter premises from the
successful driver result. `settled_parent_ranks_exact` additionally applies
the actual parent label callback. `settled_parent_every_rank` proves that
every integer in the complete product interval has a decoded view and an
inverse rank. `settled_cardinality` identifies the full
output stream length with the sum of stored original-count × point-count
fields. Visible terms can coincide after labelling, so the theorem returns
all original ranks for that term. It does not claim distinct decoded values
or distinct labelled views for every member rank.

The mass model retains each original's incoming rational mass.
`settled_expands` proves that the outer bucket mass cancels its normalized
original sampler exactly. Each original then receives its source retained
share and a uniform draw from the actual parent table. The original's
occurrence token is carried through the distribution; it need not be a
unique decoded value.

`parent_group_event` connects that expansion to the original finite tuple
domain filtered by the parent formulas. It uses actual child and parent
counter success. `heterogeneous_event` combines the equations through the
source group partition. `heterogeneous_conditioned` proves the final
normalized event distribution. `settled_conditioned` derives the parent
counter successes from the executed driver. `original_record_from_parts`
derives a joined key's point count from actual primitive component counters
and their stored records. `settled_conditioned_from_parts` uses that fact,
so it needs no separate joined-count postcondition.

`choice_members` connects the result to `OpenChoiceRouting.members`. It
proves that summing each group's original-count × point-count equals the
sum of the input occurrence counts. `group_cardinality_sum` supplies the
partition arithmetic. Thus repeated keys cannot lower a Uniform branch's
weight by silently deduplicating originals.

The fragment does not yet extract arbitrary preexisting static sources,
products between already multi-group families, or every nested constructor
recipe into `Original`. Those products have nonzero component indexes and
need the existing general keyed-join callback adapter. Parent guard
translation is covered separately by `ParentGuardFormula`; this module
accepts its translated formulas. It does not turn a solver Unknown into
truth. The zero-width direct-reader branch and the choice to leave a
symbolic parent open are separate source control paths. The point-table
stream represents their finite eventual closure. Final observation
regrouping can reorder members and adds its own merge wrappers. Its
permutation and mass laws are separate from the local ranks proved here.
Recursive and unknown-point mass fallbacks are excluded from the finite
probability theorem.

Validation: pinned Lean 4.34.1 builds the module in 90 jobs with 52 theorems.
No admitted declaration or native proof evaluation is used.

The retained public probe `repro/HeterogeneousOpenGroups.hs` compares symbolic
sources with finite pools. It exercises repeated identical open keys with
different decoded values, widths one through three, weighted and Uniform
choices, pays, and parent restrictions. All 12 cases pass. The probe checks
176 complete term-rank preimages, global and size counts, PMFs, and exact
sampler distributions. It runs inside the project Nix environment. Its log
is `/tmp/microcfta-heterogeneous-open-groups.log`. This source check covers
additional measured-node callers; it is evidence, not an extraction proof
for constructors outside the kernel fragment. No production Haskell changed.
