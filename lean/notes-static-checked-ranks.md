# Finite checked flags and exact public inverse ranking

`StaticCheckedRanks` models the checked-symbol flags in the finite
`StaticCandidateRanks.Source` fragment: pure, hole, indexed source, map, pay,
application, binary retained choice, and flexible label. It handles whole,
spine, and labelled views. `erasure` proves that removing the flags reproduces
the existing candidate callback exactly.

`checked_sound` derives a selected original outcome and an exact requested
projection from every true flag. Hole callbacks certify only the original
placeholder. Products require both child flags. Choices preserve child flags
and add source offsets. A flexible label requires both its child certificate
and equality with the stored symbol. `public_checked_sound` and
`public_view_checked_sound` supply the public `CheckedSound` contract.
`public_keep_exact` proves that the public shortcut is safe for this fragment.

`StaticRankQueryExact` supplies the other finite producer obligations.
`certified_complete` proves that every selected original outcome appears as
`(rank, true)` under its own projection. Its `MatchesSelf` premise is local:
each label matcher must accept the symbol stored by that label constructor.
A kernel example shows that a matcher that rejects its own symbol can omit a
selected term. The proof does not assume callback completeness.

`callbacks_valid` derives strict ascending order and cardinality bounds for
all candidates, including unchecked candidates. Products use valid
mixed-radix blocks. Choices place each shifted right block after all left
ranks. Labels retain the original rank sequence. These proofs do not assume
whole-callback order or bounds.

`public_ranks_exact` and `public_ranks_distinct` establish exact matching ranks
without rank duplication. `rank_query_exact` instantiates the actual public
filter and first-rank selection from `CheckedRankQueries`. It returns the
least rank that replays the requested term. `rank_query_rejected` rejects
exactly terms absent from all selected outcomes. `selected_query_succeeds`
proves that each selected member has an in-range successful public inverse.
Equal term values can still belong to different source members; their valid
ranks remain distinct and the inverse returns the least one.

The signed replay adapter retains successful term selection and maps decode
failures to `Unit`. The separate public-query model retains construction
error payloads. These proofs do not establish flags for composite joins or
recursive callbacks. They do not prove that every external flexible matcher
satisfies the local `MatchesSelf` condition. No Haskell change was required.

Validation on 2026-10-12: the pinned Lean 4.34.1 build of
`MicroCFTA.StaticRankQueryExact` succeeds with 68 jobs. No additional axioms,
`sorry`, or `native_decide` are used.
