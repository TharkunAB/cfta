# Independent computed rank and fuel review

No material defect was found in the reviewed final sources.
`IntersectNumericRank.lean` has SHA256 `be61b2ae25e91c86427cdb04c8406135090f32f9a57018abe95123fb7ee34f2e`.
`SourceRecursiveIntersectionComputedFuel.lean` has SHA256 `049ced72723b827793b0921a93117ae5cef046b4833130c547e9c84c863ca2b1`.
This review changed no production file and ran no canonical build.

## Numeric rank

`combine` at NumericRank line 15 uses the radix `width + 1`.
`combine_lt` needs only the CHILD low digit to fit.
A larger parent high digit dominates every fitting child low digit, even when the parent low digit is zero.
`combine_bound` uses a strict high capacity and an inclusive low bound.

`rank` at line 42 nests the exact four fields: closed-root size, unseen occurrence count, local weight, and swap phase.
The unseen radix is the literal pair-list length, with duplicates retained.
The local radix is `2*bound + 1`; the phase radix is one.
`parts_bound` at line 50 applies the uniform weight law to every input tag.
This permits arbitrary edge child lists.
An empty zipped list still has edgeWeight one.
A nonempty zip has maximum child weight sum at most `2*bound`.
The two node operand weights also fit this radix.

`rank_bound` at line 78 uses full-size bounds for the two roots and uniform local-weight bounds for all tags.
The resulting capacity is exactly `2*(2*bound+1)*(pairs+1)*(2*bound+2)`.
The strict rank bound leaves room for the semantic rank-plus-one fuel.
`root_decrease` at line 94 permits the child to restore every lower digit.
`local_decrease` at line 105 retains equal root-size sum, including rootswap, and follows the exact LocalStep lexicographic decrease.
No distinct pair premise, bounded identifier magnitude, result annotation, or completed execution is hidden in these lemmas.

## Source instantiation

`ComputedFuel.ceiling` at line 18 uses the full tagged carrier length `1+4*N` and its squared literal pair count.
Its monotonicity is direct natural-number arithmetic.
`schedule_numeric` at line 34 uses the actual mass-based bounds with the SAME finiteInput interface.
The size and local-weight bounds come from current causal Stored and Facts.
Its rank and pair-list field equations are definitional.
It instantiates `IntersectSchedule.call_numeric`, whose public assumptions are actual structural decrease and readiness.
That proof uses natural-number strong induction on the initial numeric rank.
It does not take a completed execution or semantic Completes as an input.

`initial_numeric` at line 66 derives source semantic closedness from the actual coherent cached free fields.
It accepts full Original source Mu/reference/union/ordinary syntax.
The literal payload mass includes both Mu probes.
`initial_requiredFuel_le` at line 86 first produces successful execution at the computed ceiling.
It uses the supplied Completes proof only to name the already-defined least successful fuel in the conclusion.
There is no successful checked receipt, future output mass, or future query width hypothesis.
The bound is intentionally conservative.
The rank counts semantic recursive depth; the instruction budget separately expands ordered branching.
It is not an allocation count or a runtime estimate.

## Independent imported checks

The reviewed final production strict logs are empty.
Their canonical logs report 72 and 1180 successful jobs.
The latter replays the existing ClosedCompletion warning.
All 15 public axiom/full-signature pairs passed imported strict checking.
All three integration pairs passed strict checking with no diagnostics and only standard axioms.
The full explicit/proof/universe/deep-term settings are present in both standalone sources.

The first kernel doubles a literal pair inventory and proves its unseen occurrence count doubles.
It derives strict numeric descent for actual nodeRows and edgeChild LocalStep constructors with that duplicated inventory.
The second starts from actual semantic NodeReady plus the reset condition.
It derives the strict root-size decrease, permits the empty domain to restore the full pair count, and proves the subsequent canonical rootswap decrease.
It does not supply the desired rank decrease as a premise.
These arithmetic kernels concern semantic steps; they do not claim a constructed checked physical reset trace.

The third kernel builds its own source with two nonidentical ordinary roots and different literal numeric guards.
It derives its causal store from the full source ResultMass producer and its source counter forecast from FreshAllocationBudget.
It produces semantic success at a ceiling from the ORIGINAL syntax budget, not the measured final source counter.
It then derives least-fuel and instruction-credit ceilings.
It does not receive any source completion, native receipt, or later result bound as an input.
This complements the other owner's distinct-Mu/union fixture.
The previous mass-input component separately tests unissued reference tags: they have unit mass without availability.
No reversed comparison from metadata-sensitive sizeOf to structural mass is used.

The first failed integration draft is preserved.
It had two local notation errors: a Prop-valued guard instead of Bool, and a missing unfolding of the static source-node forecast.
No reviewed production change was needed.
These modules close a computed semantic-fuel obligation.
They do not alone prove one initial forecast for an arbitrary serial caller, general selected outer convergence, or Haskell runtime correspondence.
