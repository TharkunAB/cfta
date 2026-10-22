# Minimal proof route

Use outer strong induction on active-cluster length and a local list induction on the remaining scan tail. Nat.strongRecOn has its actual public signature in NatInduction218–250.
This is the same well-founded macro ordering as the earlier lexicographic plan, decomposed into two elementary inductions. No custom relation, new graph or fuel bound is needed.
A local execute-prefix composition fact is required: if H16.execute used control before = .yielded next middle, then execute (used+rest) control before = execute rest next middle.
Prove that fact by induction on used and literal H16 step cases. It is not already exported by H16. It supplies no future run or callback.
The local scan-boundary lemma generalizes pivot, remaining, incomparableReversed, keptReversed and actual current before state. Every operand/accumulator member lies in fixed rows.
Its conclusion gives a positive consumed prefix that yields .cluster next newKept at an actual after, with the full current packet/effects and membership still in rows.
It also proves next.length < 1+remaining.length+incomparableReversed.length and next.length+newKept.length <= 1+remaining.length+incomparableReversed.length+keptReversed.length.
For remaining=[], one literal scan step yields cluster(incomparableReversed.reverse)(pivot::keptReversed). Both length facts follow directly.
For candidate::tail, one literal scan step enters .comparison with .call(pivot,candidate)[] at the SAME current state.
List.mem_filter supplies both literal parent-row memberships and equality to the fixed symbol. Apply H15.original_rows_complete with the SAME parent packet twice.
H15 supplies the actual completed comparison, SAME result/after, current invariants, effects and the SAME initial-to-after global Trace. It assumes no future comparison completion.
Compose source growth/history through this actual Extension to form the next H15 packet. Trace.next_le and the original Room provide every current Room; do not reserve or reset a child/current cache.
Apply repaired H16.comparison_lift to choose 0<used<=comparisonFuel and stop exactly at its inline yielded resume. Never substitute the entire supplied comparison fuel.
Candidate identity is tested first. On equality, drop the candidate and apply the tail induction with unchanged pivot/inc/kept.
Only if that test fails, pivot equality promotes candidate and immediately yields cluster(candidate::(inc.reverse++tail)) kept. Its active length is strictly smaller.
When both tests fail, apply tail induction at scan pivot tail (candidate::inc) kept. The remaining length decreases and the total active budget is unchanged.
Use the prefix composition fact to join entry, comparison and recursive worker prefixes. No native microstep rank or enclosing successful-run assumption is used.
For the outer cluster theorem, generalize active candidates and keptReversed, their membership in rows, and the actual current packet. Bound final kept length by active.length+keptReversed.length.
At cluster[], execute1 returns reverse keptReversed; preserve all invariants by reflexivity. At pivot::tail, take its literal step, the scan-boundary result, then the strong IH at strict smaller next.length.
The scan-boundary total-size inequality gives the final length bound. List.mem_reverse/mem_append and length_reverse/length_append give the membership/arithmetic facts without Sublist.
Compose Extension.trans, Cache.extends_trans and FlatMemoThunk.Returned.trans at consecutive actual states. Final Good/Contextual/SemanticReady/Stable/Idle and global Trace are the final actual packet.
The SAME global Trace is an H15 output at each call. Do not replace it with a new refl history at comparison entries or invent a native Receipt on a hit.
At most two new private helpers are proposed: execute-yielded-prefix composition and scan-boundary completion. All other local bookkeeping stays inside them or cluster_complete; no new public datatype/predicate.
Honest estimate:220–320 ordinary source lines including the eventual full public header and both resource-aware helper statements. Proposed HARD STOP350 before further machinery/checks; root must approve the exact header and source scope first.
The earlier155–210 estimate omitted some generalized worker packet and accumulator bookkeeping. Do not compress or split machinery to conceal the revised estimate.
All proof declarations keep default limits and all linters. If the exact helper/packet scope exceeds the proposed stop, preserve the partial draft and request review before adding code.
