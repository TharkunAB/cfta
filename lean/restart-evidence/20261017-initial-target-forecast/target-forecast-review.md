# Initial interleaved Target forecast

Reviewed at 2026-10-17 10:27 CEST.

The source SHA-256 is `49034867811b71e39f82af12e75f00cf6c855971cac4adf1219a2ab7da7614aa`.
The module proves a pure numeric schedule.
It does not construct a successful interleaved Target execution.

`scalar p` is the maximum of the node counter, edge counter, and causal mass fields.
`operand path count p` replaces those three fields by the complete Operand work ceiling.
It preserves the domain field.
The Operand work ceiling retains the initial scalar through projection and Merge.
No projected future height is used.

`foldProfile` follows the literal Target worker order.
It forecasts the current path Operand first.
It then forecasts the tail Fold at that returned Operand profile.
It finally applies the native resource forecast step at the complete tail profile.
The base forecasts only the original seed Operand.
`targetProfile [] p` returns exactly p.
The componentwise inflation laws retain every initial bound through these exact chosen profiles.
The proof does not require general Operand or Fold monotonicity.

`Reserved` contains only finite numeric room tests over profiles computed from the initial profile, path list, and forest count.
A nonempty Fold requires the tail reservation at the head Operand profile and Room at the exact tail-return profile.
The predicate contains no future state, actual graph, callback, desired result law, or execution premise.
A base Fold has no native query and therefore has reservation True.
`TargetReserved` preserves the distinct empty Target case.
The stronger `reserved_of_final_room` test uses the final computed forecast profile.
That profile is a pure function of the initial data, not a supplied actual final state.
Its room test implies all earlier scheduled query-entry tests through componentwise inflation.

`operandFuel` is the maximum of projection work, projection read, Merge work, and selection fuels at one exact Operand entry profile.
`queryFuel p` is its computed native instruction bound plus the final pure execution step.
`foldFuel` takes the maximum of the head Operand, tail Fold, and exact tail-entry query ceilings.
The literal worker passes the same five fuels to each local call, so the maximum is the required shared ceiling.
This is not a bound on the sum of all Target execution instructions.
`targetFuel [] p` is exactly zero.
The lowering lemmas keep every local path, forest count, and reached profile exact.

The 43 public declarations have full imported signature and axiom probes.
The three pure integration checks cover a concrete empty Target, a three-path interleaved profile schedule, and its common five-stage fuel ceiling.
The three-path check retains the exact sequence of three Operands and two queries.
It derives both query-entry rooms from one initial Reserved predicate.
These are arithmetic schedule checks, not actual Target completion checks.
The source cap depth is separate and remains in MixedTarget.foldDepth.
No Haskell source changed and no new Haskell defect was found.

The next actual producer must construct Operand, tail Fold, and native query receipts in this order.
It must transport Frame, inventory, global memos, physical Merge Stored, caps, and Fits across the same actual states.
It can use this initial reservation and shared fuel ceiling after that construction.
That successful interleaved Target producer remains open at this checkpoint.
