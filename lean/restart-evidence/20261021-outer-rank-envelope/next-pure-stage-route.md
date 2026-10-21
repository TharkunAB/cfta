# Next pure stage-bound target

This is a source-supported route. It adds no theorem or compiler command.
The exact unproved target remains `theorem stage_bounds` in `rank-envelope-plan/proposed-signatures.lean.txt`, lines 9 through 42.
The checked `retains` theorem alone does not imply that target.
First derive a private downstream one-rank equation from public `envelope`, `WellFounded.fix_eq`, and definitional reduction of the finite recipe. Resolve attached membership proofs by proof irrelevance where needed.
The current helper names are private. Do not assume that their short names are available in another module. Do not copy the envelope definition or change the frozen module to avoid this access question.

The sealed Lean source copies provide `List.range_add` and `range_succ` in `rank-envelope-plan/sources/T4-Range.lean:182-187`.
They provide `List.foldl_map` and `foldl_append` in `rank-envelope-plan/sources/T3-Lemmas.lean:2681-2683` and `2723-2724`.
Split the original row and slot ranges at the selected index. The steps ignore their range index, so the mapped suffix shift can reduce without changing the literal seed accumulator.
Keep the slot count fixed at the SAME post-Parent mass for the selected row. Recompute the candidate mass bound from the CURRENT slot seed.
Use finite-fold retention, `cover_member` and `maximum_member` to cover every selected candidate output and lower fuel. The proposed child-work inequality is childW+3+rowIndex+slotIndex <= totalW.
The defining equation, all-stage numeric inequalities, and all actual-state correspondence remain unproved here.
Before future implementation, select an exact bounded source scope and preserve the full source at its stop. The current module's compiler checks do not authorize any future command.
