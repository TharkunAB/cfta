# Source route for the two-head first slice

Use `WellFounded.fix` with motive `fun _ : Nat × Nat => Seed → Out`. The recursive argument then accepts a smaller rank and any current seed.
The installed relation is `(Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf`. `WellFounded.fix_eq` supplies the one-rank equation.
Use the attached candidate list only to derive each local strict-Lex proof. Its recursive values have no assumed output law.

For the selected theorem, every slot seed retains its entry by `cover_ge` and the left part of list append. The theorem does not need `cover_member` or a candidate-output induction.
Every Parent stage retains its input by `SourceCurrentOuterInitialSchedule.parent_ge`. Each raw rebuild retains its input by `rebuild_ge`.
`List.foldlRecOn` in installed `Init/Data/List/Lemmas.lean:2838–2843` transports that seed-retention invariant through the finite slot and row folds.
The existing `Le.trans` and ordinary list-subset composition combine the same seeds. There is no new public predicate or store framework.

Each row work update is `oldW+1+walkW`, hence at least `oldW+1`. Relate the real row fold to the counter fold `fun n _ => n+1` by `List.foldl_rel` at lines 2896–2905.
`List.foldl_add_const` at lines 2923–2929 and `List.length_range` in `Init/Data/List/Range.lean:162–163` make that counter equal to `mass` at initial counter zero.
The final body unit gives `mass+1 ≤ W`. No shift-of-range prefix theorem is needed in this first slice.
The existing range-fold recurrence remains unchanged. No replicate-list alternative is selected.

These are source-verified APIs and a proof plan. They are not an elaborated proof. No Lean or runtime check has run.
