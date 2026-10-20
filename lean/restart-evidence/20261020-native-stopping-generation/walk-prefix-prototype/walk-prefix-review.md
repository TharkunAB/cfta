# Exact indexed physical walk prefixes

Frozen at: 2026-10-20T18:32:21+02:00.

The sole public theorem is `MicroCFTA.SourceCurrentNativeWalkPrefix.walk_prefix_cases`. The input is one actual physically checked Trace of an ordered walk with an appended continuation. No decomposition, semantic relation, completed future call, `Good`, `Fields`, or compiler owner is a premise.

The unfinished arm retains an ORIGINAL input index and its exact lookup; the actual earlier Walk over `take index`; its ordered result list and full returned checked state; and the actual unfinished unbound callback Trace from that state to the SAME supplied final checked state. The current callback control is nonpure. Its appended continuation equals the SAME supplied remaining control. That continuation uses the ORIGINAL `drop (index + 1)` suffix and appends the earlier results before the selected callback result and the later tail results. Duplicate input values do not erase the selected index.

The completed arm retains the actual entire ordered Walk and the actual continuation suffix. Both arms retain exact fuel sums. Pure callback returns cost zero instructions. The empty walk therefore yields a zero-step Walk and the complete supplied trace as its continuation suffix.

The proof uses list induction and the official `NativeTracePrefixBind.bind_prefix_cases`. An unfinished first callback yields index zero. A completed first callback is retained while the SAME actual tail prefix is decomposed. Moving a tail index back into the original list adds one to its index and preserves the original take/drop geometry and result order. The proof never reconstructs physical checks from a separately selected raw run.

Selected strict `walk-prefix-direct-2` returned zero with an empty raw log. Selected `walk-prefix-public-1` was personally polled to terminal zero and prints the complete explicit statement, proof, and axiom report under all eight settings. The only axioms are `propext`, `Classical.choice`, and `Quot.sound`. Every job uses pinned Lean, all linters, a five-minute cap, 4 GiB MemoryMax/MemoryHigh, and zero swap. Fresh usage gates and actual inner cgroup readbacks are retained.

Counts: one generic public theorem, zero constructed heads, three actual Lean jobs, one failed elaboration attempt, and zero owned canonical jobs. The failed first strict attempt contains only two `0 + fuel = fuel` goals attempted with `rfl`; its exact source and log are preserved. No repository or canonical file was changed.

This producer supports compiled union, row, and checked-edge walk analysis. It does not yet attach the optional-binder site to a captured compileMu owner. Generated encoded source writers are also distinct from original-program binding ancestry. Neither ancestry is asserted here.
