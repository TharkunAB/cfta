# Independent actual-trace integration kernels

Timestamp: 2026-10-16 16:25 CEST.

The imported root source is `SourceCurrentAllocatedFiniteOrdinaryExecution.lean`, SHA-256 `c8d546542d20fc2005a01c364eb2c1b5c5de4849cfcdd44518dfe9faef107d57`. The current frozen file has 271 lines. The root canonical build passed with 1113 jobs. This task changed no proof source and ran no Lake build.

`execution-kernels-2.log` passed with exit code 0. It contains three kernel axiom reports and three full signatures. It has no errors, warnings, or `sorryAx`. Public declaration reports are owned by the root and are not counted here.

## Cold Empty/Empty

`cold_empty_installs_its_actual_owner` takes an arbitrary machine and equality-operation state with `Good` at the literal checked state whose native tables are empty. Initial semantic readiness is explicit. The width is eight. The request is the reserved empty domain with Empty on both sides.

The kernel computes the actual lookup, demand, and finish states. It proves the source key bounds with literal empty-input witnesses and numerical width checks. Empty-domain membership and both operand availabilities follow from existing initialization-independent facts. The body compiles definitionally to pure Empty, so it adds zero physical steps between publication/demand and finish.

The kernel constructs a two-step `PhysicalTrace`: the first source step publishes and starts handle zero, then emits the exact finish frame; the second finishes that handle and reaches pure Empty. It supplies the finish input check from the literal evaluating cell. It then applies `Execution.node_trace` with `initial_stored`, not a supplied producer certificate. Its conclusions include final `Stored`, the Empty domain and zero height, the exact returned owner cell, unchanged machine, and unchanged operation state.

## Warm repeat

`cold_then_warm_repeat_keeps_the_entire_checked_state` first constructs the cold trace above. It derives `Good` at that exact final state from the actual physical trace and the initial fields. No final validity premise is supplied.

It then computes a one-step warm trace for the same request. Lookup finds the actual returned handle, demand reads its Empty result, and the entire checked state remains equal to the cold result. `Execution.node_trace` derives the warm structural result from the cold-produced `Stored`. The final pure observation gives literal `NativeDemand.execute 2 = done Empty sameState`. All native tables, the machine, and equality-operation tables remain part of that same complete state.

## Warm edge

`actual_warm_edge_observation_constructs_its_checked_trace` begins from a legitimate warm state: initial `Good`, semantic readiness, `Stored`, resident original edge inputs, and checked key bounds. The actual lookup and ready-demand observations are explicit. These are reached protocol observations, not a completed body or result-language premise.

The kernel constructs the corresponding one-step checked `PhysicalTrace` through the current edge branch. It applies `Execution.edge_trace` to derive final `Stored`, finite ordinary result membership, and a height bounded by the minimum of both actual requested edge heights. The conditional structural input includes an empty incoming seen list. No historical edge producer is used.

## Retained attempts and scope

The first log preserves the failed attempt to decide a proposition with existential source-input witnesses and a nonexistent helper name in a redundant warm-state simplification. The final proof supplies the actual empty witnesses and uses the literal definitional warm-step equation. The source module did not change.

These kernels validate actual cold and warm branches of the current checked engine. They do not prove general finite native execution from arbitrary input invariants, result language equivalence, nonempty-seen result structure, or runtime/GHC correspondence. All initial physical assumptions remain visible in the full signatures. No Haskell source or root documentation changed.
