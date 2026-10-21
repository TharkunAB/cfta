# First pure rank-envelope module

The proposed module is `MicroCFTA.SourceCurrentOuterRankEnvelope`.
The selected public heads are `envelope` and `retains` ONLY. The exact eight-line header is `selected-signatures.lean.txt`.
The concrete equations remain byte-identical to `equations.md`. The definition has no supplied recursive callback.
The rank is `(count,mass)` with strict `Prod.Lex Nat.lt Nat.lt`. The seed is an extra argument to the well-founded motive.
The output is `Nat × Nat × (List Guard × Profile)`. It contains outer work, a lower-fuel maximum, and the retained output seed.
Each slot enumerates finite smaller ranks bounded by its CURRENT seed mass. It joins every numeric candidate output at that same seed.
Each row starts with the existing Parent schedule, freezes its returned mass as the slot count, and retains its local Parent fuel. The row and final body use the existing raw-constructor rebuild schedule.
The definition therefore includes the full finite W/L/Seed recipe. No smaller alternative recurrence replaces the original proposal.

The FIRST theorem proves only `mass+1 ≤ W` and retention of the ENTRY profile and alphabet.
It uses baseline `cover_ge`, `parent_ge`, `rebuild_ge`, and finite-fold work/retention laws. It needs no recursive candidate-coverage induction and no seed monotonicity theorem.
The original all-stage `stage_bounds` header remains unelaborated and UNPROVED. It is NOT a selected public head.
No coverage theorem for numeric Parent peaks, child work offsets, candidate outputs, or lower maxima is claimed in this first slice.
The exact child-fuel offset `F-3-rowIndex-slotIndex` is source-verified. Its coverage by the concrete recurrence remains a next proof target.
The empty-row and empty-slot arithmetic remains as stated in `equations.md`; no worker completion is claimed.

All physical bridges remain UNPROVED: the same global initial packet, actual intermediate Parent profile coverage, and all actual nested lower-fuel coverage.
An initial Room join and sufficient outer fuel have not been constructed or proved adequate. Fixed-width feasibility and state widening remain open.
No future success, physical state, Room, call graph, or output oracle appears in the selected API.

Source estimate for this reduced scope: concrete definition 60–85 lines; private baseline/fold facts 55–75; public headers and retention proof 20–35; imports and comments 10–15. This is a 145–210-line estimate, not a completion claim.
The HARD STOP is 250 TOTAL rendered Lean lines BEFORE further implementation OR ANY compiler. Generator recipes count. At the stop, export the complete partial source and remaining obligations for explicit review.
This package contains no implementation. No Lean, Lake, runtime, canonical, or official source job has run for it.
Any future implementation and compiler launch need separate root activation and complete source review.
The author implemented the earlier Parent/prefix native-store, child-back, closure, and local-fault foundations. This proposal does not independently re-review those proofs.
