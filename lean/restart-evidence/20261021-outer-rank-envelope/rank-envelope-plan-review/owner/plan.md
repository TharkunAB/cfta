# Concrete finite rank envelope

This is a source-only design. It does not define or prove a Lean declaration.
The proposed module is `SourceCurrentOuterRankEnvelope`. It has three public heads: `envelope`, `retains`, and `stage_bounds`.
The output is `Nat × Nat × (List Guard × Profile)`. Its fields are outer work `W`, a lower-fuel maximum `L`, and the retained output seed.
The rank is `(count, mass)` with `Prod.Lex Nat.lt Nat.lt`. The seed is an extra function argument. It need not decrease.
`WellFounded.fix` uses `(Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf` and motive `fun _ => Seed → Nat × Nat × Seed`.
At each numeric child slot, enumerate all strict smaller ranks `(a,b)` with `a ≤ count` and `b ≤ currentSeed.profile.mass`.
Evaluate every candidate envelope at that SAME current seed. Join their output profiles with `cover`, their alphabets by list append, and their two numeric fields with `maximum`.
A slot adds `1 + maximum childW` to work. It retains the maximum child lower fuel and the joined seed.
At each numeric row, first apply the existing `Schedule.parent`. Freeze its profile mass as the number of child slots for that row.
Fold the slot step exactly that many times. Add `1 + walkW` to row work. Retain the existing Parent uniform fuel and every child lower maximum. Apply `Schedule.rebuild` to the child-fold output.
Fold the row step exactly `mass` times. Add one body step and apply one final `Schedule.rebuild`.
The equations in `equations.md` are part of this proposal. No future state, Room, successful run, supplied call graph, or recursive callback is an input.

The literal worker sends fuel `F` from node demand to body. An ordinary body sends `F-1` to rows, including empty rows.
After `j` preceding row suffixes, a selected row sends `F-2-j` to its edge and descendants. The inherited prefix and children phase retain that fuel.
After `k` preceding child suffixes, the head child node receives `F-3-j-k`.
Thus `stage_bounds` must prove `childW + 3 + j + k ≤ W`. A row with no children costs one row unit. Empty rows and empty walks succeed at fuel zero.
The sum recurrence is an overestimate. It pays for every row and child slot even though the worker decrements suffix fuel by only one at each step.
`retains` proves `mass+1 ≤ W` and retains the input profile and alphabet. It supplies positive work even for numeric mass zero.
`stage_bounds` quantifies over ALL numeric row and slot prefixes. It retains each Parent profile, each slot seed, each candidate output profile and alphabet, each Parent fuel, and each recursive lower maximum.
All joins use the literal chronological accumulator. Neither seed monotonicity of `envelope` nor equality between a physical profile and a numeric seed is assumed.
The proof uses finite-list membership, `cover_ge`, `cover_member`, and `maximum_member`. A candidate membership proof supplies the local strict-Lex proof to the private fixpoint.

This foundation proves only pure finite numeric coverage. It does not prove that actual physical phases fit these numeric stages.
The future physical proof must retain ONE original initial packet and its literal `Reached` cuts. Rerooting at a child needs a separate child-schedule Room proof.
The numeric theorem retains all constructed intermediate Parent peaks. Its correspondence with actual physical peaks remains unproved.
The numeric theorem retains all constructed nested lower-fuel maxima. Its coverage of all actual lower-stage calls remains unproved.
The initial resource bridge must prove root-schedule domination or a finite initial Room join that covers the controlled peaks. No per-future Room premise is permitted.
No adequate fuel, fixed-width feasibility, state widening, or completion theorem is claimed.

Future source budget: definition and private finite steps 65–80 lines; private fold laws 60–75; public headers and proofs 80–95; imports and comments 10–15. Total target 215–250 rendered Lean lines.
The HARD STOP is 250 TOTAL rendered Lean lines, before further implementation or ANY compiler. Generator recipes also count. A complete partial source and remaining obligations must receive explicit scope review at the stop.
No implementation, Lean, Lake, runtime evaluation, canonical job, or official source edit is authorized by this plan.
The author implemented the earlier Parent/prefix native-store, child-back, closure, and local-fault foundations. This is not an independent review of those proofs.
