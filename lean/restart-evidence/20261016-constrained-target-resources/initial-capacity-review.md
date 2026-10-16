# Independent review of initial Target capacity

Reviewed 2026-10-16 20:48 CEST.

Verdict: no material defect found. Final source: `SourceCurrentAllocatedFiniteOrdinaryTargetInitialCapacity.lean`, SHA `ce362b328038621201095e2670f75251f2464fe76ea36c1e6254c44309787c63`.

This module proves a stronger universal prefix-plan adapter than the previously reviewed construction of one complete Target. The earlier `target-independent-review.md` and manifest remain unchanged.

`stable_unique` evaluates two stable witnesses at the same componentwise maximum of their five bounds. Equality of the literal worker observations identifies the result, complete checked state, and Merge memo. `operand_unique` and `fold_unique` derive stable witnesses from the supplied raw completed graphs. They require no semantic law, final invariant, capacity, or deterministic-state oracle. Their scope is the modeled serial worker and completed graph.

`fold_capacity` performs induction on the remaining path list. In a nonempty case it constructs the current head operand from the legitimate initial invariants. Actual supply bounds and total initial headroom derive the shorter tail headroom. The inductive plan applies at that head's exact returned state. Any other raw completed head is equal in all returned fields by `operand_unique`, so the same tail plan applies there. For the query entry, the proof constructs only the strictly shorter tail. `fold_unique` aligns its return with any supplied raw earlier tail and transports its final capacity to that exact query entry. The proof never requires the current query to complete and never constructs or assumes a completed enclosing Target to establish its plan.

`target_capacity` handles the empty case trivially and restricts a nonempty Target to its literal seed and remaining paths. The initial assumptions are the same causal stores, physical and semantic readiness, current admission, global validity, original forest profiles, and numeric total headroom used for constructive resource completion. No reached capacity plan, future WordRanges predicate, result profile, or semantic callback is an input.

The old `TargetCapacity` plan quantifies only over actual completed earlier Operand and Fold graphs. It does not assert capacity after an arbitrary blocked or failed instruction. Combined with `TargetCapacity.target_ranges`, it now derives the old full raw-prefix word plan from these initial-only budgets. The older adapter derives the actual earlier domain, availability, readiness, and store facts at those same returns. The finite ordinary domain continues to exclude Mu, references, and explicit unions. Guards and equality classes remain unrestricted.

Imported validation:

- `initial-capacity-public-1.log`: all five public declarations passed full-signature and axiom checks. Only standard logical axioms occur. No warnings or `sorryAx` occur.
- `initial-capacity-kernel-1.log`: one integration theorem passed on its first direct imported check. It derives a three-path `TargetCapacity` from initial total budgets, derives `TargetRanges` through the old adapter, and obtains both capacity and full native WordRanges for any actual earlier head and shorter tail. The extra old conditional Merge domain store is derived from the initial Merge profile store with `Profiles.domain`. The theorem takes no enclosing Target success or intermediate state invariant as an input.
- Root `target-initial-capacity-build-2.log`: canonical PASS, 1345 jobs. Only the historical unused-input dependency warning occurs.

The result discharges the old reached-prefix machine-capacity premise for this Target component. It does not bound equality-cache allocation, native-table allocation, host memory, or elapsed time. It does not derive resource bounds for an arbitrary sequence of class edits or the complete constrained outer caller. General Mu/ref/union behavior, runtime forcing, concurrency, and host machine correspondence remain separate.

No production file, older evidence, or Git state was changed. No canonical build was run by this reviewer. No process remains active.
