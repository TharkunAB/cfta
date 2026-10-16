# Mutual outer worker success stability validation

Timestamp: 2026-10-16T14:26:13+02:00.

## Established endpoint

`SourceCurrentAllocatedPartialWorkerStability` proves successful execution monotonicity and complete returned-state uniqueness for all eight literal current outer families: `nodeCall`, `nodeBody`, `edgeCall`, `edgeBody`, `rows`, `descendants`, `children`, and `walk`.

Each public `family_done_stable actual enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN` permits independent increases in all ten bounds: outer fuel followed by `g s r e p h m c n`. The conjunction budget remains fixed. It retains the exact successful output and entire `PartialState.State`. Each `family_done_unique one two` compares successes at arbitrary, possibly incomparable, ten-bound tuples and proves output equality and complete caller equality. This includes equality of checked heap, equality operations, native tables/domains, both outer result tables, fourth memo, and merge memo.

The public endpoints have no physical, closedness, semantic, range, completion, body-law, or callback premise. Their execution premise is the supplied literal successful equation. The additional public `bind_done_iff` exposes exact successful intermediate states.

## Constructive induction and source order

The private strong induction on outer fuel quantifies over all requests, lists, indices, and complete initial caller states. It discharges all smaller-request transports internally.

1. `edgeBody` uses the actual parent worker's nine-bound successful stability. It advances the same returned checked state and warm memos while retaining both outer result tables.
2. `edgeCall` reads the same literal begin observation. A ready hit skips the body. Evaluation uses the same stored owner, body return, and exact finish handle.
3. A nonempty `walk` uses smaller outer fuel for the node call and suffix. The head request uses the actual indexed descent at the current operation state. The suffix starts at the exact returned caller.
4. `children` erases contradictory slots without a child request. A live payload delegates to the same-fuel indexed walk.
5. `descendants` retains the actual inherited-prefix operation state, invokes same-fuel children, and executes the same raw edge rebuild.
6. A nonempty `rows` uses smaller outer fuel for its edge call, descendants of the returned narrowed edge, and suffix. It does not apply descendants to the original edge.
7. Ordinary `nodeBody` rows use smaller outer fuel. Terminal, reference, and cached Mu observations are independent of all stage bounds. The actual ordinary rebuild retains the same exact row return.
8. `nodeCall` uses the same literal begin observation and same-fuel body before finishing the selected owner.

Uniqueness raises both successful bound tuples to their componentwise maxima. Successful equations then identify both output and complete caller state. No historical worker or execution equivalence is used.

## Validation

Pinned Lean 4.34.1 direct source check `partial-stability-direct-5.log` returned exit 0 with no warnings. Root's final combined canonical build returned exit 0, 1461 jobs, session 9266, `partial-completion-stability-build-1.log`. The only warning is the pre-existing unused `inputs` dependency warning. There is no new stability warning. Final source SHA-256 is `844d81f8b118dd8e64737e2d07b81b5f5814dabd829ec4ea7159a46ef691d936`. The frozen copy is `partial-stability-frozen.lean`.

`partial-stability-checks.lean` checks all seventeen public theorem signatures and axiom reports. Nine external integration kernels each also have a signature check and axiom report. The final run `partial-stability-probes-3.log` imports the final canonical olean and returned exit 0. It contains twenty-six reports and twenty-six full signature checks, with no errors, warnings, or `sorryAx`. `bind_done_iff` has no axioms. All remaining reports list only `propext`, `Classical.choice`, and `Quot.sound`.

The nine kernels check zero-bound ready node hits, zero-bound ready edge hits, bound-independent cached Mu reconstruction, rejected parent bodies without child work, contradictory inherited children, actual indexed head/tail walking, parent-returned descendants before the ordered row suffix, actual inherited-prefix allocation before children, and incomparable successful bounds retaining every caller state field.

Earlier direct logs preserve elaboration failures from explicit larger-fuel inference and the strong-recursion constructor name. The initial canonical log preserves the private generic helper's unused section-variable warning. The final source removes those unnecessary section variables. Earlier probe logs preserve corrections to the Mu record's actual node-shaped fields, the required Cache namespace, a reserved identifier, and the checked unfolding equation for children. None of those failed probe logs is validation evidence. The final imported probe log is clean.

## Scope

This theorem concerns successful execution. It does not turn busy, absent, field errors, binder pending observations, or exhausted work into successful results. It does not prove that arbitrary outer calls terminate or construct a successful run without an actual finite graph or another progress proof. It does not establish host lazy forcing, concrete global memo event replay, pending publication, solver runtime correctness, physical machine range validity, or Sized contracts. It adds no whole-forest closedness restriction. This task changed only the new stability module and its new evidence. Older proofs, Haskell, Audit, root documents, Git, and earlier evidence remain unchanged.
