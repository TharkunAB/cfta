# Current conjunction worker scope

Source checked: `cfta/src/Data/CFTA/Enumeration.hs`, lines 589–644. No Haskell defect or repair was found in this task.

The source memo wrapper occurs at line 589. The source open-input guard at line 592 short-circuits the body before exploration. The worker therefore checks the fourth memo first and checks closedness only on a miss. A hit returns the cached answer and preserves the entire physical state. A failed miss inserts no completed entry.

Lines 595–599 check the pending queue in this order: empty queue, Empty member, then budget/closedness/key membership. Admission alone decrements the budget. The literal completed row result supplies both the new table entry and `requirements.flatten ++ rest`. The worker uses well-founded recursion on `(budget, pending.length)`. It has no additional exploration fuel. Budget zero still drains queued items. The Nat parameter covers the nonnegative source budget, including its literal value 1000 at lines 642–644.

The row implementation is `SourceCurrentConjunctionRowsWorker.rows`. The worker calls it with the actual returned constructor heap and equality operation state. No supplied row-result function implements the body. `explore_sound` uses `RowsWorkerActual.rows_graph`, which derives the same-arity condition from actual tuple matching. Row failures preserve their returned physical state and the exact local table and pending queue. Their diagnostic is an observation interface; it is not a new Haskell exception.

Lines 631–633 use an unbounded equality-stop fixed point. The model observes that fixed point with `table.grow (budget + 1)`. Existing finite-table results derive a successful grow from a completed valid exploration. The explicit `.grow` fault records exhaustion of this observation bound. It is not a new source runtime budget. The source answer and canAccept order are retained at lines 635–637.

`Completion.explore_sound`, `decision_sound`, and `call_sound` reconstruct the current graph from any literal successful worker execution. They require no physical validity, semantic result, or callback-completion premise. `explore_complete`, `decision_complete`, and `call_complete` construct stable projection/read bounds from finite actual graphs. Initial readiness and residency construct those graphs in `explore_finite` and `call_finite`. This finite existence result uses proved finite row completion; it does not assume the completed body.

The stability module proves unconditional successful execution monotonicity in projection/read bounds. The admission budget stays fixed. It also proves exact output and entire physical-state uniqueness, including the saved fourth memo for calls. Failure monotonicity is not claimed.

The model is a completed resident serial projection. Its table is the existing logical key table. Native Map/IntMap representation, machine Int/no-reuse correspondence, and the host key-demand behavior are separate adapters. The source row list is lazy. The chosen sequential row, equality, and projection schedule does not prove GHC forcing equivalence. Completed insertion is not the source lazy publication point. Publication-before-body, winner reread, pending ancestors, and concurrent execution remain outside this component. Three-family global memo Reads are logical receipts constructed separately at the same returned endpoints. This worker does not claim to execute the host global memo tables.

Source tuple order, equality combination, canonical conjunction values, and path requirements remain the current row-worker components. No historical native-intersection Decision is used as current execution. No whole class caller, whole enumerator, or whole-library correctness theorem follows from these component endpoints alone.
