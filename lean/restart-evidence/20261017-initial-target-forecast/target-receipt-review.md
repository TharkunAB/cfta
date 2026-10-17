# Target receipt composition review

The frozen production module is `SourceCurrentConstrainedCapTargetReceiptComposition.lean`.
Its SHA-256 is `4316f575137915ff2ce6bd7db44d744dd7823b8614fdea351cef49e07387ee0e`.

The five public helpers expose additive receipt composition. They do not construct an initial full Target forecast. They consume actual component receipts or actual retained read graphs. No helper requires FoldRanges, TargetRanges, a future callback law, or a new profile or closure restriction.

`of_operand` turns one actual MergeOperand receipt into the complete singleton Target receipt. It retains the exact checked states, physical extension, concrete inventory, Merge memo, global memos, original values, and semantic inclusion law.

`cons` follows the source execution order. The head path Operand runs first. The recursive receipt runs next for seed :: paths. The checked intersection runs at their exact returned state. Its result uses the actual final query inventory. Global memos compose through the head and recursive receipts; the checked query retains the last globals. The resulting path order is seed :: path :: paths. The included law combines the head and recursive language facts through the actual query's intersection meaning. It retains the nonempty and proper-path conditions of the older receipt.

`empty` uses only the same initial Ready, inventory admission, available forest, stored Merge laws, coverage, and valid globals. It returns Empty at the identical checked state and tables. `of_fold_reads` derives the final concrete inventory and full receipt by induction on the exact retained FoldReads. `of_target_reads` handles an actual empty Target with the initial facts, and a nonempty Target with its actual fold reads. Neither endpoint adds range assumptions.

Strict source attempt 1 passed with an empty log. Canonical build 1 passed with 1279 jobs. Its warning comes from the earlier ClosedCompletion dependency. The five imported public axiom/signature pairs and three integration pairs passed on attempt 1 with no diagnostics. Only propext, Classical.choice, and Quot.sound occur. Every probe uses full explicit signatures, proofs, universes, deep terms, and pp.maxSteps 10000000.

The constructed singleton kernel derives the real checked constructor heap, loaded field, valid equality descent record, pair inventory, and initial Frame. It constructs its own complete numeric Operand beside an unrelated open depth reference, then builds the singleton actual Target and TargetReads and composes the full receipt. The constructed empty kernel retains that initial state exactly. Neither kernel accepts a future execution, heap, or completed Target.

The ordered-two kernel is a proof-composition check. It consumes actual head Operand, seed Operand, and checked query receipts at their literal shared states. It builds the source Fold and TargetReads and checks both direct cons composition and of_fold_reads. Its component receipts are explicit premises. It is not an initial-only construction of the two-path Target.

Full initial resource reservation for the nonempty recursive Target fold remains separate. These helpers do not prove that reservation, a cumulative arbitrary Target schedule, whole selected reduction termination, or whole-library convergence. No earlier production, Haskell, Audit, or root documentation bytes were changed.
