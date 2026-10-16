# Recursive prefix state and receipt review

Result: PASS. No material defect was found in the current frozen modules.

- `SourceCurrentAllocatedRecursivePrefixState.lean`: 81 lines, SHA-256 `9dfc1bfc6f81749c5a47ab0d92e0bf7564be36392c62dd8c46240bf1fd0b83c1`.
- `SourceCurrentAllocatedRecursivePrefixReceipt.lean`: 132 lines, SHA-256 `989251341cf535b9272d78ebdc05bd9b6f51d698919343376153f8f94efea8f6`.

`Current` retains the original source heap separately from the current checked state. Its growth and issued-identity fields concern that original heap. Its domain field records actual past `DomainAllocation.Trace` steps from the initial domain cache. It contains no completed future query or desired output law.

`initial` starts this past history with reflexivity at the exact input heap. `yielded` uses the actual checked step and current physical inputs, enter admission, and allocated-field checks. Existing checked-step invariants derive the exact returned `Good`, machine extension, heap retention, operation-table growth, and reached fields. The semantic heap theorem uses the same current physical inputs. The domain theorem records the same literal yielded step. The result composes all three histories at the same returned state.

`Receipt.trace` is the physical trace of the supplied raw prefix. Its `inputs` and `entered` fields concern the exact reached control and state. Its `fields` retains allocated annotations in the continuation. This is stronger than a check of only the current edge annotation. The field premise remains explicit. `result` applies only when the reached control is literally a pure return.

The receipt declarations are induction combinators. `zero` takes the current checks and the local pure-return postcondition. `before_step` takes an already derived suffix receipt and derives the actual preceding step effects. It does not construct that suffix independently. These signatures do not claim initial-only query admission by themselves.

`bind_inside` requires the reached inner control to be nonpure. It appends source code to the same physical trace. It derives the reached physical and domain checks with the new forward bind transports. It transfers allocated continuation fields through actual operation-cache growth. The output postcondition is vacuous because the appended reached control cannot be pure. This cannot certify a false completed result.

`join` requires the actual inner receipt to end at a pure value and the outer receipt to start at that value's code in the exact same full checked state. It composes physical traces and each effect relation. It retains the outer reached checks and postcondition. No heap projection or independently selected middle state replaces that common state.

`Receipt.words` extracts current machine-word checks from the current physical input field. It does not derive an all-prefix `WordRanges` plan from an unproved current check.

Imported validation checks 27 axiom/full-signature pairs. This includes the eleven named public declarations, both constructors, and all fourteen state/receipt projections. The probe enables explicit types, proofs, universes, deep terms, and ten million print steps. `state-receipt-public-1.log` passes without diagnostics or `sorryAx`.

The first integration kernel constructs `Current.initial` from initial `Good` and semantic readiness. It executes the literal enter, read, and pure-work steps. It constructs the terminal receipt and prepends each actual step with `before_step`. The resulting physical receipt derives its own past domain-allocation bound. It retains the exact operation state and both native memo tables. No future receipt, completed query, or output law is supplied to this kernel.

The second kernel constructs an unfinished two-read inner program and its one-step receipt. It applies `bind_inside` to the nonpure reached read. It separately constructs the completed inner and outer read receipts, then applies `join` at their exact common checked state. `state-receipt-kernels-2.log` checks both integration pairs without diagnostics or `sorryAx`. The first failed attempt and its exact source remain unchanged.

The final production direct checks are `prefix-state-direct-2.log` and `prefix-receipt-direct-3.log`. Both are clean. The canonical cleanup build is `receipt-control-request-build.log`, exit 0 with 1131 jobs. It also builds separate root control/request helpers. Its only warning is the historical unused `inputs` warning from `InternedFreshOrdinaryClosedCompletion.lean`. The earlier `receipt-build.log` is not the final cleanup validation record.

This review changes only new evidence files. It does not establish the whole simultaneous prefix invariant, general recursive query capacity, or general constrained outer termination. It does not modify either reviewed source, older evidence, Haskell, Git, or Audit.
