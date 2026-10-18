# Literal stored-node rows after recursive Head

Completed on 2026-10-18 at 02:29 CEST.

## Result

`SourceCurrentRecursiveHeadNodeRows` extracts literal stored-body row occurrences from an actual recursive Head. Its initial producer takes Ready, an available Mu whose body is a node, and closedness of that Mu. It constructs the Head itself. It does not take BodyRows, HeadRows, a future child completion, or a desired source-row law.

The result retains the first actual stored-body execution, its growth into the final Head heap, and the exact warm body replay at that heap. It supplies an ordered RowCalls pair for every original body row. Every selected Head row has an original source-row index and a surviving output occurrence at the same index in that pair list. RowCalls retains the original symbol, the complete guard, the ordered actual child substitutions, the exact warm edge constructor, and arity equality.

The public `actual` verifier aligns the initial producer with an observed Head by uniqueness. The actual Head is an input to that verifier. It is not an input to `complete`.

## Proof boundary

The proof uses the earlier initial Head producer to recover the first actual body call and each selected row's final-reader epsilon origin. It replays that exact body execution at the final Ready heap. It then uses StoredNodeExpansion.node_warm to turn the origin into an indexed original-row pair.

The warm expansion covers both open and closed stored node bodies. Closed bodies retain literal source rows without a canonical-row premise. Arbitrary nested Mu records are allowed in children. The child calls execute the original environment and own captured leaves. This theorem does not identify reconstructed child records with their original values.

This closes the literal-node body row-flattening gap recorded in the prior recursive-head component. It does not extract rows from a stored body whose root is a union or Mu. It does not align retained-used body and ordinary-probe callbacks. It does not connect native compileMu child calls to both original input operands. It adds no owner exclusion, initial fresh-call bound, or full outer completion theorem. Only the requested Mu must be closed; unrelated heap records need not be closed. No finite Cap or whole-heap plainness is an input.

## Constructed checks

The fixture builds its own initial source and Ready heap. Its raw productive outer Mu has one open ordinary body row. That row has a nontrivial equality payload and full formula guard. Its ordered children include the outer self reference and a separate productive nested Mu. The first check constructs the Head, selects a positive row, and derives its original index and actual ordered warm child calls.

The second raw Mu has a closed ordinary body containing a nested Mu and a leaf. Its check starts at the exact heap returned by the first Head. It derives the second actual Head, the closed-body identity path, a positive selected row, the full guard, and the original row's warm calls. Neither check accepts a future heap, graph, row law, or completion premise. The public witnesses are exact explicit aliases to private checked proofs.

## Validation

- Production SHA256: `42173b654b0a5154b08d4e0b928423a67f461ddab77aae7ecfbe165cacba0f7e`.
- Final production check: `recursive-head-node-direct-3`, exit zero and zero-byte log.
- Canonical target: `recursive-head-node-canonical-1`, exit zero, 1427 jobs. Its sole warning is a replayed unchanged warning in InternedFreshOrdinaryClosedCompletion at line 24. The owned source has no warning.
- Full public probe: `recursive-head-node-public-1`, three declarations.
- Final constructed check: `recursive-head-node-kernels-4`, exit zero and zero-byte log.
- Constructed full probe: `recursive-head-node-kernels-public-1`, two explicit witnesses.

Both full probe sources explicitly enable linter.all and all seven required printer options. They use `#check @`, full `#print`, and `#print axioms`. Their selected logs contain no printer failure, omitted expression, truncation, error, warning, or sorryAx. Axiom dependencies are restricted to propext, Classical.choice, and Quot.sound.

The inner capped worker reads its effective cgroup limits. Every selected run records memory.max and memory.high equal to 4294967296 bytes and memory.swap.max equal to zero. The largest recorded owned peak is 435 MiB. The time cap is five minutes. Every direct run executes its own immutable numbered snapshot with pinned Lean 4.34.1 and `-Dlinter.all=true`.

All attempts remain retained. Direct attempt 1 stopped before Lean because the sandbox could not connect to the user bus. Direct attempt 2 contains elaboration diagnostics. Kernel attempts 1 and 2 contain syntax and type-inference diagnostics. Kernel attempt 3 was clean before the final public aliases were added. No failed attempt is selected as proof evidence. No old source, old evidence, Audit, authority note, Git state, or Haskell source was edited by this component.
