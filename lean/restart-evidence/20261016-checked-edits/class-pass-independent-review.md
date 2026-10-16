# Independent checked class-pass review

Reviewed frozen `SourceCurrentAllocatedClassPass.lean`, SHA256
`2a0b66d819f2f559f452d7206e6cbdeeb2dfe3e4494d26fd9286f6c1a84299cc`.
Also inspected current ClassEdits and SharedEditComplete source. No material defect found. No proof source was edited and no Lake build was run for this review.

## Source order and exact returned states

`cfta/src/Data/CFTA/Equality/Operations.hs:211` runs `propagateEmptyNodes $ foldr reduceEClass withNeededChildren eclasses`. Lines 236–244 build all callbacks for one class from the SAME captured `ns`, with ascending original class paths and ascending other paths. ClassPass.Fold.cons follows this order: first the actual tail Fold, then Class on the tail's literal returned forest, checked state, and completed merge table. Class.edit initializes only its class-local slots. It preserves the native node/edge/domain tables, equality-operation state and merge table from entry. It does not reset them to obtain a cold completion.

The next class receives the actual generated current Inventory. Fold.verified and fold_complete transport the next head's path domains from the original domain through the actual tail receipt. They also pass tail readiness, admitted cache, resident forest, stored merge entries, uniform warm CacheCovers, and final global validity to the head. The head does not reuse the old capture or inventory. Duplicate class records are not erased; the graph follows the input record list with its multiplicity.

The final Pass.done uses literal propagate and the SAME returned checked state and merge table. Its read graph makes no additional global call. propagate_receipt reuses physical effects, Extension, admitted inventory, stored merge table, coverage and global effect. It derives output availability/domain transport and exact language using existing pure empty-propagation laws. An empty class list still performs final propagation; it need not leave the output forest unchanged if a literal empty root occurs.

## Completion and language premises

Ranges.cons requires only the class range plan at each ACTUAL completed tail return. The plan does not assume a later result language, final Ready/At, or completed future query. SharedEditComplete constructs actual checked leaf queries and recursive Heads. The finite trie induction constructs later calls from earlier actual returns and derives their invariants via the new Effects module. Selected path domains permit unrelated open ordinary siblings. A selected recursive head's needed closedness is derived locally, not assumed for the whole forest.

The public pass law is narrowing plus an iff CONDITIONAL ON every original class being satisfied by the original term. It does not claim that all output terms satisfy the equality classes or that the pass is unconditionally language-equal to the input. No desired parent result law or old scoped-native execution transfer appears in the completion endpoint.

Initial physical Ready/At, current resident forest and selected path domains, coherent active records, uniform legitimate warm merge CacheCovers, initial global Valid, and reached machine ranges remain explicit inputs. This is the class-edit pass after selection/required preparation. It is not yet a complete original source go/precheck/Scan/Required caller theorem. Host container ordering, GHC delayed forcing, publication/concurrency and machine-identity capacity remain separate source transfer boundaries.

Receipt.fourth_correct transports correctness of the SAME supplied immutable fourth table through actual Keeps. It does not claim runtime fourth-cache publication or a call to its body during this pass.

## Validation

Root focused build inspected: `class-pass-build-3.log`, terminal 0, 1,295 jobs. Only the existing ClosedCompletion unused-input warning remains. The frozen source has no new warnings.

Independent direct command:

```
LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-checked-edits/class-pass-independent-public.lean
```

Terminal 0. Final raw log: `class-pass-independent-public-2.log`. Five public axiom checks and five full signature checks passed for Fold.verified, fold_complete, Pass.verified, pass_complete, and Receipt.fourth_correct. Three named probe theorem axiom checks also passed. The structural two-class inversion uses no axioms. All other checks use only propext, Classical.choice and Quot.sound.

Ten kernel compositions passed:

1. Invert an actual two-class fold to the exact tail and head captures.
2. Empty Fold retains the whole checked state and completed merge table.
3. Empty Pass retains both states and returns literal propagation.
4. Empty PassReads retains the identical global bundle.
5. A literal empty root erases an unrelated open sibling.
6. Finite two-class execution derives successive inventories at the actual middle/final checked states and retains both warm table prefixes.
7. Finite pass execution derives narrowing and the all-class conditional iff.
8. Any actual annotated Pass derives its receipt at the literal endpoint.
9. A pass receipt retains the same fourth-table correctness.
10. Finite pass construction derives fourth correctness from initial facts, without a final receipt premise.

No evidence .olean, .ilean or .o files were generated. No build process is owned by this review.
