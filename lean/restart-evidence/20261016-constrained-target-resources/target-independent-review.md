# Independent review of cumulative Target resources

Reviewed 2026-10-16 20:45 CEST.

Verdict: no material defect found in the final `TargetResources` source `c7b7dcbbe53e45fb0b252ea5fb36552199a06d058b2375f2c6744b7d1d2f9ca8`.

## Actual order and state joins

`SourceCurrentAllocatedFiniteOrdinaryTargetResources.fold_complete` at line 97 constructs the current path operand at `before` and obtains `middle`. It constructs the shorter tail with the same seed at that exact `middle`. It then constructs the native request on the head and tail at the exact tail return `later`. The graph constructors and `FoldReads` use these same complete checked states and Merge memos. This matches `SourceCurrentAllocatedTargetGraph.Fold.cons` and preserves the source rotation: for `[seed, first, second]`, the serial graph visits the first operand, the second operand, the seed, and then the two intersections.

The global bundle passes from the current operand to the tail. The final native request retains the tail bundle. The combined receipt uses effects at those exact heap joins. The Merge memo is the tail's actual saved memo; a native query does not change it. The initial inventory passes through constructor-only operands. Each native receipt supplies the computed inventory for the next native request. No final model or successful intermediate call is a public premise.

`OperandNativeStores.native` derives retention of both native certificate families from exact equalities of the complete node and edge tables. It does not derive a new result certificate from an arbitrary unchanged heap. `OperandResources.complete` derives the actual candidate and keep-first winner profile through the proved Merge producer. The native query then derives its structural and output certificates from the same physical trace. These steps retain the separate causal invariants for physical Merge entries, Merge profiles, native structure, native profiles, semantic admission, scoped cells, and Idle.

## Profiles and constructor budgets

`TargetBudgetNumbers` charges an operand, the shorter tail, and the native query. The native row bound is the square of the maximum head and tail row bounds. The arity bound is `max arity 1`, which includes rejection sentinels. Height stays at the original forest bound. The proof retains the captured original forest and its unchanged syntactic profile for every operand. It does not reuse a generated result as an original operand profile.

The head's actual supply bounds derive the tail headroom. The tail's actual supply bounds derive the query headroom. `TargetQueryResources.finite` derives initial capacity from those numeric inequalities and uses `Words.node_of_domain` for raw yielded-prefix word safety. It constructs one full TargetQuery receipt. `counted` applies structural, output-profile, Work-trace, and request-budget proofs to that receipt's exact trace. No future capacity, WordRanges plan, completed Target, supplied output profile, or supplied result law occurs in the public finite premise.

The final Work trace concatenates the exact actual constructor heaps and ordered request lists. Request counts bound both supplies. These bounds are not counter-difference definitions. They count constructor Work requests, including repeated occurrences and losing Merge candidates. Native requests use one conservative total Work budget for either supply.

## Whole Target and semantic scope

`target_complete` at line 196 lifts the constructed nonempty fold to the literal worker's `StableRun` at the same output, full checked state, and saved Merge table. It supplies its own graph and reads. For an empty path list it returns Empty and the identical checked state, inventory, Merge memo, and global bundle. Its request trace is empty, its node and edge budgets are zero, and its output row bound is zero.

The semantic receipt proves inclusion of a common selected subtree for nonempty proper paths. It does not claim unconditional exact equality with the original language. Merge can enlarge a language. The full checked native intersection has its separate exact language receipt.

The result is an initial-only finite-ordinary constructor resource theorem. Guards and equality classes remain unrestricted. The finite-ordinary shape excludes Mu, references, and explicit union constructors. The constructor trace does not bound equality-operation cache allocations, native table or domain allocations, global memo storage, host memory, concurrent losing evaluations, or elapsed time. Stable worker bounds are constructed; these are not a quantitative bound on every instruction or a proof of GHC demand order. Haskell `intersectList` and class target expressions at `cfta/src/Data/CFTA/Equality/Operations.hs:228-243` support the rotation and operands. Literal host forcing and runtime correspondence remain separate.

## Independent imported integration

`target-integration-kernel.lean` constructs two three-path targets on the same original forest. Initial headroom is twice each complete Target node and edge budget. The first constructed receipt supplies the original-forest availability, current physical Merge store, Merge profile store, native stores, computed inventory, semantic cache coverage, and global validity for the second construction. The second headroom follows from the first actual supply bounds and the original doubled headroom.

The kernel returns both exact `StableRun` witnesses, both actual graphs, both read receipts, both full semantic receipts, final causal stores, a concatenated Work trace, doubled request bounds, and final capacity and supply bounds. It receives no intermediate completion, capacity, profile, range plan, or result-law premise. Direct imported check 3 passed with exit 0, no warnings, and only `propext`, `Classical.choice`, and `Quot.sound`. Checks 1 and 2 are retained as failed proof diagnostics. Root canonical `target-resources-build-4.log` passed 1343 jobs and reports only the historical dependency warning.

No production file was changed by this review. No canonical build or Git operation was run by the reviewer.
