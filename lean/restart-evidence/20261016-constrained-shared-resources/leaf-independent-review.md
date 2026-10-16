# Independent Shared Leaf resource review

Reviewed 2026-10-16 21:08 CEST. Verdict: no material defect found.

Source: `SourceCurrentAllocatedFiniteOrdinarySharedLeafResources.lean`, 185 lines, SHA `f6c0732d5df2f98a7a5f83b065b6fea632d5e73b9116f9882a899eb8ead2e053`.

`queryBudget` at line 42 uses the maximum of the derived target row limit and the independently supplied current-input row limit. It uses separate captured/input arity and height maxima. These are initial data and profile bounds. It does not identify the current edited input with a captured original or require the input to fit the original forest profile.

`complete` at line 83 derives Force headroom from the initial Force-plus-query sum. It constructs one full Force receipt at its exact shared return `middle`. The actual Force supply bounds derive the query headroom there. It transports current input availability through that exact prefix and derives its closedness from the initial coherent available finite-ordinary input. It takes target availability, closedness, profile, native certificates, and the computed current inventory from the same Force receipt and returned profile store. No ForceRanges, LeafRanges, future capacity, supplied after-state, completion callback, or result-law premise occurs.

The query runs on `(target, input)` in that order at `middle.checked`. `TargetQueryResources.finite` constructs one full query receipt, its output profile, both causal native certificate families, an actual constructor Work trace, and supply bounds. The returned `NodeNarrow input result` uses the query's right-operand height bound. The final explicit height is bounded by the independent inputBound. The result profile allows squared common row counts and the rejection-sentinel arity.

Private `of_parts` at line 58 assembles the actual Leaf and its Reads from those exact Force and query receipts. Ready and admission advance at the query's computed inventory. Effects and machine extensions compose at the exact checked-state join. Shared advance retains the forced target slots and Merge table. The new result is a native query result; it is not installed as a target slot. `SharedProfiles.advance_stored` therefore retains the target slot bounds while accepting the new native and output certificates.

Global continuity is correct. Force can extend the unfolding memo and changes the incoming ghost bundle to `current`. The query uses and returns that same current bundle. The final effect composes these two facts; it does not equate the initial and final full bundles. Leaf narrowing takes the input conjunct of the actual query iff. Conditional preservation combines the actual Force SelectedIncludes law with the accepted input part. Neither is a desired parent result law supplied as an oracle.

The Work trace concatenates the actual Force and query traces at `middle.checked.heap`. Separate node and edge request counts use their own Force bound plus a conservative native total Work bound. Final supplies follow from the same actual prefix supply inequalities. The proof counts requests rather than defining a resource by final counter subtraction. Cache hits and losing candidates retain the behavior of the underlying proved producers.

Initial warm semantic slot receipts and profile certificates remain explicit causal invariants. Fresh class initialization derives them for empty slots. The finite-ordinary profile excludes Mu, references, and explicit union, while allowing full guards and nonempty equality classes. The result counts constructor Work and the two constructor supplies. Equality-operation, native-table, host-memory, timing, concurrency, full outer-caller resource, and runtime-demand claims remain separate.

Validation: root canonical `shared-leaf-capacity-build-2.log` passed 1360 jobs. It includes the final Leaf source and reports only the historical dependency warning. Independent direct imported `leaf-independent-all-public-1.log` passed all 43 public signature/axiom pairs from the root's current six-module probe, including all four Leaf declarations. It reports no warnings, errors, or `sorryAx`. Exact probe bytes are retained as `leaf-independent-all-public.lean`. This is public signature validation, not a claim that every other module in that probe received a new source review here.

Only new review/probe evidence was written. No production source, older evidence, Git state, or canonical build was changed. No process remains active.
