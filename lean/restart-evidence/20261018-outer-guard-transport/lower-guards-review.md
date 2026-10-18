# Lower-worker causal guard heaps

Final production: `lean/MicroCFTA/SourceCurrentLowerGuardHeapReturns.lean`.
SHA-256: `92c6ae319e1c8ee96c2fa9828e1164ac7d19afd68d484449ae9f0ac2c4a5b6b7`.
The source has 358 lines and nine public theorem heads.

## Contract

`operand`, `target`, `run_class`, `class_fold`, and `class_pass` take the actual successful worker equation, initial `NativeOperationHeap.Good`, initial physical `MergeEffects.Stored`, initial available inputs, and initial `GuardHeap annotation`.
`force`, `leaf`, `edit`, and `edit_list` use the corresponding `LowerOperationInvariants.SharedGood` and initial shared input availability.
Each theorem concludes `GuardHeap annotation` at the exact returned heap.
The annotation argument is first. The initial guard heap argument is last.

`GuardHeap` equates the guard-depth observations of each installed Mu body and its actual ordinary probe. It does not require every raw guard to satisfy the annotation predicate. Thus the theorems work for an arbitrary predicate. They require no closure under conjunction and no finite input cap.

## Actual composition

Projection uses its actual graph, derived from the successful literal projection equation. It applies the existing open projection guard theorem.
Merge uses its actual graph and the existing causal Merge guard theorem.
Each native query calls the new range-free `NativeGuardHeapReturns.node` with its actual request and actual equation.
The public physical lower-worker theorems derive intermediate Good, availability, memo storage, and operation growth from the same earlier returns. These are proof consequences, not future preservation premises.

Edit recursion follows the actual fuel, selected child, row, and Head branches. Edge and ordinary-node construction add no Mu record. Recursive exposure uses the actual successful Required Head graph, without a closed-input premise.
Each class initializes its actual shared state. The class fold executes the tail before the head. Final empty propagation changes no constructor heap.

## Constructed integration

`lower-guards-kernels-3` builds its own source heap. The source contains two distinct productive retained Mu values. One has an extra alternative. Its equality operations contain an actual descended equality record and a stored top field.
The actual nonempty class record has paths `[[0],[1]]`. Its full class pass starts from an empty Merge memo, returns two Mu values, and has a positive native-node allocation counter. The source constructor derives the initial causal heap for every annotation predicate. The new `class_pass` theorem derives the final heap.
The fixture assumes no future worker return, output heap, range, resource bound, or preservation theorem. Its bounded worker success and output positivity are checked by literal evaluation.
The public witness aliases a checked private proof with the same explicit statement. This keeps the full printer output bounded.

## Validation and preserved attempts

The selected strict source check is `lower-guards-direct-3`; its log is exactly zero bytes. The selected canonical check is `lower-guards-canonical-1`, successful with 1786 jobs. It replays one unchanged warning from `InternedFreshOrdinaryClosedCompletion.lean:24:5`. The owned module has no warning.
`lower-guards-public-1` prints all nine exported signatures, proofs, and axiom reports. `lower-guards-kernels-public-1` prints the one constructed witness. Both use all eight required options, explicit `#check @`, and only the three standard axioms.
The selected fixture strict check is `lower-guards-kernels-3`; its log is exactly zero bytes.
Every check runs the immutable numbered source snapshot. The inner worker reads back effective memory.max and memory.high of 4294967296 bytes and memory.swap.max of zero.

Failed direct attempts 1 and 2 remain unchanged. They contain elaboration errors at request/path/width binders. Failed fixture attempt 1 remains unchanged. It contains a wrong fallback trie constructor and a list-membership elaboration error. Fixture attempt 2 is a successful earlier witness; attempt 3 additionally proves both results are Mu values. No failed or warning-bearing owned check is selected.

## Remaining boundary

These are successful-return preservation laws. They prove no worker completion or fresh-call bound. They do not establish output annotations, exact row provenance, retained-used-Mu value congruence, or preservation for every failed stopping outcome. They do not replace the physical initial Good and stored-memo premises. Whole outer progress remains separate.
