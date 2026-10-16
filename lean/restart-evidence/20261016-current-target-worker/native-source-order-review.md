# Target and leaf source order

Reviewed the current resident serial worker against source ccebf0f7.
No new Haskell defect was found. No Haskell repair is proposed.

`Equality/Operations.hs:236–242` captures one target per selected path.
Each target uses the ascending class paths other than its own path.
Each operand is `mergeAlternatives (getPath other ns)`. The leaf function
is the partial application `intersect target`. It therefore intersects the
target on the left with the current input on the right. The captured forest
is `ns` at this class invocation. It is not the forest after a leaf edit.
The record-to-ascending-class adapter remains a separate source boundary.

`Equality/Operations.hs:228–230` defines `intersectList [] = EmptyNode` and
`intersectList (n : ns) = foldr intersect n ns`. The first element is the
seed at the base. For ordered operands `[a,b,c]`, the expression is
`intersect b (intersect c a)`. The current target worker retains this
orientation. Its explicit serial order projects and merges `b`, then `c`,
then `a`, then executes the requests `c ∩ a` and `b ∩ (c ∩ a)`.
It does not replace this fold with `foldr1`, a left fold, or an empty seed.

`TargetWorker.operand` executes its actual projection before its actual
allocated merge. It advances the constructor heap at the same operation
state before merging. `TargetWorker.fold` passes each returned native state,
equality-operation state, and completed merge table to the next stage.
The native leaf retains the merge table and calls
`NativeDemand.execute` with an empty domain. `Interned/Operations.hs:406–409`
uses that same domain at the public `intersect` entry. Node memo keying and
placeholder bypass occur at source lines 480–484. The new bridge establishes
the physical graph only on the stated initial Good/idle/closed-resident/
word-range domain. It does not equate arbitrary physical warm hits with
the desired intersection language.

`SharedTargetWorker.force` looks up the class-local path slot first. A hit
returns the same whole state. A miss executes the target at the current
checked state and completed merge memo. It stores only a completed target.
A failed target retains the returned checked state and merge memo without
installing a target. `SharedTargetWorker.leaf` forces this target before
calling its native intersection at the literal returned state. The native
step retains both shared tables. These rules match the completed serial
graph. They do not prove the GHC thunk demand order.

The source has lazy function closures, not explicit target slots or five
execution bounds. `Interned/Memo.hs:93,116–128` and
`Interned/Cache.hs:149–155` publish unforced candidates, keep the first
writer, and reread the winner. A completed target slot models resident
sharing after completion. It is not that publication event. The runtime
connection still needs closure sharing, pending or active producer
observations, candidate winner selection, and host forcing correspondence.
The explicit projection, read, merge, selection, and native limits produce
retained failure observations in the Lean worker. Those observations are
not a proof of corresponding Haskell exceptions or general termination.

`Equality/Operations.hs:313–334` separately compiles edit paths with a right
fold and traverses child maps through `IntMap.foldrWithKey`. A root edit on a
child list is ignored. An unresolved reference branch raises an error.
This target checkpoint does not prove the full edit compiler, native IntMap
iteration, source Set ordering, or the outer reduction worker. The path
domain and available-input premises prevent unsupported projection states
only inside the proved resident component.
