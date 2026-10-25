# Native child safety and retained pending inputs

## Current result

Terminal origin proof: `2c669906bad15602e34f6dd72135e92a7a1c7aa5`.
Child invariant proof: `a323cf8accc68cf55455866bd240dfe4e4ebb693`.
Main remains `9d4e4d584aa7a681f075790e98466afe7531838a`.
The goal stays ACTIVE. This checkpoint changes proofs only.

An actual supported nonterminal child preserves `Safe`. It retains each
old allocated root, the value at that root, and its complete class.
It creates no enumerated value. These results require initial safety,
bounded suspended inputs, the actual prepared action and its successful
execution. They require no native heap, `Graph`, solver, or final safety
assumption. Empty rejection and unsupported actions have no success case.
The ordinary branch allocates and writes only the fresh pending slot.
The Union and Mu branches allocate a pending slot with an empty bucket.

`child_inputs` preserves `InputsPending` for any retained bucket after
that same successful action. It uses the action's actual endpoint.
It does not call the existential completion producer again.

The cached fold completion now exports enumerated-value origin on both
completion and rejection. The terminal completion forwards it through the
prefix. The adapter exports it at the actual after-write result cache.
The incoming write stores a pending value and changes no other value.
All previous premises and conclusions remain. No native query, runtime
branch, completion producer, or proof resource limit was added or changed.
Rejected folds still have no unconditional `Safe` conclusion.

## Meaning of pending inputs

`EnumerationDependencies.InputsPending` means that every suspended input
avoids every enumerated class. It does not require each raw input slot to
contain a pending value. A terminal merge may eliminate a raw losing slot.
`EnumerationCompleteness.inputs_pendingAt` derives pending contents at the
current reached representative from safety, bounds and `InputsPending`.

`retained_inputs` composes enumerated-value origin with root protection.
For each enumerated value after the step, origin finds the same old value.
Initial safety makes its slot an old root. Initial pending inputs avoid
that root. Protection transfers the complete class relation to the result.

`terminal_inputs` applies this rule to the actual terminal partition of
one child descent. It retains the complete parent bucket for later children.
Its origin and protection premises are step receipts. The strengthened
terminal adapter supplies both at its actual result cache. This lemma is
an invariant transport result. It does not construct the child execution
or prove full traversal completion.

## Verification

All strict checks use Lean 4.34.1, `warningAsError=true` and `linter.all=true`.
Heavy checks run serially with 4 GiB memory caps and no swap.
The fold and adapter pass their first strict checks with empty logs.
Terminal attempt 1 fails to reduce the local joined-cache abbreviation.
Attempt 2 makes that reduction explicit and passes with an empty log.
Child effects attempt 1 fails on record-update layout. Attempt 2 identifies
an unqualified theorem name. Attempt 3 passes. The final attempt 4 adds the
terminal partition specialization and passes with an empty log.
All complete inputs and raw logs remain in the retained evidence.

The installed build passes with 1329 jobs. Public readback checks seven
installed declarations. Its complete log has 1174 lines and 132810 bytes.
It has no pretty-printer omission. The four new public child theorems use
only `propext` and `Quot.sound`; the general transport uses only `propext`.
The three strengthened completion theorems also use `Classical.choice`.
No other axiom occurs in these readbacks.

The aggregate Audit passes with 3735 jobs and checks 76560 theorem
axiom dependencies. This count includes generated declarations.
The older unused `inputs` warning is unchanged.
Evidence: `lean/restart-evidence/20261025-child-invariants`.

## Next target and limits

Build ordered native child traversal around `ChildDispatch.run`.
Pass the reached caller and queries, updated root map, actual successful
raw-row core and post-write cache to the next child. Prove that a returned
successful row and its candidate cache have the same core before using it.

Stop explicitly at a missing cache candidate. Preserve the completed prefix
and exact stopping observation. A missing candidate is not rejection.
The terminal outer observation retains a read core and moved waiting table.
The incoming write can add waiting counts. Do not use that intermediate
waiting table to start the next child. Do not frame a stale cache around
the returned core. No uncached continuation is justified yet.

Actual edge buckets combine inherited and fresh-own descents. Use the
combined parent bucket or the general `retained_inputs` rule for that append.
Compose `Post` and its heap-preservation receipts. Transport the remaining
children's availability to the reached heap. Keep each actual caller's
conditional numeric-range admission. A finite list does not by itself
supply those machine-width bounds. Initial-only admission remains open.
Alternatives must start from the same parent state. Record residuals after
all children complete. Then connect the final write to the original
captured raw target, which can differ from a terminal winner.

H6 remains `SourceCurrentColdFiniteWarmCalls.constructed_node_calls`.
Covered closed construction, a valid initial constraint cache and original
allocation history support any prescribed finite number of modeled warm
node calls with the same empty inherited payload, at derived sufficient
finite fuels and one mathematical width. The final available value has
exactly the original finite-tree language under formal formula and
entailment semantics. Full native traversal, whole typing/pruning,
initial-only numeric admission, concrete solvers, extraction, machine
integers and maps, practical resources, convergence and full Haskell
correspondence remain open. H6 itself is unchanged.

No Haskell source changes at this checkpoint. The six merged repair entries
and the parallel-completion follow-ups remain first in root `FINDINGS.md`.
