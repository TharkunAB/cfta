# H21 prepend grouping V4 source review
Decision: SOURCE CLEAR for89-line V4 SHA3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba. Elaboration remains the root gate.
Measured review cut: 2026-10-22T23:12:03.758996+02:00. I read every V3 and V4 source line, all17 repair-patch lines and the complete actual strict1/strict2 diagnostics.
I did not author this proof. Arity authored V1–V4. Required’s frozen V1–V3 reviews remain unchanged. I authored signature/tooling reviews and the saved verifier.
The only V3→V4 change replaces reverse_fromRows proof. Context, all9 public headers,3 definitions and all other source bytes are exact.
The repair unfolds both fromRows definitions, rewrites generalized reverse_fold, applies append-fold congruence, and proves reverseTable(empty)=empty pointwise by funext/rfl.
This supplies the exact function-valued initial-table equality reported by strict2. It adds no premise, helper, definition or local lemma.
The singleton insertion proof distinguishes equal and unequal keys. It cases on the rewritten rowKey lookup and retains both none and some [] behavior.
The fold induction generalizes the initial table. It keeps duplicate occurrences and reverses the initial table on the append side.
Iteration transport retains literal keys and emitted positions. Its forward lookup uses original entry membership; its reverse lookup uses the actual Option.map preimage.
Function.comp_def closes both map compositions. The final theorem applies the existing exact iterator permutation contract to reversed buckets.
I read all190 live MergeGrouping lines and the new Core composition cut. Unchanged API cuts reuse my frozen signature review; all9 live identities and20 bounded cuts were rechecked.
All212 owner pins verify. Source contains exactly3 definitions and6 theorems, zero private helpers and no limit override, sorry, admission or new axiom.
The two retained actual strict jobs exited1: strict1 had4 errors/0 warnings; strict2 had1 error/0 warnings. Owned inputs/logs,4G/5m caps and fresh usage are retained. V4 is uncompiled at this cut.
No concrete mathematical or source-elaboration blocker remains. Compilation must still verify the repaired tactic applications.
Scope is a pure prepend/reverse grouping bridge. No HashMap refinement, fixed outer key order, heap identity, stateful group completion, Haskell execution or public pass is claimed.
Two reviewer-only path diagnostics are retained, including one audit-copy stop before freeze. They are not root metadata or proof failures.
No prepared script, Lean/Lake/compiler/runtime/capped/Git/network command ran. I wrote only this new external audit package.
