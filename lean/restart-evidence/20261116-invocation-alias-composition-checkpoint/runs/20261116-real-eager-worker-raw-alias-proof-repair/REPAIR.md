# Whole-worker alias proof repair

Status: UNCOMPILED. The original failed candidate and full log remain unchanged.
The first check failed at 15 local elaboration and linter sites. It gives no
proof credit to the whole theorem. The Nat induction must pass a new check.

This packet changes only the following proof details.

- The opaque receipt proof cases the two actual Boolean guards explicitly.
  It does not split the operand constructor match inside the second guard.
  This exposes the literal child-dispatch branch and removes the stuck
  `Decidable.rec` expression. The redundant `dsimp` is removed.
- The finalizer case split uses valid tactic syntax. Each branch rewrites the
  actual finalizer equation before it eliminates the completed receipt.
- A callback with multiple raw rows cases its Boolean result before it
  eliminates impossible empty-output membership.
- The stopped receipt proof reduces the outer receipt match before it cases
  the actual `advance` result. It then reduces the actual endpoint pair.
- The pure parked restart equality has an explicit `Except Error` list type.
  Both successful constructors use `Except.ok`.
- The seven original resource hypotheses have explicit proof references before
  they are cleared. Their names and complete public binders remain unchanged.

Every declaration header remains byte-exact. The public header remains the
ORIGINAL `c4cb44f2` statement. The probes are byte-exact. The proof adds no
premise, runtime operation, work-fuel increase, proof-limit change, or linter
suppression. `PROOF-ONLY.diff` records the complete raw-source difference.
No compiler, Source edit, Git command, board action, or temporary file was used.
