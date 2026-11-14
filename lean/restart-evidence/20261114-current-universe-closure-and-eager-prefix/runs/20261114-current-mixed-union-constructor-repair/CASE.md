# Expose the union constructor before disequality elimination

Timestamp: 2026-11-14T19:26:38.771664+01:00
Status: UNCOMPILED. Root owns strict validation and publication.
The clear-writing skill was applied to this note.

This revision changes only the unionApart disequality proof. It exposes the
union constructor with an explicit change statement before cases. The previous
proof left operand as a local let alias. Dependent elimination did not expose
the union constructor. No declaration header, hypothesis, native branch,
original domain, machine endpoint or induction bound changes. All remaining
proof bytes are unchanged. The previous frozen packet remains unchanged.

Root reported standard axioms for all three private helpers. The previous
whole-module check failed at this one constructor proof. This revision still
needs strict validation. The full simultaneous generated-Type closure remains
OPEN. No compiler, live edit, Git write, board action, child agent or Haskell
change was made. Original full and coupled target files were not edited.

Source SHA256: be495770238859e66e6e027519b01afb55f74c9d8ac71d709e5b36d34c4b2945
Previous source SHA256: 5f9cd53f5c55e844f6763b8bfc8b2785a5afa9ded6e1f2991c24f5deb8bc33bd

Public probe: current_stored_universe_body_union_of_coupled_fuel_induction
Private probes: physical_identity_apart_owner, pair_apart_owner, body_union_branches.
Namespace: MicroCFTA.SourceSynthesisCurrentUniverseMixedBodyUnionInductionStep.

Exact proof diff:

```diff
--- previous/SourceSynthesisCurrentUniverseMixedBodyUnionInductionStep.lean
+++ repaired/SourceSynthesisCurrentUniverseMixedBodyUnionInductionStep.lean
@@ -146,7 +146,12 @@
           (by intro impossible; cases impossible)
       have unionApart : unionEntry.identity ≠ entry.identity :=
         physical_identity_apart_owner later.heap laterValid.1 entry body depth ordinary ownerAvailable
-          operand operandAvailable unionEntry.identity rfl (by intro impossible; cases impossible)
+          operand operandAvailable unionEntry.identity rfl
+          (by
+            intro impossible
+            change (Value.union unionEntry members unionDepth unionFree : Value Symbol Guard) =
+              Value.mu entry body depth ordinary at impossible
+            cases impossible)
       have originalKey := SourceRecursiveIntersectionSchedule.entered_key domains cacheValid
         IntersectionEmptyDomain.emptyKey universeValue pattern entry.identity patternId
       have apart := pair_apart_owner bodyEntry.identity unionEntry.identity entry.identity patternId bodyApart unionApart
```
