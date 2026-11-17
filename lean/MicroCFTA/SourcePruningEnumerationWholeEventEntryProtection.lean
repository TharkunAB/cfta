import MicroCFTA.SourcePruningEnumerationJointCausalEventLedger
import MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation

namespace MicroCFTA.SourcePruningEnumerationWholeEventEntryProtection
open SourcePruningEnumerationJointCausalEventLedger
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing : Type} {width : Nat}
set_option autoImplicit false

/- Note [All visible event inputs]
The operation list carries the actual outer and nested input caches.
The predicate checks held history at every one of those visible inputs.
The finalizer input is its before cache. The recordTypes input is its finished cache.
The nested cases use the existing preparation, residual and dispatch event fields.
The predicate adds no event identity, runtime traversal or semantic assignment.
It does not describe primitive states hidden inside one atomic operation.
-/

/-- Protect every visible input cache on one actual outer and nested event list. -/
def EntriesHeld (held heldHandle : Nat) (anchor : Core)
    (events : List (Operation Typing width)) : Prop :=
  ∀ event ∈ events,
    match event with
    | .parked _ _ _ entry _ _ _ _ _ _ =>
        EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core
    | .selected _ _ _ entry _ _ _ _ _ _ _ _ _ =>
        EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core
    | .prepare _ _ entry _ _ _ _ _ _ _ =>
        EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core
    | .opaque _ _ _ _ entry _ _ _ _ _ =>
        EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core
    | .finalize _ _ _ entry _ =>
        EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core
    | .recordTypes _ _ _ entry _ _ =>
        EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core
    | .nested nested =>
        match nested with
        | .prepare _ _ _ _ entry _ _ =>
            EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core
        | .residual _ _ _ _ _ entry _ =>
            EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core
        | .dispatch _ _ _ _ _ _ _ _ _ _ entry _ _ _ =>
            EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core

/-- Concatenate protection proofs for the same anchor and actual event lists. -/
theorem entries_held_append (held heldHandle : Nat) (anchor : Core)
    (front back : List (Operation Typing width))
    (left : EntriesHeld held heldHandle anchor front)
    (right : EntriesHeld held heldHandle anchor back) :
    EntriesHeld held heldHandle anchor (front ++ back)
 := by
  intro event member
  rcases List.mem_append.mp member with member | member
  · exact left event member
  · exact right event member

end MicroCFTA.SourcePruningEnumerationWholeEventEntryProtection
