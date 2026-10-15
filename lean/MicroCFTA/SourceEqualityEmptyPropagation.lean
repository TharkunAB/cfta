import MicroCFTA.EqualityLeafProjectionRuntimeEmpty
import MicroCFTA.SourceEqualityNativeScoped

/-!
# Final literal empty propagation at the independent forest language

The source performs this operation once after the complete class fold.
The test reads only literal EmptyNode membership. Erasure has no constructor
or native effect and retains exactly the accepted ordered term forests.
-/
namespace MicroCFTA.SourceEqualityEmptyPropagation
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open EqualityLeafProjectionRuntimeEmpty (erase propagate empty_test)
open InternedGuardedLanguage (meaning)

/-- An accepted ordered forest cannot contain a literal empty root. -/
theorem accepted_nonempty (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    {values : List (Value Symbol Guard)} {terms : List (Term Symbol)} (accepted : All₂ (meaning holds ambient) values terms) :
    (.empty : Value Symbol Guard) ∉ values := by
  induction accepted with
  | nil => simp
  | cons first rest ih =>
      intro member
      rcases List.mem_cons.mp member with same | member
      · subst same
        simp only [meaning] at first
      · exact ih member

/-- Final propagation preserves the exact independent ordered forest language. -/
theorem exact (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (values : List (Value Symbol Guard)) (terms : List (Term Symbol)) :
    All₂ (meaning holds ambient) (propagate values) terms ↔ All₂ (meaning holds ambient) values terms := by
  unfold propagate
  split
  · rename_i erased
    have member := (empty_test values).mp erased
    have outputMember : (.empty : Value Symbol Guard) ∈ erase values := List.mem_map.mpr ⟨.empty, member, rfl⟩
    exact ⟨fun accepted => False.elim (accepted_nonempty holds ambient accepted outputMember),
      fun accepted => False.elim (accepted_nonempty holds ambient accepted member)⟩
  · rfl

/-- Erasure introduces only available closed empty values in the same constructor heap. -/
theorem erased_scope (heap : State Symbol Guard) (values : List (Value Symbol Guard)) :
    Values heap (erase values) ∧ ClosedValues (erase values) := by
  constructor
  · intro value member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    exact empty_available heap
  · intro value member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
    rfl

/-- Final propagation retains closed physical output scope without any cache change. -/
theorem scope (heap : State Symbol Guard) (values : List (Value Symbol Guard))
    (available : Values heap values) (closed : ClosedValues values) :
    Values heap (propagate values) ∧ ClosedValues (propagate values) := by
  unfold propagate
  split
  · exact erased_scope heap values
  · exact ⟨available, closed⟩

/-- Neither final propagation branch changes the source child-list arity. -/
theorem length (values : List (Value Symbol Guard)) : (propagate values).length = values.length := by
  unfold propagate
  split
  · exact List.length_map _
  · rfl

end MicroCFTA.SourceEqualityEmptyPropagation
