import MicroCFTA.SourceSynthesisProgramEnumerationRoles

/-!
# Program-role preservation through unmarked raw writes

The payload may have any shape at an unmarked raw target.
Its suspended references avoid every current marked root.
The actual write preserves the complete marked-slot role certificate.
This result does not assert safety or fragment dependency order.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesUnmarkedWrite
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver
open InternedConstructorTemplates SourceSynthesisProgramEnumerationRoles
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint

/-- One actual unmarked raw write retains all marked Program roles and protected roots. -/
theorem setValue_unmarked_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked)
    (target : Nat) (unmarked : ¬marked target) (payload : UVarValue Symbol)
    (avoids : ∀ held, marked held → Avoids before.representatives held (references payload))
    (written : Success (EnumerationState.setValue target payload) before () after) :
    after = {before with values := before.values.set target payload} ∧
      ProgramSlots valid literal heap after marked ∧
      ∀ held, marked held → Protected held before after := by
  have shape : after = {before with values := before.values.set target payload} :=
    (EnumerationDriver.modify_success _ before after).mp written
  subst after
  have protects : ∀ held, marked held →
      Protected held before {before with values := before.values.set target payload} := by
    intro held known
    have different : target ≠ held := by
      intro same
      exact unmarked (same.symm ▸ known)
    exact ⟨by simp only [List.getElem?_set_ne different], slots.roots held known, fun _ => Iff.rfl⟩
  refine ⟨rfl, ?_, protects⟩
  refine ⟨slots.bounded, slots.roots, ?_, ?_⟩
  · intro held known
    exact EnumerationReferences.setValue_allowed
      (fun uv => ¬UnionFind.SameClass before.representatives held uv)
      target payload before _ (slots.incoming held known) (avoids held known) written
  · intro held known
    obtain ⟨value, stored, role⟩ := slots.stored held known
    exact ⟨value, (protects held known).value.trans stored, role⟩

end MicroCFTA.SourceSynthesisProgramRolesUnmarkedWrite
