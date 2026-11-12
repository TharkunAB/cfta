import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourcePruningEnumerationChildEffects
import MicroCFTA.SourcePruningEnumerationNativeReferences

/-!
# Program roles through a non-Program shallow child

The actual child action retains all old marked roots.
The fresh child does not extend the Program mark set.
The result keeps the complete existing child-effects receipt.
The incoming bucket must avoid the current marked classes.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesUnmarkedChild
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationReferences EnumerationDependencies EnumerationDriver InternedConstructorTemplates
open SourceSynthesisProgramEnumerationRoles
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint

/-- The same successful shallow child retains all current Program marks. -/
theorem prepared_child_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (incoming : Node) (scs : List Suspended)
    (before after : Core) (marked : Nat → Prop)
    (safe : Safe before) (slots : ProgramSlots valid literal heap before marked)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv scs)
    (action : EnumerateM Symbol Constraint (Fragment Symbol)) (fragment : Fragment Symbol)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action)
    (actual : Success action before fragment after) :
    Safe after ∧ EnumeratedOrigin before after ∧
      (∀ held, held < before.counter → IsRoot before.representatives held →
        Protected held before after) ∧
      ProgramSlots valid literal heap after marked := by
  obtain ⟨afterSafe, origin, protects⟩ :=
    SourcePruningEnumerationChildEffects.child scs incoming action before after fragment
      safe bounded prepared actual
  have markedProtected : ∀ uv, marked uv → Protected uv before after :=
    fun uv known => protects uv (slots.bounded uv known) (slots.roots uv known)
  refine ⟨afterSafe, origin, protects, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro uv known
    obtain ⟨payload, stored, _role⟩ := slots.stored uv known
    have afterStored := (markedProtected uv known).value.trans stored
    rw [afterSafe.1.aligned]
    exact (List.getElem?_eq_some_iff.mp afterStored).elim (fun bound _ => bound)
  · intro uv known
    exact (markedProtected uv known).root
  · intro uv known
    exact SourcePruningEnumerationNativeReferences.incoming_preserved before after uv scs
      (slots.incoming uv known) (avoids uv known) (markedProtected uv known).classes
      (fun allowed prior bucket => SourcePruningEnumerationNativeReferences.prepared_allowed
        allowed scs incoming action before after fragment prior bucket prepared actual)
  · intro uv known
    obtain ⟨payload, stored, role⟩ := slots.stored uv known
    exact ⟨payload, (markedProtected uv known).value.trans stored, role⟩

end MicroCFTA.SourceSynthesisProgramRolesUnmarkedChild
