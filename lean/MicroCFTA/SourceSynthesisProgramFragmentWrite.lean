import MicroCFTA.SourceSynthesisProgramEnumerationRoles

/-!
# Program-role preservation by the actual enumerated-slot write

The same successful setValue step supplies the complete state update.
The new fragment supplies its Program layout. The existing slots retain their
bounds, root identity, protected references, and stored roles.
This result does not assert fragment acyclicity or the complete execution Packet.
-/
namespace MicroCFTA.SourceSynthesisProgramFragmentWrite
open Fragments EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourceSynthesisProgramEnumerationRoles (FragmentRoles SlotRole ProgramSlots)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint

/-- The same actual fragment write preserves every marked Program slot. -/
theorem setValue_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked)
    (uv : Nat) (selected : marked uv) (fragment : Fragment Symbol)
    (roles : FragmentRoles literal marked fragment)
    (written : Success (EnumerationState.setValue uv (.enumerated fragment)) before () after) :
    after = {before with values := before.values.set uv (.enumerated fragment)} ∧
      ProgramSlots valid literal heap after marked := by
  have shape : after = {before with values := before.values.set uv (.enumerated fragment)} :=
    (EnumerationDriver.modify_success _ before after).mp written
  refine ⟨shape, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro held tagged
    simpa only [shape] using slots.bounded held tagged
  · intro held tagged
    simpa only [shape] using slots.roots held tagged
  · intro held tagged
    have allowed := EnumerationReferences.setValue_allowed
      (fun target => ¬UnionFind.SameClass before.representatives held target)
      uv (.enumerated fragment) before after (slots.incoming held tagged)
      (by intro sc member; cases member) written
    simpa only [EnumerationReferences.IncomingAvoid, shape] using allowed
  · intro held tagged
    by_cases same : held = uv
    · subst held
      obtain ⟨_payload, stored, _role⟩ := slots.stored uv selected
      have inside : uv < before.values.length := (List.getElem?_eq_some_iff.mp stored).1
      refine ⟨.enumerated fragment, ?_, SlotRole.enumerated fragment roles⟩
      simp only [shape, List.getElem?_set_self inside]
    · obtain ⟨payload, stored, role⟩ := slots.stored held tagged
      refine ⟨payload, ?_, role⟩
      simpa only [shape, List.getElem?_set_ne (Ne.symm same)] using stored

end MicroCFTA.SourceSynthesisProgramFragmentWrite
