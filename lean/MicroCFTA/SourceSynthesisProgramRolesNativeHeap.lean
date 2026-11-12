import MicroCFTA.SourceSynthesisProgramEnumerationRoles

/-!
# Program slot roles across actual native heap growth

The existing native Keeps relation retains each successful node lookup.
The enumeration Core and its marked raw occurrences stay fixed.
Actual caller Post.effects.keeps supplies this native relation.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesNativeHeap
open EnumerationState InternedConstructorTemplates
open SourceSynthesisProgramEnumerationRoles
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {valid : Constraint → Prop} {literal : String → Symbol}

/-- Actual native growth retains every marked slot and its complete payload role. -/
theorem keeps_program_slots
    (beforeHeap afterHeap : NativeHeap) (state : Core) (marked : Nat → Prop)
    (kept : SourceEqualityRequiredCache.Keeps beforeHeap afterHeap)
    (roles : ProgramSlots valid literal beforeHeap state marked) :
    ProgramSlots valid literal afterHeap state marked := by
  refine ⟨roles.bounded, roles.roots, roles.incoming, ?_⟩
  intro uv known
  obtain ⟨payload, stored, role⟩ := roles.stored uv known
  refine ⟨payload, stored, ?_⟩
  cases role with
  | pending handle scs value decoded fields validTries annotationPaths =>
      exact .pending handle scs value
        (lookupNode_keeps beforeHeap afterHeap kept handle value decoded)
        fields validTries annotationPaths
  | enumerated fragment shaped => exact .enumerated fragment shaped

end MicroCFTA.SourceSynthesisProgramRolesNativeHeap
