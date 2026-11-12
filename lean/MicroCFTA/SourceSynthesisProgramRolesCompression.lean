import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.EnumerationPendingReplacement

/-!
# Program slots across actual representative compression

The existing frame retains exact counters, stores and finite root paths.
The native heap and marked raw occurrences remain the same.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesCompression
open SourceSynthesisProgramEnumerationRoles (ProgramSlots)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {valid : Constraint → Prop} {literal : String → Symbol}

/-- The same exact compression frame transports every marked Program slot. -/
theorem compression_frame_program_slots
    (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (frame : EnumerationCompressionFrame.Frame before after)
    (roles : ProgramSlots valid literal heap before marked) :
    ProgramSlots valid literal heap after marked := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro uv known
    rw [frame.counter]
    exact roles.bounded uv known
  · intro uv known
    obtain ⟨size, path⟩ := roles.roots uv known
    exact ⟨size, (frame.reaches uv uv size).mpr path⟩
  · intro uv known
    exact EnumerationPendingReplacement.frame_incoming uv before after frame (roles.incoming uv known)
  · intro uv known
    obtain ⟨payload, stored, payloadRoles⟩ := roles.stored uv known
    refine ⟨payload, ?_, payloadRoles⟩
    rw [frame.values]
    exact stored

end MicroCFTA.SourceSynthesisProgramRolesCompression
