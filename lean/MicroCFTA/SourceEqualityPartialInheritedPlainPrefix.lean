import MicroCFTA.SourceEqualityPartialInheritedPlainPass

/-!
# Literal empty-own edge prefixes for arbitrary inherited payloads

The complete source pass returns the original children or literal empty
slots. Exact edge interning retains the full original guard. Actual
readback derives the child alternatives used by structural completion.
-/
namespace MicroCFTA.SourceEqualityPartialInheritedPlainPrefix
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance (Values)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Every inherited payload derives a complete literal source edge prefix with original or erased structural children. -/
theorem complete (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard)
    (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some []))
    (facts : Facts before.machine.heap) (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge) :
    ∃ narrowed middle, ∃ _trace : SourceEqualityPCSNativeEdge.Execution edge inherited before narrowed middle,
      SourceEqualityPhysicalPayload.own narrowed.entry.key.constraint = .ok (some []) ∧
      (narrowed.children = edge.children ∨ narrowed.children = EqualityLeafProjectionRuntimeEmpty.erase edge.children) := by
  obtain ⟨values, pass, shape⟩ := SourceEqualityPartialInheritedPlainPass.complete inherited edge.children before
  have available : Values before.machine.heap values := by
    rcases shape with same | erased
    · rw [same]
      exact facts.cached.edges _ _ resident
    · rw [erased]
      intro value member
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      exact InternedProbeProvenance.empty_available before.machine.heap
  have fields := MergedPhysicalGroupEdges.makeEdge_fields before.machine.heap facts edge.entry.key.symbol edge.entry.key.constraint values available
  refine ⟨_, _, .done physical pass, ?_, ?_⟩
  · rw [fields.2.1]
    exact physical
  · exact shape.imp (fun same => fields.2.2.trans same) (fun same => fields.2.2.trans same)

/-- Empty own source classes reach no native word request for any inherited payload. -/
theorem ranges (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard)
    (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some [])) :
    SourceEqualityPCSNativeEdge.Ranges edge inherited before := by
  intro payload actual
  have same := Except.ok.inj (physical.symm.trans actual)
  cases same
  change SourceEqualityOnePassGraph.Ranges source top conjoin SourceMemoGate.plain top
    (SourceEqualityPrecheck.precheck (some []) inherited) edge.children before
  rcases SourceEqualityPartialInheritedPlainPass.precheck_cases inherited with unchanged | contradiction | live
  · rw [unchanged]; trivial
  · rw [contradiction]; trivial
  · rw [live]
    intro _ _ _ _ _
    exact .nil

end MicroCFTA.SourceEqualityPartialInheritedPlainPrefix
