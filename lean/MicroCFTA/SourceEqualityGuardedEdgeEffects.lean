import MicroCFTA.SourceEqualityGuardedEdgeGraph

/-!
# Native state and literal fields of source edge reconstruction

The complete pass supplies closed children. The actual edge constructor
retains those children and the original label. Its cache effect advances the
same native state and preserves its domain and memo tables.
-/
namespace MicroCFTA.SourceEqualityGuardedEdgeEffects
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityClassFoldGraph SourceEqualityGuardedEdgeGraph SourceObservations SourceSymbolicIndex
open MergedColdReaderClosedInputs (ClosedValues)
variable {Formula : Type}
local notation "Symbol" => Label Formula
local notation "Guard" => Constraint Formula

/-- Actual guarded-edge reconstruction retains idle native validity, cache histories, and closed children. -/
theorem effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {edge result : EdgeValue Symbol Guard} {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width Symbol Guard}
    (trace : Graph unconstrained emptyGuard conjoin clear top edge inherited before result after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap edge.children) (closed : ClosedValues edge.children) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      InternedEdgeResidency.EdgeResident after.machine.heap result ∧ Values after.machine.heap result.children ∧ ClosedValues result.children ∧
      result.entry.key.symbol = edge.entry.key.symbol ∧ result.entry.key.constraint = edge.entry.key.constraint := by
  cases trace with
  | done physical pass =>
      have children := SourceEqualityOnePassEffects.effects pass ready available closed
      have built := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint _ _ children.1.semantic.ready children.2.2.1
      have semantic := SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint _ _ children.1.semantic children.2.2.1
      have fields := MergedPhysicalGroupEdges.makeEdge_fields _ children.1.semantic.ready.semantic.1.normal.facts
        edge.entry.key.symbol edge.entry.key.constraint _ children.2.2.1
      refine ⟨children.1.advance _ built.1 semantic, children.2.1.trans built.1, built.2.1, ?_, ?_, fields.1, fields.2.1⟩
      · rw [built.2.2]
        exact fun value member => built.1.available value (children.2.2.1 value member)
      · rw [built.2.2]
        exact children.2.2.2

end MicroCFTA.SourceEqualityGuardedEdgeEffects
