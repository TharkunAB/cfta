import MicroCFTA.SourceEqualityPartialPlainRegion

/-!
# Actual empty-payload native prefixes of equality-free caller regions

The concrete source precheck returns unchanged before native requests.
Literal edge interning retains the original guard and ordered children.
The physical descendant payload is empty and stays empty after descent.
-/
namespace MicroCFTA.SourceEqualityPartialPlainPrefix
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

/-- Actual physical combination takes the empty source fast path. -/
theorem combine_empty : SourceEqualityInheritedPayload.combine (some []) (some []) = .ok (some []) := rfl

/-- Actual empty inherited payloads stay empty at every child index. -/
theorem descend_empty (index : Nat) : SourceEqualityDescend.descend (some []) index = some [] := rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Actual empty payload readback selects the immediate unchanged pass and literal edge request. -/
theorem execute (edge : EdgeValue Symbol Guard) (before : NativeState width Symbol Guard)
    (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some [])) :
    let built := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint edge.children) before.machine.heap
    SourceEqualityPCSNativeEdge.Execution edge (some []) before built.1 (advanceHeap before built.2) :=
  .done physical (.unchanged rfl)

omit [DecidableEq Symbol] in
/-- Literal prefix readback derives the exact empty own payload and original structural child list. -/
theorem fields (edge : EdgeValue Symbol Guard) (before : NativeState width Symbol Guard)
    (facts : Facts before.machine.heap) (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge)
    (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some [])) :
    let built := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint edge.children) before.machine.heap
    SourceEqualityPhysicalPayload.own built.1.entry.key.constraint = .ok (some []) ∧ built.1.children = edge.children := by
  have readback := MergedPhysicalGroupEdges.makeEdge_fields before.machine.heap facts edge.entry.key.symbol edge.entry.key.constraint
    edge.children (facts.cached.edges _ _ resident)
  refine ⟨?_, readback.2.2⟩
  rw [readback.2.1]
  exact physical

/-- The actual immediate precheck reaches no primitive native word request. -/
theorem ranges (edge : EdgeValue Symbol Guard) (before : NativeState width Symbol Guard)
    (physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some [])) :
    SourceEqualityPCSNativeEdge.Ranges edge (some []) before := by
  intro payload actual
  have same := Except.ok.inj (physical.symm.trans actual)
  cases same
  trivial

end MicroCFTA.SourceEqualityPartialPlainPrefix
