import MicroCFTA.SourceCurrentSameSymbolEdgeStable
import MicroCFTA.SourceCurrentAllocatedNativePairAdmission

namespace MicroCFTA.SourceCurrentSameSymbolEdgeModelTransport
open Language IntersectSchedule InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State

/-- Retain the same populated pair memo under admitted finite input agreement. -/
theorem rebase
    {width : Nat} {oldView newView : View Symbol}
    (before : FiniteInput oldView) (after : FiniteInput newView)
    (agreement : SourceCurrentAllocatedNativeContextRebase.Agreement before after)
    (holds : Guard → Term Symbol → Bool) (state : Wrapper width)
    (stable : SourceCurrentSameSymbolEdgeStable.Stable oldView
      (finiteInputMeaning oldView before) (finiteRankedInput oldView before) holds state)
    (admitted : ∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
      state.memo.cells handle = some ⟨pair, .returned value⟩ →
      let ordered := if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair
      SourceCurrentAllocatedNativeContextCache.EdgeInputs oldView
        (finiteInputMeaning oldView before)
        ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩) :
    SourceCurrentSameSymbolEdgeStable.Stable newView
      (finiteInputMeaning newView after) (finiteRankedInput newView after) holds state := by
  refine ⟨⟨stable.valid.bounded, stable.valid.linked, ?_⟩,
    stable.returned, stable.canonical⟩
  intro handle cell stored
  obtain ⟨leftResident, rightResident, law⟩ := stable.valid.checked handle cell stored
  refine ⟨leftResident, rightResident, ?_⟩
  rcases cell with ⟨pair, status⟩
  cases status with
  | suspended | evaluating => trivial
  | returned value =>
      exact ⟨law.1,
        SourceCurrentAllocatedNativeContextRebase.edge_law agreement holds
          _ value (admitted handle pair value stored)
          (SourceCurrentAllocatedNativePairAdmission.empty_seen before) law.2⟩

end MicroCFTA.SourceCurrentSameSymbolEdgeModelTransport

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentSameSymbolEdgeModelTransport.rebase
#print MicroCFTA.SourceCurrentSameSymbolEdgeModelTransport.rebase
#print axioms MicroCFTA.SourceCurrentSameSymbolEdgeModelTransport.rebase
