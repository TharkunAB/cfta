import MicroCFTA.SourceCurrentOriginalGateProjectionCap
import MicroCFTA.SourceCurrentRequiredPrimaryExposure
import MicroCFTA.SourceEqualityProjectionLanguage
import MicroCFTA.SourceEqualityRequiredExecution

/-!
# Finite caps at actual selected forest projections

The actual Required return fixes the prepared forest. Forward Keeps retains
its availability at the projection heap. The false gates remain on the
original forest at the Required entry. The projected endpoint has a finite
Plain cap. The result does not bound unrelated original branches.
-/
namespace MicroCFTA.SourceCurrentRequiredForestProjectionCap
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph EndpointStatefulGateTrace
open SourceCurrentRequiredRowOrigins (Origin)
open SourceCurrentConstrainedCap (Cap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- An actual selected forest projection derives its cap from the original false gates. -/
theorem project [edgeEq : DecidableEq (EdgeKey Symbol Guard)]
    {requiredFuel requiredReadFuel : Nat}
    {selected : EqualityNormalize.Constraints} {originals prepared : List Node}
    {scanHeap preparedHeap currentHeap afterHeap : Heap} {index : Nat} {path : List Nat}
    {chosenClass : EqualityNormalize.Class} {result : Node}
    (required : SourceEqualityRequiredExecution.requireAll requiredFuel requiredReadFuel
      (SourceEqualitySelectedRequired.paths selected) originals scanHeap = .done prepared preparedHeap)
    (semantic : SemanticReady scanHeap) (normal : SourceCurrentRequiredUnionNormal.UnionNormal scanHeap)
    (costs : CostHeap scanHeap) (available : Values scanHeap originals) (guards : Guards scanHeap)
    (primary : ∀ paths ∈ selected, ClassTrace source reaches originals paths scanHeap false scanHeap)
    (chosen : chosenClass ∈ selected) (included : index :: path ∈ chosenClass)
    (later : Keeps preparedHeap currentHeap)
    (currentSemantic : SemanticReady currentHeap) (currentCosts : CostHeap currentHeap)
    (currentGuards : Guards currentHeap)
    (actual : Forest ((index :: path).map Int.ofNat) prepared currentHeap result afterHeap) :
    ∃ depth, Cap Plain depth result := by
  have sameEdge : edgeEq = SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint :=
    Subsingleton.elim _ _
  cases sameEdge
  letI : DecidableEq (EdgeKey Symbol Guard) :=
    SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint
  have requiredEffects := SourceCurrentRequiredHeapEffects.requireAll (fun _ => True)
    requiredFuel requiredReadFuel (SourceEqualitySelectedRequired.paths selected) originals prepared scanHeap preparedHeap
    required semantic costs (fun _ _ _ => trivial) available
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff
    (SourceEqualitySelectedRequired.paths selected) originals scanHeap prepared preparedHeap).mpr
      ⟨requiredFuel, requiredReadFuel, required⟩
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected) with
  | node entries =>
    simp only [compiled] at graph
    have domain := SourceCurrentRequiredPrimaryExposure.selected_domain originals selected scanHeap
      semantic normal available primary entries compiled
    have safe : SourceCurrentRequiredRowOrigins.ChildrenSafe entries 0 originals := by
      intro offset needed selectedNeeded value atOffset
      exact domain offset needed (by simpa only [Nat.zero_add] using selectedNeeded) value atOffset
    have related : All₂ Origin originals prepared :=
      SourceCurrentRequiredRowOrigins.children graph semantic costs available guards safe
    have currentValues : Values currentHeap prepared :=
      fun value member => later.available value (requiredEffects.2.2.2.2 value member)
    cases actual with
    | missing absent => exact ⟨0, .plain 0 .empty⟩
    | selected found projection =>
      have natural := found
      simp only [select, Int.ofNat_eq_natCast,
        ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)), Int.toNat_natCast] at natural
      obtain ⟨original, originalFound, origin⟩ :=
        SourceEqualityProjectionLanguage.all₂_selected related index _ natural
      have gatePath := SourceCurrentRequiredPrimaryExposure.false_class_paths originals chosenClass scanHeap scanHeap
        (primary chosenClass chosen) semantic available scanHeap (grows_refl _) (index :: path) included
      have gate : NodeTrace source reaches path original scanHeap false scanHeap := by
        cases gatePath with
        | child traced => exact SourceCurrentRequiredPrimaryExposure.false_selected traced originalFound
      exact SourceCurrentOriginalGateProjectionCap.project path original _ scanHeap scanHeap currentHeap afterHeap result
        origin gate semantic (available _ (List.mem_of_getElem? originalFound)) currentSemantic currentCosts
        (currentValues _ (select_member found)) currentGuards projection

end MicroCFTA.SourceCurrentRequiredForestProjectionCap

set_option linter.all true
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentRequiredForestProjectionCap.project
#print MicroCFTA.SourceCurrentRequiredForestProjectionCap.project
#print axioms MicroCFTA.SourceCurrentRequiredForestProjectionCap.project
