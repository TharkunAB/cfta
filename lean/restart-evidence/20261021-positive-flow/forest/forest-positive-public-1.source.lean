import MicroCFTA.SourceCurrentRequiredPositivePosition
import MicroCFTA.SourceCurrentRequiredPrimaryExposure

/-!
# Positive positions in actual Required forest returns

Original false class traces supply the selected exposure safety.
Each prepared positive occurrence retains the same forest slot and
natural child path. No false gate is imposed on the prepared forest.
-/
namespace MicroCFTA.SourceCurrentRequiredForestPositive
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityNeeded EndpointStatefulGateTrace
open SourceCurrentRequiredRowOrigins (Origin)
open SourceCurrentRequiredPositivePosition (PositiveAt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- A positive prepared slot retains its original slot and path under the actual selected Required return. -/
theorem requireAll [edgeEq : DecidableEq (EdgeKey Symbol Guard)]
    {fuel readFuel : Nat} {selected : EqualityNormalize.Constraints}
    {originals prepared : List Node} {before after : Heap} {index : Nat} {output : Node} {path : List Nat}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths selected) originals before = .done prepared after)
    (semantic : SemanticReady before) (normal : SourceCurrentRequiredUnionNormal.UnionNormal before)
    (costs : CostHeap before) (available : Values before originals) (guards : Guards before)
    (primary : ∀ paths ∈ selected, ClassTrace source reaches originals paths before false before)
    (found : prepared[index]? = some output) (positive : PositiveAt output path) :
    ∃ original, originals[index]? = some original ∧ PositiveAt original path := by
  have same : edgeEq = SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint :=
    Subsingleton.elim _ _
  cases same
  letI : DecidableEq (EdgeKey Symbol Guard) :=
    SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff
    (SourceEqualitySelectedRequired.paths selected) originals before prepared after).mpr ⟨fuel, readFuel, actual⟩
  cases compiled : build (SourceEqualitySelectedRequired.paths selected) with
  | node entries =>
      simp only [compiled] at graph
      have domain := SourceCurrentRequiredPrimaryExposure.selected_domain originals selected before
        semantic normal available primary entries compiled
      have safe : SourceCurrentRequiredRowOrigins.ChildrenSafe entries 0 originals := by
        intro offset needed selectedNeeded value atOffset
        exact domain offset needed (by simpa only [Nat.zero_add] using selectedNeeded) value atOffset
      have related : All₂ Origin originals prepared :=
        SourceCurrentRequiredRowOrigins.children graph semantic costs available guards safe
      obtain ⟨original, originalFound, origin⟩ :=
        SourceEqualityProjectionLanguage.all₂_selected related index output found
      exact ⟨original, originalFound, SourceCurrentRequiredPositivePosition.origin origin positive⟩

end MicroCFTA.SourceCurrentRequiredForestPositive

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 16384
set_option maxHeartbeats 0

#check @MicroCFTA.SourceCurrentRequiredForestPositive.requireAll
#print MicroCFTA.SourceCurrentRequiredForestPositive.requireAll
#print axioms MicroCFTA.SourceCurrentRequiredForestPositive.requireAll
