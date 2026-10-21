import MicroCFTA.SourceCurrentTargetOperandPositivePosition

/-!
# Positive positions in later target operand heaps

The prepared forest remains fixed. Actual forward heap retention supplies
its availability. The original false gates remain at the Required entry.
Current semantic, cost, guard and Merge support remain explicit.
-/
namespace MicroCFTA.SourceCurrentTargetLaterHeapPositivePosition
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph EndpointStatefulGateTrace
open SourceCurrentRequiredRowOrigins (Origin)
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentMergePositivePosition (Support)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- A later supported operand heap retains the fixed original slot and full positive path. -/
theorem operand [symbolEq : DecidableEq Symbol] [edgeEq : DecidableEq (EdgeKey Symbol Guard)]
    {width requiredFuel requiredReadFuel projectionFuel readFuel mergeFuel selectionFuel : Nat}
    {selected : EqualityNormalize.Constraints} {originals prepared : List Node}
    {scanHeap preparedHeap : Heap} {index : Nat} {path residual : List Nat}
    {chosenClass : EqualityNormalize.Class}
    {before after : SourceEqualityNativeDemand.State width}
    {memo saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard} {result : Node}
    (required : SourceEqualityRequiredExecution.requireAll requiredFuel requiredReadFuel
      (SourceEqualitySelectedRequired.paths selected) originals scanHeap = .done prepared preparedHeap)
    (semantic : SemanticReady scanHeap) (normal : SourceCurrentRequiredUnionNormal.UnionNormal scanHeap)
    (costs : CostHeap scanHeap) (available : Values scanHeap originals) (guards : Guards scanHeap)
    (primary : ∀ paths ∈ selected, ClassTrace source reaches originals paths scanHeap false scanHeap)
    (chosen : chosenClass ∈ selected) (included : index :: path ∈ chosenClass)
    (later : Keeps preparedHeap before.native.machine.heap)
    (beforeSemantic : SemanticReady before.native.machine.heap)
    (beforeCosts : CostHeap before.native.machine.heap) (beforeGuards : Guards before.native.machine.heap)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (support : Support memo)
    (actual : SourceCurrentAllocatedTargetWorker.operand projectionFuel readFuel mergeFuel selectionFuel
      ((index :: path).map Int.ofNat) prepared before memo = .done result after saved)
    (positive : PositiveAt result residual) :
    Support saved ∧ ∃ original, originals[index]? = some original ∧ PositiveAt original (path ++ residual) := by
  have sameEdge : edgeEq = SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint :=
    Subsingleton.elim _ _
  cases sameEdge
  letI : DecidableEq (EdgeKey Symbol Guard) :=
    SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint
  have sameSymbol : symbolEq = @instDecidableEqProd SourceGuards.Name FullSyntax.Formula
      instDecidableEqString FormulaExecutable.formulaDecidableEq := Subsingleton.elim _ _
  cases sameSymbol
  letI : DecidableEq Symbol := @instDecidableEqProd SourceGuards.Name FullSyntax.Formula
    instDecidableEqString FormulaExecutable.formulaDecidableEq
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
    obtain ⟨projected,middle,current,projectionDone,mergeDone⟩ :=
      (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
    obtain ⟨heap,forest,shape,sameMemo⟩ := SourceCurrentAllocatedTargetWorkerSound.projection_sound
      projectionFuel readFuel ((index :: path).map Int.ofNat) prepared before memo projected middle current projectionDone
    subst current
    have beforeValues : Values before.native.machine.heap prepared :=
      fun value member => later.available value (requiredEffects.2.2.2.2 value member)
    have facts := SourceEqualityProjectionCosts.forest_effects forest beforeSemantic beforeCosts beforeValues
    have middleHeap : middle.native.machine.heap = heap := by rw [shape]; rfl
    have currentSemantic : SemanticReady middle.native.machine.heap := by simpa only [middleHeap] using facts.2.1
    have currentCosts : CostHeap middle.native.machine.heap := by simpa only [middleHeap] using facts.2.2.1
    have currentStored : SourceCurrentMemoMergeEffects.Stored middle.native.machine.heap memo := by
      simpa only [middleHeap] using stored.grows facts.1
    have currentAvailable : Available middle.native.machine.heap projected := by simpa only [middleHeap] using facts.2.2.2
    cases called : SourceCurrentAllocatedMergeWorker.call SourceCurrentAllocatedMerge.literalClear
        mergeFuel selectionFuel projected (physical middle) memo with
    | failed =>
      simp only [SourceCurrentAllocatedTargetWorker.merge,called] at mergeDone
      cases mergeDone
    | done output final current =>
      simp only [SourceCurrentAllocatedTargetWorker.merge,called] at mergeDone
      cases mergeDone
      have merged := SourceCurrentMergePositivePosition.allocated SourceCurrentAllocatedMerge.literalClear called
        currentSemantic currentCosts currentStored support currentAvailable
      have projectedPositive := merged.2.2.2.2 residual positive
      refine ⟨merged.2.2.1, ?_⟩
      cases forest with
      | missing absent => cases projectedPositive
      | selected found actualProject =>
        have natural := found
        simp only [select,Int.ofNat_eq_natCast,
          ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] at natural
        obtain ⟨original, originalFound, origin⟩ :=
          SourceEqualityProjectionLanguage.all₂_selected related index _ natural
        have gatePath := SourceCurrentRequiredPrimaryExposure.false_class_paths originals chosenClass scanHeap scanHeap
          (primary chosenClass chosen) semantic available scanHeap (grows_refl _) (index :: path) included
        have gate : NodeTrace source reaches path original scanHeap false scanHeap := by
          cases gatePath with
          | child traced => exact SourceCurrentRequiredPrimaryExposure.false_selected traced originalFound
        refine ⟨original, originalFound, ?_⟩
        exact SourceCurrentTargetOperandPositivePosition.project path original _ scanHeap scanHeap before.native.machine.heap heap projected origin gate
          semantic normal (available _ (List.mem_of_getElem? originalFound)) beforeSemantic beforeCosts
          (beforeValues _ (select_member found)) beforeGuards actualProject projectedPositive


end MicroCFTA.SourceCurrentTargetLaterHeapPositivePosition
