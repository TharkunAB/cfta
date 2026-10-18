import MicroCFTA.SourceCurrentRequiredProjectionOrigins
import MicroCFTA.SourceCurrentRequiredPrimaryOrigins
import MicroCFTA.SourceCurrentActualMergeOperandOrigins

/-!
# Original row sources through Required and literal target operands

The primary certificate names the original forest. Required produces a
different forest. A literal target operand projects that prepared forest.
Its positive row retains original fields and ordered child origins.
The actual Merge writer uses the prepared children in their original order.
Only the original source children have the stated source mass bound.
-/
namespace MicroCFTA.SourceCurrentRequiredTargetOperandOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead
open SourceCurrentMergePositiveRowOrigins EndpointStatefulGateTrace
open SourceCurrentRequiredRowOrigins (Origin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "literalClear" => SourceCurrentAllocatedMerge.literalClear
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

private theorem origin_index {originals prepared : List Node} (origins : All₂ Origin originals prepared)
    {index : Nat} {value : Node} (selected : prepared[index]? = some value) :
    ∃ original, originals[index]? = some original ∧ Origin original value := by
  induction origins generalizing index with
  | nil => cases selected
  | cons first rest ih =>
    cases index with
    | zero =>
      cases Option.some.inj selected
      exact ⟨_,rfl,first⟩
    | succ index =>
      obtain ⟨original,found,related⟩ := ih (by simpa only [List.getElem?_cons_succ] using selected)
      exact ⟨original,by simpa only [List.getElem?_cons_succ] using found,related⟩

section Actual
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem required_origins {fuel readFuel : Nat} {paths : EqualityNormalize.Class}
    {values prepared : List Node} {initial anchor before after : Heap}
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel
      (paths.map (List.map Int.ofNat)) values before = .done prepared after)
    (gate : ClassTrace source reaches values paths initial false anchor)
    (initialSemantic : SemanticReady initial) (initialAvailable : Values initial values)
    (semantic : SemanticReady before) (normal : SourceCurrentRequiredUnionNormal.UnionNormal before)
    (costs : CostHeap before) (guards : Guards before) (available : Values before values)
    (growth : Grows anchor before) : All₂ Origin values prepared ∧ Guards after := by
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff
    (paths.map (List.map Int.ofNat)) values before prepared after).mpr ⟨fuel,readFuel,actual⟩
  cases compiled : SourceEqualityNeeded.build (paths.map (List.map Int.ofNat)) with
  | node entries =>
    simp only [compiled] at graph
    exact ⟨SourceCurrentRequiredRowOrigins.children graph semantic costs available guards
      (SourceCurrentRequiredPrimaryExposure.primary_domain gate initialSemantic initialAvailable
        before semantic normal available growth entries compiled),
      SourceCurrentRequiredGuard.children Plain graph semantic costs available guards⟩

/-- An actual Required return and target operand retain original row fields and ordered changed-child origins. -/
theorem operand {requiredFuel requiredReadFuel projectionFuel readFuel mergeFuel selectionFuel : Nat}
    (index : Nat) (path : EqualityNormalize.Path) (paths : EqualityNormalize.Class)
    (values prepared : List Node) (requiredBefore requiredAfter : Heap)
    (before after : Checked width) (memo saved : Memo) (result : Node)
    (required : SourceEqualityRequiredExecution.requireAll requiredFuel requiredReadFuel
      (paths.map (List.map Int.ofNat)) values requiredBefore = .done prepared requiredAfter)
    (actual : SourceCurrentAllocatedTargetWorker.operand projectionFuel readFuel mergeFuel selectionFuel
      ((index :: path).map Int.ofNat) prepared before memo = .done result after saved)
    (sameHeap : before.native.machine.heap = requiredAfter)
    (requiredSemantic : SemanticReady requiredBefore)
    (requiredNormal : SourceCurrentRequiredUnionNormal.UnionNormal requiredBefore)
    (requiredCosts : CostHeap requiredBefore) (requiredGuards : Guards requiredBefore)
    (requiredAvailable : Values requiredBefore values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (raw : Raw literalClear top memo) (gateBefore gateAfter : Heap)
    (gate : ClassTrace source reaches values paths gateBefore false gateAfter)
    (initialSemantic : SemanticReady gateBefore)
    (initialAvailable : Values gateBefore values) (retained : Grows gateAfter requiredBefore)
    (included : index :: path ∈ paths)
    (row : Row) (member : row ∈ nodeEdges result) (records : List SourceEqualityClassOrder.Record)
    (positive : SourceEqualityPhysicalPayload.own row.entry.key.constraint = .ok (some records))
    (nonempty : records ≠ []) :
    Raw literalClear top saved ∧
    ∃ (projected : Node) (middle : Checked width) (sourceValue preparedValue : Node)
      (sourceIndex : Nat) (preparedRow original : Row),
      SourceCurrentAllocatedTargetWorker.projection projectionFuel readFuel ((index :: path).map Int.ofNat)
        prepared before memo = .done projected middle memo ∧
      SourceCurrentAllocatedTargetWorker.merge mergeFuel selectionFuel projected middle memo = .done result after saved ∧
      Forest ((index :: path).map Int.ofNat) prepared before.native.machine.heap projected middle.native.machine.heap ∧
      Writer literalClear top projected result ∧ values[index]? = some sourceValue ∧
      prepared[index]? = some preparedValue ∧ (nodeEdges projected)[sourceIndex]? = some preparedRow ∧
      Project (path.map Int.ofNat) preparedValue before.native.machine.heap projected middle.native.machine.heap ∧
      SourceCurrentPositiveProjectionSourceRoute.Route (path.map Int.ofNat) sourceValue original ∧
      SourceCurrentRequiredGuardOrigins.RowOrigin original preparedRow ∧
      All₂ Origin original.children preparedRow.children ∧
      row.entry.key.symbol = preparedRow.entry.key.symbol ∧ row.entry.key.constraint = preparedRow.entry.key.constraint ∧
      (∀ child ∈ original.children, InternedValueMass.value child < InternedValueMass.value sourceValue) ∧
      (row = preparedRow ∨ ∃ start current finish final,
        SourceCurrentMemoMergeGraph.Run literalClear top
          (SourceCurrentMemoMergeGraph.map SourceCurrentMemoMergeGraph.Code.request preparedRow.children)
          start current row.children finish final) := by
  have preparedFacts := SourceCurrentRequiredHeapEffects.requireAll (fun _ => True)
    requiredFuel requiredReadFuel (paths.map (List.map Int.ofNat)) values prepared requiredBefore requiredAfter
    required requiredSemantic requiredCosts (fun _ _ _ => trivial) requiredAvailable
  obtain ⟨origins,preparedGuards⟩ := required_origins required gate initialSemantic initialAvailable
    requiredSemantic requiredNormal requiredCosts requiredGuards requiredAvailable retained
  have semantic : SemanticReady before.native.machine.heap := sameHeap ▸ preparedFacts.2.1
  have costs : CostHeap before.native.machine.heap := sameHeap ▸ preparedFacts.2.2.1
  have available : Values before.native.machine.heap prepared := sameHeap ▸ preparedFacts.2.2.2.2
  have guards : Guards before.native.machine.heap := sameHeap ▸ preparedGuards
  obtain ⟨finalRaw,projected,middle,projectionDone,mergeDone,graph,writer,
      sourceIndex,preparedRow,found,symbol,guard,children⟩ :=
    SourceCurrentActualMergeOperandOrigins.operand actual semantic costs stored available raw row member records positive nonempty
  have effects := SourceEqualityProjectionCosts.forest_effects graph semantic costs available
  have middleGuards := SourceCurrentConstrainedCapProjectionGuard.forest Plain graph semantic costs available guards
  have selected : preparedRow ∈ nodeEdges projected := List.mem_of_getElem? found
  have nonPlain : ¬ Plain preparedRow.entry.key.constraint := by
    intro accepted
    have emptyOwn := SourceCurrentHereditaryUnconstrained.plain_physical _ accepted
    rw [← guard,positive] at emptyOwn
    exact nonempty (Option.some.inj (Except.ok.inj emptyOwn))
  have read : Read projected middle.native.machine.heap (nodeEdges projected) middle.native.machine.heap := by
    cases projected with
    | empty | node => exact .done 0 rfl
    | reference | union | mu => cases selected
  cases graph with
  | missing absent =>
    cases selected
  | selected chosen project =>
    rename_i preparedValue
    have natural : prepared[index]? = some preparedValue := by
      simpa only [select,Int.ofNat_eq_natCast,
        ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] using chosen
    obtain ⟨sourceValue,originalFound,origin⟩ := origin_index origins natural
    have pathGate := SourceCurrentRequiredPrimaryExposure.false_class_paths values paths gateBefore gateAfter
      gate initialSemantic initialAvailable requiredBefore retained (index :: path) included
    have nodeGate : NodeTrace source reaches path sourceValue requiredBefore false requiredBefore := by
      cases pathGate with
      | child traced => exact SourceCurrentRequiredPrimaryExposure.false_selected traced originalFound
    obtain ⟨original,route,fields,childOrigins⟩ :=
      SourceCurrentRequiredProjectionOrigins.project_read path sourceValue preparedValue requiredBefore requiredBefore
        before.native.machine.heap middle.native.machine.heap projected origin nodeGate requiredSemantic
        requiredNormal (requiredAvailable sourceValue (List.mem_of_getElem? originalFound))
        semantic costs (available preparedValue (List.mem_of_getElem? natural)) guards project
        middle.native.machine.heap effects.2.1 middleGuards (pure_keeps _ effects.2.1.ready)
        (nodeEdges projected) middle.native.machine.heap read preparedRow selected nonPlain
    exact ⟨finalRaw,projected,middle,sourceValue,preparedValue,sourceIndex,preparedRow,original,
      projectionDone,mergeDone,.selected chosen project,writer,originalFound,natural,found,project,route,fields,
      childOrigins,symbol,guard,fun child present => route.mass_lt child present,children⟩

end Actual
end MicroCFTA.SourceCurrentRequiredTargetOperandOrigins
