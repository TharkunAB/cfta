import MicroCFTA.SourceCurrentRequiredForestProjectionCap
import MicroCFTA.SourceCurrentConstrainedCapMixedShared

/-!
# Local target caps from actual Required captures

Each competing operand uses its own projected cap. A miss stores the cap
of its actual result. A hit reuses the cap of the same stored slot value.
-/
namespace MicroCFTA.SourceCurrentRequiredSharedTargetCap
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache EndpointStatefulGateTrace
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State initial store Ready)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentConstrainedCap (Cap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "ClassReady" => SourceCurrentConjunctionClassScan.Ready
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "physical" => SourceCurrentAllocatedNativeEffects.physical
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
variable {width : Nat}

/-- Current native and Merge laws retain a finite cap for each present target value. -/
structure Stored (state : State width) : Prop where
  current : Current state.checked
  merge : MergeStored state.memo
  slots : ∀ path value, state.targets path = some value → ∃ depth, Cap Plain depth value

/-- Empty slots derive every slot obligation from the supplied current native and Merge laws. -/
theorem initial_stored (checked : Checked width) (memo : Memo) (current : Current checked) (merged : MergeStored memo) :
    Stored (initial checked memo) :=
  ⟨current,merged,by intro path value absent; cases absent⟩

private theorem store_stored (state : State width) (path : EqualityNormalize.Path) (value : Node)
    (checked : Checked width) (memo : Memo) (stored : Stored state) (current : Current checked)
    (merged : MergeStored memo) (bounded : ∃ depth, Cap Plain depth value) : Stored (store state path value checked memo) := by
  refine ⟨current,merged,?_⟩
  intro other result found
  by_cases same : other = path
  · subst other
    have identity : value = result := Option.some.inj (by simpa only [store,put,ite_true] using found)
    exact identity ▸ bounded
  · exact stored.slots other result (by simpa only [store,put,same,ite_false] using found)

section Source
variable [DecidableEq (EdgeKey Symbol Guard)]
private structure Data (record : SourceEqualityClassOrder.Record) (prepared : List Node) (preparedHeap : Heap) where
  requiredFuel : Nat
  readFuel : Nat
  selected : EqualityNormalize.Constraints
  originals : List Node
  scanHeap : Heap
  required : SourceEqualityRequiredExecution.requireAll requiredFuel readFuel
    (SourceEqualitySelectedRequired.paths selected) originals scanHeap = .done prepared preparedHeap
  semantic : SemanticReady scanHeap
  normal : SourceCurrentRequiredUnionNormal.UnionNormal scanHeap
  costs : CostHeap scanHeap
  available : Values scanHeap originals
  guards : Guards scanHeap
  primary : ∀ paths ∈ selected, ClassTrace source reaches originals paths scanHeap false scanHeap
  chosen : record.paths ∈ selected

private theorem prepared_available {record prepared preparedHeap} (data : Data record prepared preparedHeap) :
    Values preparedHeap prepared :=
  (SourceCurrentRequiredHeapEffects.requireAll (fun _ => True) data.requiredFuel data.readFuel
    (SourceEqualitySelectedRequired.paths data.selected) data.originals prepared data.scanHeap preparedHeap data.required
    data.semantic data.costs (fun _ _ _ => trivial) data.available).2.2.2.2

variable [DecidableEq Symbol]
private theorem operand_cap {record prepared preparedHeap} (data : Data record prepared preparedHeap)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {path : List Int} {before after : Checked width} {memo saved : Memo}
    {result : Node} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path prepared before memo result after saved memos final)
    (proper : ∃ natural, natural ∈ record.paths ∧ natural ≠ [] ∧ path = natural.map Int.ofNat)
    (ready : ClassReady before) (captured : Keeps preparedHeap before.native.machine.heap)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (merged : MergeStored memo) (current : Current before) :
    MergeStored saved ∧ Current after ∧ ∃ depth, Cap Plain depth result := by
  obtain ⟨natural,member,nonempty,rfl⟩ := proper
  cases natural with
  | nil => exact False.elim (nonempty rfl)
  | cons index path =>
    obtain ⟨projected,middle,currentMemos,projection,mergedReceipt⟩ := receipt.actual
    obtain ⟨depth,bounded⟩ := SourceCurrentRequiredForestProjectionCap.project data.required data.semantic data.normal
      data.costs data.available data.guards data.primary data.chosen member captured ready.semantic ready.costs
      current.1.guards projection.graph
    have projectedGuards := SourceCurrentConstrainedCapProjectionGuard.forest Plain projection.graph
      ready.semantic ready.costs (fun value member => captured.available value (prepared_available data value member)) current.1.guards
    have projectedCurrent := SourceCurrentConstrainedCapCurrentNative.advance Plain before middle current projection.ready.good
      projection.ready.semantic.ready.semantic projectedGuards projection.extension projection.nodes projection.edges
    have retained := SourceCurrentConstrainedCapMergeJointEffects.merge Plain formulas solver inventory
      mergedReceipt.actual projection.ready projection.admitted (physicalStored.grows projection.effects.keeps)
      projection.available projectedCurrent
    cases mergedReceipt.actual with
    | done call =>
      have produced := SourceCurrentConstrainedCapMemoMerge.retained Plain SourceCurrentUnconstrainedGuardClosure.top_plain
        call.graph projection.ready.semantic projection.ready.costs (physicalStored.grows projection.effects.keeps)
        merged projection.available depth bounded
      exact ⟨produced.2.2.1,retained.1,depth,produced.2.2.2.2⟩

private theorem fold_cap {record prepared preparedHeap} (data : Data record prepared preparedHeap)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {seed : List Int} {paths : List (List Int)} {before after : Checked width} {memo saved : Memo}
    {result : Node} {memos final : Memos} {actual : Fold prepared seed paths before memo result after saved}
    (reads : FoldReads formulas solver actual memos final) :
    ClassReady before → Keeps preparedHeap before.native.machine.heap → PhysicalStored before.native.machine.heap memo →
    MergeStored memo → Current before →
    (∀ path ∈ seed::paths, ∃ natural, natural ∈ record.paths ∧ natural ≠ [] ∧ path = natural.map Int.ofNat) →
    ClassReady after ∧ Effects (physical before) (physical after) ∧ PhysicalStored after.native.machine.heap saved ∧
    MergeStored saved ∧ Current after ∧ Available after.native.machine.heap result ∧ result.free = [] ∧
    ∃ depth, Cap Plain depth result := by
  induction reads with
  | nil receipt =>
    intro ready captured physicalStored merged current proper
    have own := operand_cap data receipt (proper _ List.mem_cons_self) ready captured physicalStored merged current
    exact ⟨receipt.ready,receipt.effects,receipt.stored,own.1,own.2.1,receipt.available,receipt.closed,own.2.2⟩
  | cons receipt remaining query ih =>
    intro ready captured physicalStored merged current proper
    have own := operand_cap data receipt (proper _ (by simp)) ready captured physicalStored merged current
    obtain ⟨tailReady,tailEffects,tailPhysical,tailMerged,tailCurrent,tailAvailable,tailClosed,tailDepth,tailCap⟩ :=
      ih receipt.ready (captured.trans receipt.effects.keeps) receipt.stored own.1 own.2.1 (by
        intro path member
        rcases List.mem_cons.mp member with rfl | later
        · exact proper _ List.mem_cons_self
        · exact proper _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ later)))
    obtain ⟨headDepth,headCap⟩ := own.2.2
    have checked := SourceCurrentConstrainedCapCurrentNative.step (max headDepth tailDepth) formulas solver query.actual
      tailReady.good tailReady.semantic tailCurrent (tailEffects.keeps.available _ receipt.available)
      tailAvailable receipt.closed tailClosed (headCap.mono (Nat.le_max_left _ _)) (tailCap.mono (Nat.le_max_right _ _))
    exact ⟨query.ready,receipt.effects.trans (tailEffects.trans query.effects),tailPhysical.grows query.effects.keeps,
      tailMerged,checked.1,query.available,query.closed,_,checked.2.1⟩

private theorem target_cap {record prepared preparedHeap} (data : Data record prepared preparedHeap)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {action : EqualityNormalize.Path} {before after : Checked width} {memo saved : Memo} {result : Node} {memos final : Memos}
    {actual : Target prepared (SourceEqualityClassTarget.operandPaths record.paths action) before memo result after saved}
    (reads : TargetReads formulas solver actual memos final) (ready : ClassReady before)
    (captured : Keeps preparedHeap before.native.machine.heap) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (merged : MergeStored memo) (current : Current before) :
    MergeStored saved ∧ Current after ∧ ∃ depth, Cap Plain depth result := by
  have proper : ∀ path ∈ SourceEqualityClassTarget.operandPaths record.paths action,
      ∃ natural, natural ∈ record.paths ∧ natural ≠ [] ∧ path = natural.map Int.ofNat := by
    intro path member
    have nonroot := SourceEqualityClassTarget.operandPaths_nonroot record coherent active action path member
    obtain ⟨natural,selected,rfl⟩ := List.mem_map.mp member
    exact ⟨natural,(List.mem_filter.mp selected).1,by intro empty; subst natural; exact nonroot rfl,rfl⟩
  cases reads with
  | nil => exact ⟨merged,current,0,.plain 0 .empty⟩
  | cons reads =>
    obtain ⟨_,_,_,mergedAfter,currentAfter,_,_,bounded⟩ :=
      fold_cap data reads ready captured physicalStored merged current proper
    exact ⟨mergedAfter,currentAfter,bounded⟩

/-- The actual force installs a miss cap or reuses the same earlier slot value's cap. -/
theorem force_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {originals prepared : List Node}
    {requiredFuel requiredReadFuel : Nat} {selected : EqualityNormalize.Constraints} {scanHeap preparedHeap receiptBase : Heap}
    {action : EqualityNormalize.Path} {before after : State width} {value : Node} {memos final : Memos}
    (required : SourceEqualityRequiredExecution.requireAll requiredFuel requiredReadFuel
      (SourceEqualitySelectedRequired.paths selected) originals scanHeap = .done prepared preparedHeap)
    (semantic : SemanticReady scanHeap) (normal : SourceCurrentRequiredUnionNormal.UnionNormal scanHeap)
    (costs : CostHeap scanHeap) (available : Values scanHeap originals) (guards : Guards scanHeap)
    (primary : ∀ paths ∈ selected, ClassTrace source reaches originals paths scanHeap false scanHeap)
    (chosen : record.paths ∈ selected) (coherent : SourceEqualityClassOrder.Coherent record)
    (active : EqualityNormalize.Nontrivial record.paths)
    (receipt : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record prepared receiptBase action
      before value after memos final)
    (ready : Ready formulas solver inventory record prepared preparedHeap before) (stored : Stored before) :
    Stored after ∧ ∃ depth, Cap Plain depth value := by
  let data : Data record prepared preparedHeap :=
    ⟨requiredFuel,requiredReadFuel,selected,originals,scanHeap,required,semantic,normal,costs,available,guards,primary,chosen⟩
  cases receipt.reads with
  | hit present => exact ⟨stored,stored.slots action value present⟩
  | miss absent reads =>
    have produced := target_cap data coherent active reads ready.checked ready.captured ready.stored stored.merge stored.current
    exact ⟨store_stored before action value _ _ stored produced.2.1 produced.1 produced.2.2,produced.2.2⟩
end Source
end MicroCFTA.SourceCurrentRequiredSharedTargetCap
