import MicroCFTA.SourceCurrentRequiredSharedTargetCap
import MicroCFTA.SourceCurrentRawCorridorProjectionCap
import MicroCFTA.SourceCurrentConstrainedCapMixedShared

/-!
# Target caps from the actual captured raw corridors

Each competing operand follows its captured raw endpoint corridor. A miss
stores the cap of its actual result. A hit retains its same-slot certificate.
-/
namespace MicroCFTA.SourceCurrentRawCorridorSharedTargetCap
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

local notation "Stored" => SourceCurrentRequiredSharedTargetCap.Stored
local notation "RawCorridor" => SourceCurrentRequiredRawCorridor.RawCorridor

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
private structure Data (record : SourceEqualityClassOrder.Record) (values : List Node) (base : Heap) where
  known : Values base values
  masks : ∀ index path, index :: path ∈ record.paths →
    ∀ value, SourceEqualityProjectionGraph.select values (Int.ofNat index) = some value →
      RawCorridor (path.map Int.ofNat) value

variable [DecidableEq Symbol]
private theorem operand_cap {record values base} (data : Data record values base)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {path : List Int} {before after : Checked width} {memo saved : Memo}
    {result : Node} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final)
    (proper : ∃ natural, natural ∈ record.paths ∧ natural ≠ [] ∧ path = natural.map Int.ofNat)
    (ready : ClassReady before) (captured : Keeps base before.native.machine.heap)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (merged : MergeStored memo) (current : Current before) :
    MergeStored saved ∧ Current after ∧ ∃ depth, Cap Plain depth result := by
  obtain ⟨natural,member,nonempty,rfl⟩ := proper
  cases natural with
  | nil => exact False.elim (nonempty rfl)
  | cons index path =>
    obtain ⟨projected,middle,currentMemos,projection,mergedReceipt⟩ := receipt.actual
    obtain ⟨depth,bounded⟩ := SourceCurrentRawCorridorProjectionCap.forest projection.graph
      ready.semantic ready.costs (fun value member => captured.available value (data.known value member))
      current.1.guards (data.masks index path member)
    have projectedGuards := SourceCurrentConstrainedCapProjectionGuard.forest Plain projection.graph
      ready.semantic ready.costs (fun value member => captured.available value (data.known value member)) current.1.guards
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

private theorem fold_cap {record values base} (data : Data record values base)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {seed : List Int} {paths : List (List Int)} {before after : Checked width} {memo saved : Memo}
    {result : Node} {memos final : Memos} {actual : Fold values seed paths before memo result after saved}
    (reads : FoldReads formulas solver actual memos final) :
    ClassReady before → Keeps base before.native.machine.heap → PhysicalStored before.native.machine.heap memo →
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
      ih data receipt.ready (captured.trans receipt.effects.keeps) receipt.stored own.1 own.2.1 (by
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

private theorem target_cap {record values base} (data : Data record values base)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {paths : List (List Int)} {before after : Checked width} {memo saved : Memo} {result : Node} {memos final : Memos}
    {actual : Target values paths before memo result after saved}
    (reads : TargetReads formulas solver actual memos final) (ready : ClassReady before)
    (captured : Keeps base before.native.machine.heap) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (merged : MergeStored memo) (current : Current before)
    (proper : ∀ path ∈ paths, ∃ natural, natural ∈ record.paths ∧ natural ≠ [] ∧ path = natural.map Int.ofNat) :
    MergeStored saved ∧ Current after ∧ ∃ depth, Cap Plain depth result := by
  cases reads with
  | nil => exact ⟨merged,current,0,.plain 0 .empty⟩
  | cons reads =>
    obtain ⟨_,_,_,mergedAfter,currentAfter,_,_,bounded⟩ :=
      fold_cap data reads ready captured physicalStored merged current proper
    exact ⟨mergedAfter,currentAfter,bounded⟩

/-- The actual force derives finite target slots from its own captured raw corridors. -/
theorem force_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List Node}
    {base receiptBase : Heap} {action : EqualityNormalize.Path} {before after : State width}
    {value : Node} {memos final : Memos}
    (known : Values base values)
    (masks : ∀ index path, index :: path ∈ record.paths →
      ∀ value, SourceEqualityProjectionGraph.select values (Int.ofNat index) = some value →
        RawCorridor (path.map Int.ofNat) value)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (receipt : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record values receiptBase action
      before value after memos final)
    (ready : Ready formulas solver inventory record values base before) (stored : Stored before) :
    Stored after ∧ ∃ depth, Cap Plain depth value := by
  let data : Data record values base := ⟨known,masks⟩
  have proper : ∀ path ∈ SourceEqualityClassTarget.operandPaths record.paths action,
      ∃ natural, natural ∈ record.paths ∧ natural ≠ [] ∧ path = natural.map Int.ofNat := by
    intro path member
    have nonroot := SourceEqualityClassTarget.operandPaths_nonroot record coherent active action path member
    obtain ⟨natural,selected,rfl⟩ := List.mem_map.mp member
    exact ⟨natural,(List.mem_filter.mp selected).1,by intro empty; subst natural; exact nonroot rfl,rfl⟩
  cases receipt.reads with
  | hit present => exact ⟨stored,stored.slots action value present⟩
  | miss absent reads =>
    have produced := target_cap data reads ready.checked ready.captured ready.stored stored.merge stored.current proper
    exact ⟨store_stored before action value _ _ stored produced.2.1 produced.1 produced.2.2,produced.2.2⟩
end Source
end MicroCFTA.SourceCurrentRawCorridorSharedTargetCap
