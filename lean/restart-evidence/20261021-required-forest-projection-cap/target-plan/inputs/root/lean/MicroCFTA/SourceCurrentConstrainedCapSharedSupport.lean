import MicroCFTA.SourceCurrentConstrainedCapSupportedProjection
import MicroCFTA.SourceCurrentHereditaryTargetQuery
import MicroCFTA.SourceCurrentHereditaryMergeStore
import MicroCFTA.SourceCurrentAllocatedSharedTargetLeaf

/-!
# Hereditary targets from captured original path support

Each operand uses its actual projection and Merge return. Each native fold
query uses two hereditary operands at the actual recursive tail return.
Slots retain conditional laws for their original captured forest. The
universal native store permits a later query to use a new source heap.
These theorems verify supplied reads. They do not establish edit-wide store
retention or completion of a mixed constrained recursive reduction.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSharedSupport
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityAnnotationLanguage SourceCurrentConstrainedCapPaths
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "ClassReady" => SourceCurrentConjunctionClassScan.Ready
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "NativeStored" => SourceCurrentHereditaryNativeUniversalStore.Stored Plain
local notation "MergeStored" => SourceCurrentHereditaryMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))

section TargetProducers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The operand retains its exact native cells while deriving its actual local annotation. -/
theorem operand_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {path : List Int}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final)
    (ready : ClassReady before) (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (merged : MergeStored memo)
    (native : NativeStored before) (supported : ForestSupported Plain path values) :
    MergeStored saved ∧ NativeStored after ∧ Annotated Plain result := by
  obtain ⟨projected, middle, current, projection, mergedReceipt⟩ := receipt.actual
  have localProjection := SourceCurrentConstrainedCapSupportedProjection.forest Plain projection.graph
    ready.semantic available closed native.constructors supported
  cases mergedReceipt.actual with
  | done call =>
      have produced := SourceCurrentHereditaryMergeStore.call Plain SourceCurrentUnconstrainedGuardClosure.top_plain
        call.graph projection.ready.semantic projection.ready.costs (physicalStored.grows projection.effects.keeps)
        merged localProjection.1 projection.available localProjection.2
      refine ⟨produced.2.2.1, ?_, produced.2.2.2.2.2 localProjection.2⟩
      refine ⟨produced.2.2.2.1, ?_⟩
      intro source
      exact ⟨by simpa only [receipt.nodes] using (native.native source).nodes,
        by simpa only [receipt.edges] using (native.native source).edges⟩

/-- The rotated right fold derives its own annotated query operands in source order. -/
theorem fold
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Fold values seed paths before memo result after saved} (reads : FoldReads formulas solver actual memos final) :
    ClassReady before → Values before.native.machine.heap values → ClosedValues values → PhysicalStored before.native.machine.heap memo →
      MergeStored memo → NativeStored before → (∀ path ∈ seed :: paths, ForestSupported Plain path values) →
      ClassReady after ∧ Effects (physical before) (physical after) ∧ PhysicalStored after.native.machine.heap saved ∧
      MergeStored saved ∧ NativeStored after ∧ Available after.native.machine.heap result ∧ result.free = [] ∧ Annotated Plain result := by
  induction reads with
  | nil receipt =>
      intro ready available closed physicalStored merged native supported
      have own := operand_receipt receipt ready available closed physicalStored merged native (supported _ List.mem_cons_self)
      exact ⟨receipt.ready, receipt.effects, receipt.stored, own.1, own.2.1, receipt.available, receipt.closed, own.2.2⟩
  | cons receipt remaining query ih =>
      intro ready available closed physicalStored merged native supported
      have head := operand_receipt receipt ready available closed physicalStored merged native (supported _ (by simp))
      obtain ⟨tailReady, tailEffects, tailPhysical, tailMerged, tailNative, tailAvailable, tailClosed, tailAnnotated⟩ :=
        ih receipt.ready receipt.originals closed receipt.stored head.1 head.2.1 (tail_all supported)
      have produced := SourceCurrentHereditaryTargetQuery.step query.actual tailReady.good tailReady.semantic
        (tailEffects.keeps.available _ receipt.available) tailAvailable receipt.closed tailClosed tailNative head.2.2 tailAnnotated
      exact ⟨query.ready, receipt.effects.trans (tailEffects.trans query.effects), tailPhysical.grows query.effects.keeps,
        tailMerged, produced.1, query.available, query.closed, produced.2⟩

/-- Every literal operand mask yields the same supplied whole target's hereditary result. -/
theorem target_reads
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Target values paths before memo result after saved} (reads : TargetReads formulas solver actual memos final)
    (ready : ClassReady before) (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (merged : MergeStored memo)
    (native : NativeStored before) (supported : ∀ path ∈ paths, ForestSupported Plain path values) :
    MergeStored saved ∧ NativeStored after ∧ Annotated Plain result := by
  cases reads with
  | nil => exact ⟨merged, native, .empty⟩
  | cons reads =>
      obtain ⟨_, _, _, mergedAfter, nativeAfter, _, _, annotated⟩ := fold reads ready available closed physicalStored merged native supported
      exact ⟨mergedAfter, nativeAfter, annotated⟩

end TargetProducers

open SourceCurrentAllocatedSharedTargetState (State initial advance store)
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "ForceReceipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt

/-- Slot laws retain the exact captured forest and the literal other-path operand order. -/
def Certificate (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (path : EqualityNormalize.Path) (value : Value Symbol Guard) : Prop :=
  (∀ operand ∈ SourceEqualityClassTarget.operandPaths record.paths path, ForestSupported Plain operand values) → Annotated Plain value

/-- These independent causal stores permit unrelated constrained heap records. -/
structure Stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (state : State width) : Prop where
  /-- Every native source heap has the conditional laws of the actual returned cells. -/
  native : NativeStored state.checked
  /-- Each Merge entry retains the law of its own captured original. -/
  merge : MergeStored state.memo
  /-- A target slot retains the law of its exact captured forest and path. -/
  slots : ∀ path value, state.targets path = some value → Certificate record values path value

/-- Fresh class slots retain both warm tables and impose no prior slot obligation. -/
theorem initial_stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (checked : Checked width) (memo : Memo) (native : NativeStored checked) (merged : MergeStored memo) :
    Stored record values (initial checked memo) :=
  ⟨native, merged, by intro path value absent; cases absent⟩

/-- Checked advancement retains captured slot laws and the unchanged Merge table. -/
theorem advance_stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (state : State width) (checked : Checked width) (stored : Stored record values state) (native : NativeStored checked) :
    Stored record values (advance state checked) := ⟨native, stored.merge, stored.slots⟩

/-- Constructor-only advancement needs its actual causal Mu store at the returned heap. -/
theorem advance_heap_stored {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    (state : State width) (heap : InternedConstructorTemplates.State Symbol Guard) (stored : Stored record values state)
    (constructors : SourceCurrentHereditaryConstruction.MuStored Plain heap) :
    Stored record values (advance state (SourceCurrentAllocatedQueryMemo.advancePhysical state.checked ⟨heap, state.checked.operations⟩)) :=
  advance_stored record values state _ stored
    (SourceCurrentHereditaryNativeUniversalStore.advance Plain state.checked _ stored.native constructors)

/-- A miss stores only a law derived for that same actual target result. -/
theorem store_stored (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (state : State width) (path : EqualityNormalize.Path) (value : Value Symbol Guard) (checked : Checked width) (memo : Memo)
    (stored : Stored record values state) (native : NativeStored checked) (merged : MergeStored memo)
    (certificate : Certificate record values path value) : Stored record values (store state path value checked memo) := by
  refine ⟨native, merged, ?_⟩
  intro other result found
  by_cases same : other = path
  · subst other
    have sameResult : value = result := Option.some.inj (by simpa only [store, put, ite_true] using found)
    exact sameResult ▸ certificate
  · exact stored.slots other result (by simpa only [store, put, same, ite_false] using found)

section Producers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory next : Inventory}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : State width} {input value result : Value Symbol Guard} {memos final : Memos}

/-- A first force derives its target law before store; a warm force reads that causal law. -/
theorem force_receipt
    {receiptBase : InternedConstructorTemplates.State Symbol Guard}
    (receipt : ForceReceipt formulas solver next record values receiptBase path before value after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (closed : ClosedValues values) (stored : Stored record values before)
    (supported : ∀ operand ∈ SourceEqualityClassTarget.operandPaths record.paths path, ForestSupported Plain operand values) :
    Stored record values after ∧ Annotated Plain value := by
  cases receipt.reads with
  | hit present => exact ⟨stored, stored.slots path value present supported⟩
  | miss absent reads =>
      have available : Values before.checked.native.machine.heap values := fun value member => ready.captured.available value (known value member)
      have own := target_reads reads ready.checked available closed ready.stored stored.merge stored.native supported
      have certificate : Certificate record values path value := by
        intro otherMasks
        exact (target_reads reads ready.checked available closed ready.stored stored.merge stored.native otherMasks).2.2
      exact ⟨store_stored record values before path value _ _ stored own.2.1 own.1 certificate, own.2.2⟩

/-- The same actual leaf intersects two hereditary inputs and retains every causal table. -/
theorem leaf_receipt
    (receipt : LeafReceipt formulas solver next record values base path input before result after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (closed : ClosedValues values) (stored : Stored record values before)
    (supported : ∀ operand ∈ SourceEqualityClassTarget.operandPaths record.paths path, ForestSupported Plain operand values)
    (available : Available before.checked.native.machine.heap input) (inputClosed : input.free = []) (annotated : Annotated Plain input) :
    Stored record values after ∧ Annotated Plain result := by
  cases receipt.reads with
  | apply first query =>
      have forced := force_receipt first ready known closed stored supported
      have produced := SourceCurrentHereditaryTargetQuery.step query.actual first.ready.checked.good first.ready.checked.semantic
        first.available (first.effects.keeps.available input available) first.closed inputClosed forced.1.native forced.2 annotated
      exact ⟨advance_stored record values _ _ forced.1 produced.1, produced.2⟩

end Producers
end MicroCFTA.SourceCurrentConstrainedCapSharedSupport
