import MicroCFTA.SourceCurrentRawCorridorSharedTargetCap
import MicroCFTA.SourceCurrentRawCorridorPositiveValue
import MicroCFTA.SourceCurrentNativePositiveSupportAdvance
import MicroCFTA.SourceCurrentNativeCurrentPositivePositions
import MicroCFTA.SourceCurrentMergePositivePosition
import MicroCFTA.SourceCurrentParentPublicationHistory

/-!
# Positive positions in actual class target slots

Each operand retains its same captured forest index and positive suffix.
Actual native joins choose one of their two input origins. A miss stores
that law for its exact result. A hit retains the same earlier slot law.
-/
namespace MicroCFTA.SourceCurrentRawCorridorSharedTargetPositivePositions
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State store Ready)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentNativeMuPublication (History)
open SourceEqualityProjectionGraph (select)
open SourceEqualityRequiredCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "MergeSupport" => SourceCurrentMergePositivePosition.Support
local notation "NativeSupport" => SourceCurrentNativeRequestPositivePositions.Support
local notation "CapStored" => SourceCurrentRequiredSharedTargetCap.Stored
local notation "RawCorridor" => SourceCurrentRequiredRawCorridor.RawCorridor
local notation "ClassReady" => SourceCurrentConjunctionClassScan.Ready
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "physical" => SourceCurrentAllocatedNativeEffects.physical
variable {width : Nat}

private def Back (values : List Node) (paths : List (List Int)) (value : Node) : Prop :=
  ∀ q, PositiveAt value q → ∃ index path original,
    ((index :: path).map Int.ofNat) ∈ paths ∧
    values[index]? = some original ∧ PositiveAt original (path ++ q)

private theorem back_mono {values first last value} (back : Back values first value)
    (included : ∀ path ∈ first, path ∈ last) : Back values last value := by
  intro q positive
  obtain ⟨index,path,original,member,found,origin⟩ := back q positive
  exact ⟨index,path,original,included _ member,found,origin⟩

section Actual
variable [DecidableEq (EdgeKey Symbol Guard)]

private structure Data (record : SourceEqualityClassOrder.Record) (values : List Node) (base : Heap) where
  known : Values base values
  masks : ∀ index path, index :: path ∈ record.paths → ∀ value,
    select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value

private theorem forest_back {index : Nat} {path q : List Nat} {values : List Node}
    {before after : Heap} {result : Node}
    (actual : SourceEqualityProjectionGraph.Forest ((index :: path).map Int.ofNat) values before result after)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Values before values)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain before)
    (corridor : ∀ original, select values (Int.ofNat index) = some original →
      RawCorridor (path.map Int.ofNat) original) (positive : PositiveAt result q) :
    ∃ original, values[index]? = some original ∧ PositiveAt original (path ++ q) := by
  cases actual with
  | missing absent => cases positive
  | selected found project =>
    rename_i value
    have natural : values[index]? = some value := by
      simpa only [select,Int.ofNat_eq_natCast,
        ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] using found
    exact ⟨_,natural,SourceCurrentRawCorridorPositiveValue.project project semantic costs
      (available _ (SourceEqualityProjectionGraph.select_member found)) guards (corridor _ found) positive⟩

variable [symbolEq : DecidableEq Symbol]

private theorem operand_law {record values base} (data : Data record values base)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {path : List Int} {before after : Checked width} {memo saved : Memo}
    {result : Node} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo result after saved memos final)
    (proper : ∃ natural, natural ∈ record.paths ∧ natural ≠ [] ∧ path = natural.map Int.ofNat)
    (ready : ClassReady before) (captured : Keeps base before.native.machine.heap)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (merged : MergeStored memo) (current : Current before)
    (supported : NativeSupport before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap) (positiveMemo : MergeSupport memo) :
    MergeStored saved ∧ Current after ∧ NativeSupport after.native.machine.heap after.native ∧
      Nonempty (History empty after.native.machine.heap) ∧ MergeSupport saved ∧
      (∃ depth, Cap Plain depth result) ∧ Back values [path] result := by
  have sameSymbol : symbolEq = @instDecidableEqProd SourceGuards.Name FullSyntax.Formula
      instDecidableEqString FormulaExecutable.formulaDecidableEq := Subsingleton.elim _ _
  cases sameSymbol
  letI : DecidableEq Symbol := @instDecidableEqProd SourceGuards.Name FullSyntax.Formula
    instDecidableEqString FormulaExecutable.formulaDecidableEq
  obtain ⟨natural,member,nonempty,rfl⟩ := proper
  cases natural with
  | nil => exact False.elim (nonempty rfl)
  | cons index path =>
    obtain ⟨projected,middle,currentMemos,projection,mergedReceipt⟩ := receipt.actual
    have available : Values before.native.machine.heap values :=
      fun value member => captured.available value (data.known value member)
    obtain ⟨depth,bounded⟩ := SourceCurrentRawCorridorProjectionCap.forest projection.graph
      ready.semantic ready.costs available current.1.guards (data.masks index path member)
    have projectedGuards := SourceCurrentConstrainedCapProjectionGuard.forest Plain projection.graph
      ready.semantic ready.costs available current.1.guards
    have projectedCurrent := SourceCurrentConstrainedCapCurrentNative.advance Plain before middle current
      projection.ready.good projection.ready.semantic.ready.semantic projectedGuards
      projection.extension projection.nodes projection.edges
    have projectedSupport := SourceCurrentNativePositiveSupportAdvance.advance before middle current supported
      projection.ready.good projection.extension projection.nodes projection.edges
    have retained := SourceCurrentConstrainedCapMergeJointEffects.merge Plain formulas solver inventory
      mergedReceipt.actual projection.ready projection.admitted (physicalStored.grows projection.effects.keeps)
      projection.available projectedCurrent
    have finalSupport := SourceCurrentNativePositiveSupportAdvance.advance middle after projectedCurrent
      projectedSupport mergedReceipt.ready.good mergedReceipt.extension mergedReceipt.nodes mergedReceipt.edges
    obtain ⟨interval⟩ := SourceCurrentParentPublicationHistory.operand receipt ready available physicalStored
    have finalHistory : Nonempty (History empty after.native.machine.heap) := ⟨.trans causal interval⟩
    cases mergedReceipt.actual with
    | done call =>
      have caps := SourceCurrentConstrainedCapMemoMerge.retained Plain SourceCurrentUnconstrainedGuardClosure.top_plain
        call.graph projection.ready.semantic projection.ready.costs (physicalStored.grows projection.effects.keeps)
        merged projection.available depth bounded
      have positions := SourceCurrentMergePositivePosition.call SourceCurrentAllocatedMerge.literalClear
        SourceEqualityConstraintConstructors.top rfl call.graph projection.ready.semantic projection.ready.costs
        (physicalStored.grows projection.effects.keeps) positiveMemo projection.available
      refine ⟨caps.2.2.1,retained.1,finalSupport,finalHistory,positions.2.2.1,
        ⟨depth,caps.2.2.2.2⟩,?_⟩
      intro q positive
      have projectedPositive := positions.2.2.2.2 q positive
      obtain ⟨original,found,origin⟩ := forest_back projection.graph ready.semantic ready.costs available
        current.1.guards (data.masks index path member) projectedPositive
      exact ⟨index,path,original,List.mem_cons_self,found,origin⟩

private theorem fold_law {record values base} (data : Data record values base)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {seed : List Int} {paths : List (List Int)} {before after : Checked width} {memo saved : Memo}
    {result : Node} {memos final : Memos} {actual : Fold values seed paths before memo result after saved}
    (reads : FoldReads formulas solver actual memos final) :
    ClassReady before → Keeps base before.native.machine.heap → PhysicalStored before.native.machine.heap memo →
    MergeStored memo → Current before → NativeSupport before.native.machine.heap before.native →
    History empty before.native.machine.heap → MergeSupport memo →
    (∀ path ∈ seed :: paths, ∃ natural, natural ∈ record.paths ∧ natural ≠ [] ∧ path = natural.map Int.ofNat) →
    ClassReady after ∧ Effects (physical before) (physical after) ∧ PhysicalStored after.native.machine.heap saved ∧
      MergeStored saved ∧ Current after ∧ NativeSupport after.native.machine.heap after.native ∧
      Nonempty (History empty after.native.machine.heap) ∧ MergeSupport saved ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      (∃ depth, Cap Plain depth result) ∧ Back values (seed :: paths) result := by
  induction reads with
  | nil receipt =>
    intro ready captured physicalStored merged current supported causal positiveMemo proper
    obtain ⟨nextMerged,nextCurrent,nextSupport,nextHistory,nextPositive,bounded,back⟩ :=
      operand_law data receipt (proper _ List.mem_cons_self) ready captured physicalStored
        merged current supported causal positiveMemo
    exact ⟨receipt.ready,receipt.effects,receipt.stored,nextMerged,nextCurrent,nextSupport,
      nextHistory,nextPositive,receipt.available,receipt.closed,bounded,back⟩
  | cons receipt remaining query ih =>
    intro ready captured physicalStored merged current supported causal positiveMemo proper
    obtain ⟨headMerged,headCurrent,headSupport,⟨headHistory⟩,headPositive,headBounded,headBack⟩ :=
      operand_law data receipt (proper _ (by simp)) ready captured physicalStored
        merged current supported causal positiveMemo
    obtain ⟨tailReady,tailEffects,tailPhysical,tailMerged,tailCurrent,tailSupport,⟨tailHistory⟩,
      tailPositive,tailAvailable,tailClosed,tailBounded,tailBack⟩ :=
      ih data receipt.ready (captured.trans receipt.effects.keeps) receipt.stored headMerged headCurrent
        headSupport headHistory headPositive (by
          intro path member
          rcases List.mem_cons.mp member with rfl | later
          · exact proper _ List.mem_cons_self
          · exact proper _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ later)))
    obtain ⟨headDepth,headCap⟩ := headBounded
    obtain ⟨tailDepth,tailCap⟩ := tailBounded
    obtain ⟨nextCurrent,nextSupport,nextHistory,nextCap,back⟩ :=
      SourceCurrentNativeCurrentPositivePositions.step (max headDepth tailDepth) formulas solver query.actual
        tailReady.good tailReady.semantic tailCurrent tailSupport tailHistory
        (tailEffects.keeps.available _ receipt.available) tailAvailable receipt.closed tailClosed
        (headCap.mono (Nat.le_max_left _ _)) (tailCap.mono (Nat.le_max_right _ _))
    refine ⟨query.ready,receipt.effects.trans (tailEffects.trans query.effects),
      tailPhysical.grows query.effects.keeps,tailMerged,nextCurrent,nextSupport,nextHistory,
      tailPositive,query.available,query.closed,⟨_,nextCap⟩,?_⟩
    intro q positive
    rcases back q positive with head | tail
    · apply back_mono headBack (by
        intro path member
        rcases List.mem_singleton.mp member with rfl
        exact List.mem_cons_of_mem _ List.mem_cons_self) q head
    · apply back_mono tailBack (by
        intro path member
        rcases List.mem_cons.mp member with rfl | later
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ later)) q tail

private theorem target_law {record values base} (data : Data record values base)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {paths : List (List Int)} {before after : Checked width} {memo saved : Memo} {result : Node} {memos final : Memos}
    {actual : Target values paths before memo result after saved}
    (reads : TargetReads formulas solver actual memos final) (ready : ClassReady before)
    (captured : Keeps base before.native.machine.heap) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (merged : MergeStored memo) (current : Current before)
    (supported : NativeSupport before.native.machine.heap before.native)
    (causal : History empty before.native.machine.heap) (positiveMemo : MergeSupport memo)
    (proper : ∀ path ∈ paths, ∃ natural, natural ∈ record.paths ∧ natural ≠ [] ∧ path = natural.map Int.ofNat) :
    MergeStored saved ∧ Current after ∧ NativeSupport after.native.machine.heap after.native ∧
      Nonempty (History empty after.native.machine.heap) ∧ MergeSupport saved ∧
      (∃ depth, Cap Plain depth result) ∧ Back values paths result := by
  cases reads with
  | nil => exact ⟨merged,current,supported,⟨causal⟩,positiveMemo,⟨0,.plain 0 .empty⟩,by intro q positive; cases positive⟩
  | cons reads =>
    obtain ⟨_,_,_,nextMerged,nextCurrent,nextSupport,nextHistory,nextPositive,_,_,bounded,back⟩ :=
      fold_law data reads ready captured physicalStored merged current supported causal positiveMemo proper
    exact ⟨nextMerged,nextCurrent,nextSupport,nextHistory,nextPositive,bounded,back⟩

/-- The same completed force retains exact competing-path ancestry for every present target slot. -/
theorem force_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List Node}
    {base receiptBase : Heap} {action : EqualityNormalize.Path} {before after : State width}
    {value : Node} {memos final : Memos}
    (known : Values base values)
    (masks : ∀ index path, index :: path ∈ record.paths → ∀ original,
      select values (Int.ofNat index) = some original → RawCorridor (path.map Int.ofNat) original)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (receipt : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record values
      receiptBase action before value after memos final)
    (ready : Ready formulas solver inventory record values base before) (stored : CapStored before)
    (supported : NativeSupport before.checked.native.machine.heap before.checked.native)
    (causal : History empty before.checked.native.machine.heap) (positiveMemo : MergeSupport before.memo)
    (slots : ∀ a t, before.targets a = some t → ∀ q, PositiveAt t q → ∃ index path original,
      ((index :: path).map Int.ofNat) ∈ SourceEqualityClassTarget.operandPaths record.paths a ∧
      values[index]? = some original ∧ PositiveAt original (path ++ q)) :
    CapStored after ∧ NativeSupport after.checked.native.machine.heap after.checked.native ∧
      Nonempty (History empty after.checked.native.machine.heap) ∧ MergeSupport after.memo ∧
      (∀ a t, after.targets a = some t → ∀ q, PositiveAt t q → ∃ index path original,
        ((index :: path).map Int.ofNat) ∈ SourceEqualityClassTarget.operandPaths record.paths a ∧
        values[index]? = some original ∧ PositiveAt original (path ++ q)) := by
  have caps := SourceCurrentRawCorridorSharedTargetCap.force_receipt known masks coherent active receipt ready stored
  let data : Data record values base := ⟨known,masks⟩
  have proper : ∀ path ∈ SourceEqualityClassTarget.operandPaths record.paths action,
      ∃ natural, natural ∈ record.paths ∧ natural ≠ [] ∧ path = natural.map Int.ofNat := by
    intro path member
    have nonroot := SourceEqualityClassTarget.operandPaths_nonroot record coherent active action path member
    obtain ⟨natural,selected,rfl⟩ := List.mem_map.mp member
    exact ⟨natural,(List.mem_filter.mp selected).1,by intro empty; subst natural; exact nonroot rfl,rfl⟩
  cases receipt.reads with
  | hit present => exact ⟨caps.1,supported,⟨causal⟩,positiveMemo,slots⟩
  | miss absent reads =>
    obtain ⟨_nextMerged,_nextCurrent,nextSupport,nextHistory,nextPositive,_bounded,back⟩ :=
      target_law data reads ready.checked ready.captured ready.stored stored.merge stored.current
        supported causal positiveMemo proper
    refine ⟨caps.1,nextSupport,nextHistory,nextPositive,?_⟩
    intro a t present q positive
    by_cases same : a = action
    · subst a
      have identity : value = t := Option.some.inj (by simpa only [store,put,ite_true] using present)
      subst t
      exact back q positive
    · have original : before.targets a = some t := by simpa only [store,put,same,ite_false] using present
      exact slots a t original q positive

end Actual
end MicroCFTA.SourceCurrentRawCorridorSharedTargetPositivePositions
