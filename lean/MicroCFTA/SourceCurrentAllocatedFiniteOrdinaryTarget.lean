import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryProjection
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMerge
import MicroCFTA.SourceCurrentAllocatedTargetComplete

/-!
# Finite ordinary structure through current checked targets

Projection and memo-aware merging derive each operand's domain. The actual
head operand precedes the tail and its checked native request. Concrete
current receipts supply intermediate readiness. Structural verification
uses the same requests and returned states. Initial forest structure derives
all selected path domains.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionGraph SourceEqualityProjectionPathDomain
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children

private theorem node_closed {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (path : List Int) (state : State Symbol Guard) (semantic : SemanticReady state)
    (value : Value Symbol Guard) (available : Available state value) (domain : DNode value) : NodeClosed path value := by
  induction path generalizing value with
  | nil => simpa only [NodeClosed] using
      SourceCurrentAllocatedFiniteOrdinaryFinite.closed state semantic.ready.semantic.1.normal.facts.coherent value available domain
  | cons index path ih =>
      cases domain with
      | empty => simp only [NodeClosed]
      | ordinary rows =>
          rw [NodeClosed]
          intro edge member child found
          have selected := select_member found
          exact ih child (available.children child (List.mem_flatMap.mpr ⟨edge, member, selected⟩))
            ((rows.member edge member).member child selected)

/-- The complete available domain forest supplies every finite selected path domain. -/
theorem forest_closed {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (semantic : SemanticReady state) (values : List (Value Symbol Guard))
    (available : Values state values) (domain : DChildren values) (path : List Int) : ForestClosed path values := by
  cases path with
  | nil =>
      intro value member
      exact SourceCurrentAllocatedFiniteOrdinaryFinite.closed state
        semantic.ready.semantic.1.normal.facts.coherent value (available value member) (domain.member value member)
  | cons index path =>
      intro value found
      exact node_closed path state semantic value (available value (select_member found)) (domain.member value (select_member found))

open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "GlobalValid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem operand_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {path : List Int}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values) (domain : DChildren values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (mergeStored : MergeStored memo)
    (nativeStored : NativeStored before.native) : MergeStored saved ∧ NativeStored after.native ∧ DNode result := by
  obtain ⟨projected, middle, current, projection, merged⟩ := receipt.actual
  have projectedDomain := SourceCurrentAllocatedFiniteOrdinaryProjection.forest projection.graph ready.semantic available domain
  have middleNative : NativeStored middle.native := by
    rw [projection.advanced]
    exact SourceCurrentAllocatedFiniteOrdinaryStored.advance_stored _ _ nativeStored
  have checked := SourceCurrentAllocatedFiniteOrdinaryMerge.merge merged.actual projection.ready
    (physicalStored.grows projection.effects.keeps) mergeStored middleNative projection.available projectedDomain.2.2.2
  exact ⟨checked.2.2.1, checked.2.2.2.1, checked.2.2.2.2.2.1⟩

private theorem fold_reads
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Fold values seed paths before memo result after saved} (reads : FoldReads formulas solver actual memos final) :
    Ready before → Values before.native.machine.heap values → DChildren values → PhysicalStored before.native.machine.heap memo →
      MergeStored memo → NativeStored before.native →
      Ready after ∧ Effects (physical before) (physical after) ∧ PhysicalStored after.native.machine.heap saved ∧
      MergeStored saved ∧ NativeStored after.native ∧ Available after.native.machine.heap result ∧ DNode result := by
  induction reads with
  | nil receipt =>
      intro ready available domain physicalStored mergeStored nativeStored
      have own := operand_receipt receipt ready available domain physicalStored mergeStored nativeStored
      exact ⟨receipt.ready, receipt.effects, receipt.stored, own.1, own.2.1, receipt.available, own.2.2⟩
  | cons receipt remaining query ih =>
      intro ready available domain physicalStored mergeStored nativeStored
      have head := operand_receipt receipt ready available domain physicalStored mergeStored nativeStored
      have tail := ih receipt.ready receipt.originals domain receipt.stored head.1 head.2.1
      cases query.actual with
      | run trace =>
          have checked := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace
            tail.1.good tail.1.semantic tail.2.2.2.2.1 ⟨rfl, head.2.2, tail.2.2.2.2.2.2⟩
          exact ⟨query.ready, receipt.effects.trans (tail.2.1.trans query.effects),
            tail.2.2.1.grows query.effects.keeps, tail.2.2.2.1, checked.1, query.available, checked.2.1⟩

/-- Every actual operand derives its full receipt and both structural cache invariants. -/
theorem operand
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {values : List (Value Symbol Guard)} {path : List Int}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Operand path values before memo result after saved) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : DChildren values) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (mergeStored : MergeStored memo) (nativeStored : NativeStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : GlobalValid before.native.machine.heap memos) :
    ∃ final, SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final ∧
      MergeStored saved ∧ NativeStored after.native ∧ DNode result := by
  obtain ⟨final, receipt⟩ := actual.verified formulas solver inventory ready admitted available
    (forest_closed _ ready.semantic values available domain path) physicalStored covered memos valid
  exact ⟨final, receipt, operand_receipt receipt ready available domain physicalStored mergeStored nativeStored⟩

/-- Actual first-seeded folds retain domain results and their exact native and merge certificates. -/
theorem fold
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Fold values seed paths before memo result after saved) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : DChildren values) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (mergeStored : MergeStored memo) (nativeStored : NativeStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : FoldRanges values seed paths before memo) (memos : Memos) (valid : GlobalValid before.native.machine.heap memos) :
    ∃ next final, FoldReads formulas solver actual memos final ∧
      Receipt formulas solver next values (seed :: paths) before memo result after saved memos final ∧
      MergeStored saved ∧ NativeStored after.native ∧ DNode result := by
  obtain ⟨next, final, reads, receipt⟩ := SourceCurrentAllocatedTargetComplete.Fold.verified formulas solver inventory actual ready admitted available
    (fun path _ => forest_closed _ ready.semantic values available domain path) physicalStored covered ranges memos valid
  have checked := fold_reads reads ready available domain physicalStored mergeStored nativeStored
  exact ⟨next, final, reads, receipt, checked.2.2.2.1, checked.2.2.2.2.1, checked.2.2.2.2.2.2⟩

/-- Existing actual targets derive domain closure from initial captured forest and cache facts. -/
theorem target
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Target values paths before memo result after saved) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : DChildren values) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (mergeStored : MergeStored memo) (nativeStored : NativeStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values paths before memo) (memos : Memos) (valid : GlobalValid before.native.machine.heap memos) :
    ∃ next final, TargetReads formulas solver actual memos final ∧
      Receipt formulas solver next values paths before memo result after saved memos final ∧
      MergeStored saved ∧ NativeStored after.native ∧ DNode result := by
  cases actual with
  | nil =>
      obtain ⟨next, final, reads, receipt⟩ := SourceCurrentAllocatedTargetComplete.Target.verified formulas solver inventory Target.nil ready admitted available
        (fun path _ => forest_closed _ ready.semantic values available domain path) physicalStored covered ranges memos valid
      exact ⟨next, final, reads, receipt, mergeStored, nativeStored, .empty⟩
  | nonempty actual =>
      obtain ⟨next, final, reads, receipt, retained, native, resultDomain⟩ := fold formulas solver inventory actual
        ready admitted available domain physicalStored mergeStored nativeStored covered ranges memos valid
      exact ⟨next, final, .cons reads, receipt, retained, native, resultDomain⟩

/-- Initial invariants and reached range checks construct the actual target and its structural result. -/
theorem finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : DChildren values) (physicalStored : PhysicalStored before.native.machine.heap memo)
    (mergeStored : MergeStored memo) (nativeStored : NativeStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values paths before memo) (memos : Memos) (valid : GlobalValid before.native.machine.heap memos) :
    ∃ result after saved next final, ∃ actual : Target values paths before memo result after saved,
      TargetReads formulas solver actual memos final ∧
      Receipt formulas solver next values paths before memo result after saved memos final ∧
      MergeStored saved ∧ NativeStored after.native ∧ DNode result := by
  obtain ⟨result, after, saved, next, final, actual, reads, receipt⟩ := target_complete formulas solver inventory values paths
    before memo ready admitted available (fun path _ => forest_closed _ ready.semantic values available domain path)
    physicalStored covered ranges memos valid
  have structural : MergeStored saved ∧ NativeStored after.native ∧ DNode result := by
    cases reads with
    | nil => exact ⟨mergeStored, nativeStored, .empty⟩
    | cons remaining =>
        have checked := fold_reads remaining ready available domain physicalStored mergeStored nativeStored
        exact ⟨checked.2.2.2.1, checked.2.2.2.2.1, checked.2.2.2.2.2.2⟩
  exact ⟨result, after, saved, next, final, actual, reads, receipt, structural⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTarget
