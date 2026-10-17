import MicroCFTA.SourceCurrentConstrainedCapMemoMerge
import MicroCFTA.SourceCurrentConstrainedCapMergeJointEffects
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard
import MicroCFTA.SourceCurrentConstrainedCapSelectedProjection
import MicroCFTA.SourceCurrentAllocatedTargetComplete

/-!
# Finite-depth caps through actual selected target callers

Each operand projects the captured forest before its actual Merge call.
Selected closure permits unrelated open ordinary siblings. The fold uses
the maximum of its two actual operand depths at each checked intersection.
These proofs verify supplied target reads. The operand endpoint constructs
its own finite return from initial facts.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMixedTarget
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "Current" => SourceCurrentConstrainedCapCurrentNative.At Plain
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "physical" => SourceCurrentAllocatedNativeEffects.physical
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The first forest index selects a root. Each later index consumes one cap layer. -/
def operandDepth (depth : Nat) (path : List Int) : Nat := depth - (path.length - 1)

/-- Each actual fold query uses the larger bound of its head operand and recursive tail. -/
def foldDepth (depth : Nat) (seed : List Int) : List (List Int) → Nat
  | [] => operandDepth depth seed
  | path :: paths => max (operandDepth depth path) (foldDepth depth seed paths)

/-- An empty target is hereditary. A nonempty target uses its actual first seed. -/
def targetDepth (depth : Nat) : List (List Int) → Nat
  | [] => 0
  | seed :: paths => foldDepth depth seed paths

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))

/-- The same literal operand derives its output cap and retains the populated joint and Merge stores. -/
theorem operand_receipt (depth : Nat)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {path : List Int}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo result after saved memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values) (domain : Domain path values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (merged : MergeStored memo)
    (current : Current before) (bounded : ∀ value ∈ values, Cap Plain depth value) :
    MergeStored saved ∧ Current after ∧ Cap Plain (operandDepth depth path) result := by
  obtain ⟨projected, middle, currentMemos, projection, mergedReceipt⟩ := receipt.actual
  have localProjection := SourceCurrentConstrainedCapSelectedProjection.forest Plain depth projection.graph
    ready.semantic available domain
    (SourceCurrentConstrainedCapGuardNative.stored Plain before.native.machine.heap current.1.guards) bounded
  have projectedGuards := SourceCurrentConstrainedCapProjectionGuard.forest Plain projection.graph
    ready.semantic ready.costs available current.1.guards
  have projectedCurrent := SourceCurrentConstrainedCapCurrentNative.advance Plain before middle current projection.ready.good
    projection.ready.semantic.ready.semantic projectedGuards projection.extension projection.nodes projection.edges
  have retained := SourceCurrentConstrainedCapMergeJointEffects.Allocated.merge Plain formulas solver inventory
    mergedReceipt.actual projection.ready projection.admitted (physicalStored.grows projection.effects.keeps)
    projection.available projectedCurrent
  cases mergedReceipt.actual with
  | done call =>
      have produced := SourceCurrentConstrainedCapMemoMerge.call Plain SourceCurrentUnconstrainedGuardClosure.top_plain
        call.graph projection.ready.semantic projection.ready.costs (physicalStored.grows projection.effects.keeps)
        merged projection.available
      exact ⟨produced.2.2.1, retained.1, produced.2.2.2.2 _ localProjection.2⟩

/-- Initial selected domains construct a finite operand with the exact depth reduction and retained stores. -/
theorem operand_complete (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (path : List Int) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : Domain path values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (merged : MergeStored memo) (current : Current before) (bounded : ∀ value ∈ values, Cap Plain depth value) :
    ∃ result after saved final,
      Operand path values before memo result after saved ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
        before memo result after saved memos final ∧
      MergeStored saved ∧ Current after ∧ Cap Plain (operandDepth depth path) result := by
  obtain ⟨result, after, saved, final, actual, receipt⟩ := Operand.complete formulas solver inventory path values
    before memo ready admitted available domain physicalStored covered memos valid
  exact ⟨result, after, saved, final, actual, receipt,
    operand_receipt depth receipt ready available domain physicalStored merged current bounded⟩

/-- Actual head, tail, and checked-query order retain the explicit maximum cap transformer. -/
theorem fold (depth : Nat)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Fold values seed paths before memo result after saved} (reads : FoldReads formulas solver actual memos final) :
    Ready before → Values before.native.machine.heap values → PhysicalStored before.native.machine.heap memo →
      MergeStored memo → Current before → (∀ value ∈ values, Cap Plain depth value) →
      (∀ path ∈ seed :: paths, Domain path values) →
      Ready after ∧ Effects (physical before) (physical after) ∧ PhysicalStored after.native.machine.heap saved ∧
      MergeStored saved ∧ Current after ∧ Available after.native.machine.heap result ∧ result.free = [] ∧
      Cap Plain (foldDepth depth seed paths) result := by
  induction reads with
  | nil receipt =>
      intro ready available physicalStored merged current bounded domains
      have own := operand_receipt depth receipt ready available (domains _ List.mem_cons_self) physicalStored merged current bounded
      exact ⟨receipt.ready, receipt.effects, receipt.stored, own.1, own.2.1, receipt.available, receipt.closed, own.2.2⟩
  | cons receipt remaining query ih =>
      intro ready available physicalStored merged current bounded domains
      have own := operand_receipt depth receipt ready available (domains _ (by simp)) physicalStored merged current bounded
      obtain ⟨tailReady, tailEffects, tailPhysical, tailMerged, tailCurrent, tailAvailable, tailClosed, tailBound⟩ :=
        ih receipt.ready receipt.originals receipt.stored own.1 own.2.1 bounded (tail_all domains)
      have headBound := own.2.2.mono (Nat.le_max_left _ _)
      have restBound := tailBound.mono (Nat.le_max_right _ _)
      have checked := SourceCurrentConstrainedCapCurrentNative.step _ formulas solver query.actual tailReady.good tailReady.semantic
        tailCurrent (tailEffects.keeps.available _ receipt.available) tailAvailable receipt.closed tailClosed headBound restBound
      exact ⟨query.ready, receipt.effects.trans (tailEffects.trans query.effects), tailPhysical.grows query.effects.keeps,
        tailMerged, checked.1, query.available, query.closed, checked.2.1⟩

/-- A supplied target derives its finite cap without a hereditary leaf or all-root closure premise. -/
theorem target_reads (depth : Nat)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Target values paths before memo result after saved} (reads : TargetReads formulas solver actual memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (merged : MergeStored memo)
    (current : Current before) (bounded : ∀ value ∈ values, Cap Plain depth value)
    (domains : ∀ path ∈ paths, Domain path values) :
    MergeStored saved ∧ Current after ∧ Cap Plain (targetDepth depth paths) result := by
  cases reads with
  | nil => exact ⟨merged, current, .plain 0 .empty⟩
  | cons reads =>
      obtain ⟨_, _, _, mergedAfter, currentAfter, _, _, boundedAfter⟩ :=
        fold depth reads ready available physicalStored merged current bounded domains
      exact ⟨mergedAfter, currentAfter, boundedAfter⟩

end MicroCFTA.SourceCurrentConstrainedCapMixedTarget
