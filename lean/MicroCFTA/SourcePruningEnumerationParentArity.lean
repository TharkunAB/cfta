import MicroCFTA.SourceCurrentAllocatedParentEdgeActual
import MicroCFTA.SourcePruningEnumerationAllocatedOriginHeap
import MicroCFTA.SourcePruningEnumerationLocalReductionArity

/-!
# Arity through actual allocated parent construction

A rejected parent uses its actual checked sentinel constructor.
A live parent uses its actual local-reduction reads before construction.
The complete native heap passes through both literal endpoints.
-/
namespace MicroCFTA.SourcePruningEnumerationParentArity
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedParentEdge (Edge)
open SourceCurrentAllocatedParentEdgeActual (Reads)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- The supplied actual parent reads retain arity at the same returned native heap. -/
theorem parent_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before after : Checked width} {result : EdgeValue Symbol Guard}
    {fourth savedFourth : Fourth} {memo saved : Memo} {memos final : Memos}
    {actual : Edge budget symbol original loaded inherited values before fourth memo result after savedFourth saved}
    (reads : Reads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (live : contradictory original = false →
      SourceEqualityGuardReadback.Cached original.equalities ∧
      SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited ∧
      Values before.native.machine.heap values ∧
      SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (heap : Heap before.native.machine.heap) :
    Heap after.native.machine.heap := by
  cases reads with
  | rejected =>
      exact (SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory _ _ ready admitted).preserves_arity_heap heap
  | live reads =>
      rename_i children middle test built reduction
      obtain ⟨cached, found, inheritedReady, available, ranges⟩ := live test
      have middleHeap := SourcePruningEnumerationLocalReductionArity.reduction_heap
        formulas solver inventory original reads ready admitted cached found inheritedReady available
        correct stored covered ranges valid heap
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original before.operations.constraints
        ready.good.operations.constraints cached loaded found
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory original
        reads ready admitted cached found inheritedReady available correct stored covered ranges valid
      have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original from ⟨cached, loaded, found⟩).grows
          receipt.effects.grows
      obtain ⟨chosen, returned, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next symbol loaded children middle
        receipt.ready receipt.admitted storedReady field receipt.available
      have same := Prod.mk.inj (constructor.actual.symm.trans built)
      have sameValue := Except.ok.inj same.1
      cases sameValue
      cases same.2
      exact constructor.preserves_arity_heap middleHeap

end MicroCFTA.SourcePruningEnumerationParentArity
