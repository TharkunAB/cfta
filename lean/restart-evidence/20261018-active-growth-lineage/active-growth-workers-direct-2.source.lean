import MicroCFTA.SourceCurrentOperationGrowth

/-!
# Equality-operation growth through literal lower workers

The proofs inspect bounded worker outcomes. They require no supplied
completed graph, dynamic range, or semantic result law.
-/
namespace MicroCFTA.SourceCurrentWorkerOperationGrowth
open Cache InternedConstructorTemplates
open SourceEqualityConstraintMemoAllocation (Grows)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Record" => SourceEqualityClassOrder.Record

private theorem trans {before middle after : SourceEqualityConstraintMemoAllocation.State}
    (first : Grows before middle) (last : Grows middle after) : Grows before after :=
  SourceCurrentConjunctionEquality.grows_trans first last

private theorem rows_bind (first : SourceCurrentConjunctionRowsWorker.Outcome Symbol FullSyntax.Formula A)
    (next : A → Physical → SourceCurrentConjunctionRowsWorker.Outcome Symbol FullSyntax.Formula B)
    (head : Grows before first.state.equality)
    (tail : ∀ value middle, Grows middle.equality (next value middle).state.equality) :
    Grows before (first.bind next).state.equality := by
  cases first with
  | failed => exact head
  | done value middle => exact trans head (tail value middle)

private theorem exposures (h : Nat) (values : List Node) (before : Physical) :
    (SourceCurrentConjunctionRowsWorker.exposures h values before).state.equality = before.equality := by
  induction values generalizing before with
  | nil => rfl
  | cons value values ih =>
    simp only [SourceCurrentConjunctionRowsWorker.exposures]
    split
    · rename_i edges heap actual
      have rest := ih (⟨heap,before.equality⟩ : Physical)
      cases next : SourceCurrentConjunctionRowsWorker.exposures h values ⟨heap,before.equality⟩ <;>
        simpa only [next,SourceCurrentConjunctionRowsWorker.Outcome.state,
          SourceCurrentConjunctionRowsWorker.Outcome.bind] using rest
    all_goals rfl

private theorem projections (p h : Nat) (jobs : List (SourceCurrentConjunctionRowsWorker.Job Symbol FullSyntax.Formula))
    (before : Physical) :
    (SourceCurrentConjunctionRowsWorker.projections p h jobs before).state.equality = before.equality := by
  induction jobs generalizing before with
  | nil => rfl
  | cons job jobs ih =>
    cases job with
    | mk forest path =>
      simp only [SourceCurrentConjunctionRowsWorker.projections]
      split
      · rename_i value heap actual
        have rest := ih (⟨heap,before.equality⟩ : Physical)
        cases next : SourceCurrentConjunctionRowsWorker.projections p h jobs ⟨heap,before.equality⟩ <;>
          simpa only [next,SourceCurrentConjunctionRowsWorker.Outcome.state,
            SourceCurrentConjunctionRowsWorker.Outcome.bind] using rest
      all_goals rfl

private theorem classes (p h : Nat) (forests : List (List Node))
    (constraints : EqualityNormalize.Constraints) (before : Physical) :
    Grows before.equality (SourceCurrentConjunctionRowsWorker.classes p h forests constraints before).state.equality := by
  induction constraints generalizing before with
  | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | cons paths rest ih =>
    simp only [SourceCurrentConjunctionRowsWorker.classes]
    apply rows_bind
    · rw [projections]; exact SourceEqualityConstraintMemoAllocation.grows_refl _
    · intro values middle
      apply rows_bind _ _ (ih middle)
      intro values after
      exact SourceEqualityConstraintMemoAllocation.grows_refl _

private theorem requirements (p h : Nat) (edges : List Edge) (constraints) (before : Physical) :
    Grows before.equality (SourceCurrentConjunctionRowsWorker.requirements p h edges constraints before).state.equality := by
  apply rows_bind _ _ (classes p h _ constraints before)
  intro values after
  exact SourceEqualityConstraintMemoAllocation.grows_refl _

private theorem tuple (p h : Nat) (edges : List Edge) (before : Physical) :
    Grows before.equality (SourceCurrentConjunctionRowsWorker.tuple p h edges before).state.equality := by
  unfold SourceCurrentConjunctionRowsWorker.tuple
  dsimp only
  split
  · exact SourceCurrentOperationGrowth.equality_fold _ _
  · exact SourceCurrentOperationGrowth.equality_fold _ _
  · split
    · exact SourceCurrentOperationGrowth.equality_fold _ _
    · apply rows_bind _ _ (trans (SourceCurrentOperationGrowth.equality_fold _ _) (requirements p h edges _ ⟨before.heap,(SourceCurrentConjunctionEquality.fold edges before.equality).2⟩))
      intro values after
      exact SourceEqualityConstraintMemoAllocation.grows_refl _

private theorem tuples (p h : Nat) (edges : List (List Edge)) (before : Physical) :
    Grows before.equality (SourceCurrentConjunctionRowsWorker.tuples p h edges before).state.equality := by
  induction edges generalizing before with
  | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | cons first rest ih =>
    apply rows_bind _ _ (tuple p h first before)
    intro value middle
    apply rows_bind _ _ (ih middle)
    intro values after
    exact SourceEqualityConstraintMemoAllocation.grows_refl _

private theorem conjunction_rows (p h : Nat) (values : List Node) (before : Physical) :
    Grows before.equality (SourceCurrentConjunctionRowsWorker.rows p h values before).state.equality := by
  apply rows_bind
  · rw [exposures]; exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · intro edges after
    exact tuples p h _ after

private theorem physical_bind (first : SourceCurrentConjunctionWorker.Outcome Symbol FullSyntax.Formula A)
    (next : A → Physical → SourceCurrentConjunctionWorker.Outcome Symbol FullSyntax.Formula B)
    (head : Grows before first.state.equality)
    (tail : ∀ value middle, Grows middle.equality (next value middle).state.equality) :
    Grows before (first.bind next).state.equality := by
  cases first with
  | failed => exact head
  | done value middle => exact trans head (tail value middle)

private theorem merge_bind (first : SourceCurrentAllocatedMergeWorker.Outcome A)
    (next : A → SourceCurrentAllocatedMergeGraph.State → Memo → SourceCurrentAllocatedMergeWorker.Outcome B)
    (head : Grows before first.state.equality)
    (tail : ∀ value middle saved, Grows middle.equality (next value middle saved).state.equality) :
    Grows before (first.bind next).state.equality := by
  cases first with
  | failed => exact head
  | done value middle saved => exact trans head (tail value middle saved)

private theorem target_bind (first : SourceCurrentAllocatedTargetWorker.Outcome width)
    (next : Node → Checked width → Memo → SourceCurrentAllocatedTargetWorker.Outcome width)
    (head : Grows before first.state.operations)
    (tail : ∀ value middle saved, Grows middle.operations (next value middle saved).state.operations) :
    Grows before (first.bind next).state.operations := by
  cases first with
  | failed => exact head
  | done value middle saved => exact trans head (tail value middle saved)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem conjunction_explore (p h budget : Nat)
    (table : SourceCurrentConjunctionWorker.Table Symbol FullSyntax.Formula)
    (pending : List (List Node)) (before : Physical) :
    Grows before.equality (SourceCurrentConjunctionWorker.explore p h budget table pending before).state.equality := by
  rw [SourceCurrentConjunctionWorker.explore.eq_def]
  cases pending with
  | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | cons nodes rest =>
    split
    · exact conjunction_explore p h budget table rest before
    · split
      · exact conjunction_explore p h budget table rest before
      · have first := conjunction_rows p h nodes before
        cases actual : SourceCurrentConjunctionRowsWorker.rows p h nodes before with
        | failed fault after => simpa only [SourceCurrentConjunctionRowsWorker.Outcome.state,actual] using first
        | done requirements middle =>
          have first : Grows before.equality middle.equality := by simpa only [actual,SourceCurrentConjunctionRowsWorker.Outcome.state] using first
          exact trans first (conjunction_explore p h (budget-1) _ _ middle)
termination_by (budget,pending.length)
decreasing_by
  all_goals first
    | apply Prod.Lex.right; simp_all
    | apply Prod.Lex.left
      have positive := (SourceCurrentConjunctionEmptinessTable.admitted SourceCurrentConjunctionRequirements.key
        SourceCurrentConjunctionWorklist.closed budget table nodes (by assumption)).1
      omega

private theorem conjunction_decision [DecidableEq Node] (p h budget : Nat) (value : Node) (before : Physical) :
    Grows before.equality (SourceCurrentConjunctionWorker.decision p h budget value before).state.equality := by
  unfold SourceCurrentConjunctionWorker.decision
  split
  · apply physical_bind _ _ (conjunction_explore p h budget _ _ before)
    intro table after
    split <;> exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · exact SourceEqualityConstraintMemoAllocation.grows_refl _

private theorem conjunction [DecidableEq Node] (p h budget : Nat) (value : Node) (before : Checked width) (memo : Fourth) :
    Grows before.operations (SourceCurrentAllocatedConjunctionWorker.call p h budget value before memo).state.operations := by
  have first : Grows before.operations (SourceCurrentConjunctionWorker.call p h budget memo value
      (SourceCurrentAllocatedNativeEffects.physical before)).state.equality := by
    unfold SourceCurrentConjunctionWorker.call
    split
    · exact SourceEqualityConstraintMemoAllocation.grows_refl _
    · apply physical_bind _ _ (conjunction_decision p h budget value _)
      intros
      exact SourceEqualityConstraintMemoAllocation.grows_refl _
  unfold SourceCurrentAllocatedConjunctionWorker.call
  cases actual : SourceCurrentConjunctionWorker.call p h budget memo value
      (SourceCurrentAllocatedNativeEffects.physical before) <;>
    simpa only [actual,SourceCurrentConjunctionWorker.Outcome.state] using first

private theorem merge_both (fuel : Nat) :
    (∀ clear s (code : SourceCurrentAllocatedMergeGraph.Code A) state memo,
      Grows state.equality (SourceCurrentAllocatedMergeWorker.execute clear fuel s code state memo).state.equality) ∧
    (∀ clear s value state memo,
      Grows state.equality (SourceCurrentAllocatedMergeWorker.call clear fuel s value state memo).state.equality) := by
  induction fuel generalizing A with
  | zero => constructor <;> intros <;> exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | succ fuel ih =>
    constructor
    · intro clear s code before memo
      cases code with
      | pure | work => exact SourceEqualityConstraintMemoAllocation.grows_refl _
      | topRow => exact SourceCurrentOperationGrowth.emptyField _
      | select values => simp only [SourceCurrentAllocatedMergeWorker.execute]; split <;> exact SourceEqualityConstraintMemoAllocation.grows_refl _
      | request value => exact ih.2 clear s value before memo
      | bind first next =>
        exact merge_bind _ _ (ih.1 clear s first before memo) (fun value middle saved => ih.1 clear s (next value) middle saved)
    · intro clear s value before memo
      unfold SourceCurrentAllocatedMergeWorker.call
      split
      · exact SourceEqualityConstraintMemoAllocation.grows_refl _
      · apply merge_bind _ _ (ih.1 clear s _ before memo)
        intros
        exact SourceEqualityConstraintMemoAllocation.grows_refl _

private theorem target_operand (p h m s : Nat) (path : List Int) (values : List Node) (before : Checked width) (memo : Memo) :
    Grows before.operations (SourceCurrentAllocatedTargetWorker.operand p h m s path values before memo).state.operations := by
  unfold SourceCurrentAllocatedTargetWorker.operand
  apply target_bind
  · unfold SourceCurrentAllocatedTargetWorker.projection
    split <;> exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · intro value middle saved
    have first := (merge_both (A := Node) m).2 SourceCurrentAllocatedMerge.literalClear s value (SourceCurrentAllocatedNativeEffects.physical middle) saved
    unfold SourceCurrentAllocatedTargetWorker.merge
    cases actual : SourceCurrentAllocatedMergeWorker.call SourceCurrentAllocatedMerge.literalClear m s value
        (SourceCurrentAllocatedNativeEffects.physical middle) saved <;>
      simpa only [actual,SourceCurrentAllocatedMergeWorker.Outcome.state] using first

private theorem target_leaf (n : Nat) (left right : Node) (before : Checked width) (memo : Memo) :
    Grows before.operations (SourceCurrentAllocatedTargetWorker.leaf n left right before memo).state.operations := by
  have first := SourceCurrentOperationGrowth.native n (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before
  unfold SourceCurrentAllocatedTargetWorker.leaf
  split <;> simp_all only [SourceEqualityNativeDemand.Outcome.state]

private theorem target_fold (p h m s n : Nat) (values : List Node) (seed : List Int)
    (paths : List (List Int)) (before : Checked width) (memo : Memo) :
    Grows before.operations (SourceCurrentAllocatedTargetWorker.fold p h m s n values seed paths before memo).state.operations := by
  induction paths generalizing before memo with
  | nil => exact target_operand p h m s seed values before memo
  | cons path paths ih =>
    apply target_bind _ _ (target_operand p h m s path values before memo)
    intro value middle saved
    exact target_bind _ _ (ih middle saved) (fun value after memo => target_leaf n _ _ after memo)

private theorem target (p h m s n : Nat) (values : List Node) (paths : List (List Int))
    (before : Checked width) (memo : Memo) :
    Grows before.operations (SourceCurrentAllocatedTargetWorker.target p h m s n values paths before memo).state.operations := by
  cases paths with
  | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | cons seed paths => exact target_fold p h m s n values seed paths before memo

end MicroCFTA.SourceCurrentWorkerOperationGrowth
