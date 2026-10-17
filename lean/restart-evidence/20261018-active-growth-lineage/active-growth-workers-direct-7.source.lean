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

private theorem exposures [DecidableEq (EdgeKey Symbol Guard)] (h : Nat) (values : List Node) (before : Physical) :
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

private theorem projections [DecidableEq (EdgeKey Symbol Guard)] (p h : Nat) (jobs : List (SourceCurrentConjunctionRowsWorker.Job Symbol FullSyntax.Formula))
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

private theorem classes [DecidableEq (EdgeKey Symbol Guard)] (p h : Nat) (forests : List (List Node))
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

private theorem requirements [DecidableEq (EdgeKey Symbol Guard)] (p h : Nat) (edges : List Edge) (constraints) (before : Physical) :
    Grows before.equality (SourceCurrentConjunctionRowsWorker.requirements p h edges constraints before).state.equality := by
  apply rows_bind _ _ (classes p h _ constraints before)
  intro values after
  exact SourceEqualityConstraintMemoAllocation.grows_refl _

private theorem tuple [DecidableEq (EdgeKey Symbol Guard)] (p h : Nat) (edges : List Edge) (before : Physical) :
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

private theorem tuples [DecidableEq (EdgeKey Symbol Guard)] (p h : Nat) (edges : List (List Edge)) (before : Physical) :
    Grows before.equality (SourceCurrentConjunctionRowsWorker.tuples p h edges before).state.equality := by
  induction edges generalizing before with
  | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | cons first rest ih =>
    apply rows_bind _ _ (tuple p h first before)
    intro value middle
    apply rows_bind _ _ (ih middle)
    intro values after
    exact SourceEqualityConstraintMemoAllocation.grows_refl _

private theorem conjunction_rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (p h : Nat) (values : List Node) (before : Physical) :
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

private theorem shared_bind (first : SourceCurrentAllocatedSharedTargetWorker.Outcome width)
    (next : Node → Shared width → SourceCurrentAllocatedSharedTargetWorker.Outcome width)
    (head : Grows before first.state.checked.operations)
    (tail : ∀ value middle, Grows middle.checked.operations (next value middle).state.checked.operations) :
    Grows before (first.bind next).state.checked.operations := by
  cases first with
  | failed => exact head
  | done value middle => exact trans head (tail value middle)

private theorem edit_bind (first : SourceCurrentAllocatedSharedEditWorker.Outcome width A)
    (next : A → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width B)
    (head : Grows before first.state.checked.operations)
    (tail : ∀ value middle, Grows middle.checked.operations (next value middle).state.checked.operations) :
    Grows before (first.bind next).state.checked.operations := by
  cases first with
  | failed => exact head
  | done value middle => exact trans head (tail value middle)

private theorem class_bind (first : SourceCurrentAllocatedClassWorker.Outcome width)
    (next : List Node → Checked width → Memo → SourceCurrentAllocatedClassWorker.Outcome width)
    (head : Grows before first.state.operations)
    (tail : ∀ value middle saved, Grows middle.operations (next value middle saved).state.operations) :
    Grows before (first.bind next).state.operations := by
  cases first with
  | failed => exact head
  | done value middle saved => exact trans head (tail value middle saved)

private theorem seeded_bind (first : SourceCurrentAllocatedSeededWorker.Outcome width)
    (next : Node → Checked width → SourceCurrentAllocatedSeededWorker.Outcome width)
    (head : Grows before first.state.operations)
    (tail : ∀ value middle, Grows middle.operations (next value middle).state.operations) :
    Grows before (first.bind next).state.operations := by
  cases first with
  | failed => exact head
  | done value middle => exact trans head (tail value middle)

private theorem edit_children
    (recur : SourceEqualityEdits.Edits EqualityNormalize.Path → Node → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width Node)
    (small : ∀ edits value before, Grows before.checked.operations (recur edits value before).state.checked.operations)
    (entries) (index : Nat) (values : List Node) (before : Shared width) :
    Grows before.checked.operations (SourceCurrentAllocatedSharedEditWorker.children recur entries index values before).state.checked.operations := by
  induction values generalizing index before with
  | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | cons value values ih =>
    simp only [SourceCurrentAllocatedSharedEditWorker.children]
    split
    · apply edit_bind _ _ (ih _ _)
      intros
      exact SourceEqualityConstraintMemoAllocation.grows_refl _
    · apply edit_bind _ _ (small _ _ _)
      intro result middle
      apply edit_bind _ _ (ih _ _)
      intros
      exact SourceEqualityConstraintMemoAllocation.grows_refl _

private theorem seeded_operand [DecidableEq (EdgeKey Symbol Guard)] (p h : Nat) (path : List Int) (values : List Node) (before : Checked width) :
    Grows before.operations (SourceCurrentAllocatedSeededWorker.operand p h path values before).state.operations := by
  unfold SourceCurrentAllocatedSeededWorker.operand
  split <;> exact SourceEqualityConstraintMemoAllocation.grows_refl _

private theorem scan_bind (first : SourceCurrentAllocatedScanWorker.Outcome A width)
    (next : A → Checked width → Fourth → SourceCurrentAllocatedScanWorker.Outcome B width)
    (head : Grows before first.state.operations)
    (tail : ∀ value middle saved, Grows middle.operations (next value middle saved).state.operations) :
    Grows before (first.bind next).state.operations := by
  cases first with
  | failed => exact head
  | done value middle saved => exact trans head (tail value middle saved)

private theorem local_bind (first : SourceCurrentAllocatedLocalWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedLocalWorker.Outcome B width)
    (head : Grows before first.state.operations)
    (tail : ∀ value middle fourth saved, Grows middle.operations (next value middle fourth saved).state.operations) :
    Grows before (first.bind next).state.operations := by
  cases first with
  | failed => exact head
  | done value middle fourth saved => exact trans head (tail value middle fourth saved)

private theorem gate_lift (tag : InternedNestedConstruction.Outcome Symbol Guard (Option Bool) → SourceCurrentAllocatedGateWorker.Fault)
    (before : Checked width) (actual : InternedNestedConstruction.Outcome Symbol Guard (Option Bool)) :
    (SourceCurrentAllocatedGateWorker.lift tag before actual).state.operations = before.operations := by
  cases actual with
  | pending => rfl
  | done value => cases value <;> rfl

private theorem scan_gate [DecidableEq (EdgeKey Symbol Guard)] (belowEnd : Bool) (fuel : Nat) (values : List Node) (paths) (before : Checked width) (memo : Fourth) :
    Grows before.operations (SourceCurrentAllocatedScanWorker.gate belowEnd fuel values paths before memo).state.operations := by
  have first : (if belowEnd then SourceCurrentAllocatedGateWorker.primary fuel values paths before
      else SourceCurrentAllocatedGateWorker.secondary fuel values paths before).state.operations = before.operations := by
    cases belowEnd <;> exact gate_lift _ _ _
  unfold SourceCurrentAllocatedScanWorker.gate
  split <;> simp_all only [SourceCurrentAllocatedGateWorker.Outcome.state,
    SourceCurrentAllocatedScanWorker.Outcome.state]
  all_goals exact SourceEqualityConstraintMemoAllocation.grows_refl _

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

private theorem conjunction_explore (p h budget : Nat)
    (table : SourceCurrentConjunctionWorker.Table Symbol FullSyntax.Formula)
    (pending : List (List Node)) (before : Physical) :
    Grows before.equality (SourceCurrentConjunctionWorker.explore p h budget table pending before).state.equality := by
  rw [SourceCurrentConjunctionWorker.explore.eq_def]
  cases pending with
  | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | cons nodes rest =>
    cases impossible : nodes.any SourceCurrentConjunctionRequirements.isEmpty with
    | true => simpa only [impossible,ite_true] using conjunction_explore p h budget table rest before
    | false =>
      simp only [impossible,Bool.false_eq_true,ite_false]
      cases skipped : SourceCurrentConjunctionEmptinessTable.skip SourceCurrentConjunctionRequirements.key
          SourceCurrentConjunctionWorklist.closed budget table nodes with
      | true => simpa only [skipped,ite_true] using conjunction_explore p h budget table rest before
      | false =>
        simp only [Bool.false_eq_true,ite_false]
        have first := conjunction_rows p h nodes before
        cases actual : SourceCurrentConjunctionRowsWorker.rows p h nodes before with
        | failed fault after =>
          rw [actual] at first
          exact first
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
    · apply physical_bind _ _ (conjunction_decision p h budget value (SourceCurrentAllocatedNativeEffects.physical before))
      intros
      exact SourceEqualityConstraintMemoAllocation.grows_refl _
  unfold SourceCurrentAllocatedConjunctionWorker.call
  cases actual : SourceCurrentConjunctionWorker.call p h budget memo value
      (SourceCurrentAllocatedNativeEffects.physical before) <;>
    rw [actual] at first
    exact first

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
      | request value => exact (ih (A := Node)).2 clear s value before memo
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
      rw [actual] at first
      exact first

private theorem target_leaf (n : Nat) (left right : Node) (before : Checked width) (memo : Memo) :
    Grows before.operations (SourceCurrentAllocatedTargetWorker.leaf n left right before memo).state.operations := by
  have first := SourceCurrentOperationGrowth.native n (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before
  unfold SourceCurrentAllocatedTargetWorker.leaf
  split <;> simp_all only [SourceEqualityNativeDemand.Outcome.state,SourceCurrentAllocatedTargetWorker.Outcome.state]

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

private theorem force (p h m s n : Nat) (record : Record) (values : List Node) (path) (before : Shared width) :
    Grows before.checked.operations (SourceCurrentAllocatedSharedTargetWorker.force p h m s n record values path before).state.checked.operations := by
  unfold SourceCurrentAllocatedSharedTargetWorker.force
  split
  · exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · have first := target p h m s n values (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo
    split <;> simp_all only [SourceCurrentAllocatedTargetWorker.Outcome.state,
      SourceCurrentAllocatedSharedTargetWorker.Outcome.state,SourceCurrentAllocatedSharedTargetState.store]

private theorem shared_step (n : Nat) (left right : Node) (before : Shared width) :
    Grows before.checked.operations (SourceCurrentAllocatedSharedTargetWorker.step n left right before).state.checked.operations := by
  have first := SourceCurrentOperationGrowth.native n (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked
  unfold SourceCurrentAllocatedSharedTargetWorker.step
  split <;> simp_all only [SourceEqualityNativeDemand.Outcome.state,
    SourceCurrentAllocatedSharedTargetWorker.Outcome.state,SourceCurrentAllocatedSharedTargetState.advance]

private theorem shared_leaf (p h m s n : Nat) (record : Record) (values : List Node) (path) (input : Node) (before : Shared width) :
    Grows before.checked.operations (SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record values path input before).state.checked.operations :=
  shared_bind _ _ (force p h m s n record values path before) (fun _value middle => shared_step n _ _ middle)

private theorem edit_rows
    (recur : SourceEqualityEdits.Edits EqualityNormalize.Path → Node → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width Node)
    (small : ∀ edits value before, Grows before.checked.operations (recur edits value before).state.checked.operations)
    (entries) (edges : List Edge) (before : Shared width) :
    Grows before.checked.operations (SourceCurrentAllocatedSharedEditWorker.rows recur entries edges before).state.checked.operations := by
  induction edges generalizing before with
  | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | cons edge edges ih =>
    apply edit_bind _ _ (edit_children recur small entries 0 edge.children before)
    intro values middle
    have made : Grows middle.checked.operations
        (SourceCurrentAllocatedSharedEditWorker.work (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).state.checked.operations := SourceEqualityConstraintMemoAllocation.grows_refl _
    apply edit_bind _ _ made
    intro result afterEdge
    apply edit_bind _ _ (ih _)
    intros
    exact SourceEqualityConstraintMemoAllocation.grows_refl _

private theorem edit (record : Record) (originals : List Node) (e p h m s n : Nat) (edits) (value : Node) (before : Shared width) :
    Grows before.checked.operations (SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits value before).state.checked.operations := by
  induction e generalizing edits value before with
  | zero => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | succ e ih =>
    cases edits with
    | editAt path =>
      have first := shared_leaf p h m s n record originals path value before
      unfold SourceCurrentAllocatedSharedEditWorker.edit SourceCurrentAllocatedSharedEditWorker.leaf
      cases actual : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals path value before <;>
        simpa only [actual,SourceCurrentAllocatedSharedEditWorker.lift,
          SourceCurrentAllocatedSharedTargetWorker.Outcome.state,SourceCurrentAllocatedSharedEditWorker.Outcome.state] using first
    | editBelow entries =>
      cases value with
      | empty | reference => exact SourceEqualityConstraintMemoAllocation.grows_refl _
      | node entry edges depth free =>
        exact edit_bind _ _ (edit_rows _ (fun edits value before => ih edits value before) entries edges before)
          (fun values after => SourceEqualityConstraintMemoAllocation.grows_refl _)
      | mu | union =>
        all_goals
          apply edit_bind
          · unfold SourceCurrentAllocatedSharedEditWorker.head
            split <;> exact SourceEqualityConstraintMemoAllocation.grows_refl _
          · intro value after
            exact ih _ value after

private theorem class_run (e p h m s n : Nat) (record : Record) (values : List Node) (before : Checked width) (memo : Memo) :
    Grows before.operations (SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo).state.operations := by
  have first : Grows before.operations (SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record values e p h m s n)
      (SourceCurrentAllocatedClassEditPlan.compiled record) values
      (SourceCurrentAllocatedSharedTargetState.initial before memo)).state.checked.operations := by
    unfold SourceCurrentAllocatedSharedEditWorker.editList
    split
    · exact SourceEqualityConstraintMemoAllocation.grows_refl _
    · exact edit_children _ (edit record values e p h m s n) _ 0 values (SourceCurrentAllocatedSharedTargetState.initial before memo)
  unfold SourceCurrentAllocatedClassWorker.runClass
  split <;> simp_all only [SourceCurrentAllocatedSharedEditWorker.Outcome.state,SourceCurrentAllocatedClassWorker.Outcome.state]

private theorem class_fold (e p h m s n : Nat) (records : List Record) (values : List Node) (before : Checked width) (memo : Memo) :
    Grows before.operations (SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo).state.operations := by
  induction records generalizing values before memo with
  | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | cons record records ih =>
    exact class_bind _ _ (ih values before memo) (fun values after saved => class_run e p h m s n record values after saved)

private theorem class_pass (e p h m s n : Nat) (records : List Record) (values : List Node) (before : Checked width) (memo : Memo) :
    Grows before.operations (SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo).state.operations :=
  class_bind _ _ (class_fold e p h m s n records values before memo)
    (fun _values _after _saved => SourceEqualityConstraintMemoAllocation.grows_refl _)

private theorem seeded_leaf (n : Nat) (left right : Node) (before : Checked width) :
    Grows before.operations (SourceCurrentAllocatedSeededWorker.leaf n left right before).state.operations := by
  have first := SourceCurrentOperationGrowth.native n (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before
  unfold SourceCurrentAllocatedSeededWorker.leaf
  split <;> simp_all only [SourceEqualityNativeDemand.Outcome.state,SourceCurrentAllocatedSeededWorker.Outcome.state]

private theorem seeded_fold (p h n : Nat) (values : List Node) (seed : List Int) (paths : List (List Int)) (before : Checked width) :
    Grows before.operations (SourceCurrentAllocatedSeededWorker.fold p h n values seed paths before).state.operations := by
  induction paths generalizing before with
  | nil => exact seeded_operand p h seed values before
  | cons path paths ih =>
    exact seeded_bind _ _ (seeded_operand p h path values before)
      (fun value middle => seeded_bind _ _ (ih middle) (fun result after => seeded_leaf n _ _ after))

private theorem seeded (p h n : Nat) (values : List Node) (paths : List (List Int)) (before : Checked width) :
    Grows before.operations (SourceCurrentAllocatedSeededWorker.seeded p h n values paths before).state.operations := by
  cases paths with
  | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | cons seed paths => exact seeded_fold p h n values seed paths before

private theorem scan_query (p h n : Nat) (values : List Node) (paths) (before : Checked width) (memo : Fourth) :
    Grows before.operations (SourceCurrentAllocatedScanWorker.query p h n values paths before memo).state.operations := by
  have first := seeded p h n values (paths.map (List.map Int.ofNat)) before
  unfold SourceCurrentAllocatedScanWorker.query
  split <;> simp_all only [SourceCurrentAllocatedSeededWorker.Outcome.state,SourceCurrentAllocatedScanWorker.Outcome.state]

variable [DecidableEq Node]

private theorem scan_decision (p h budget : Nat) (paths) (value : Node) (before : Checked width) (memo : Fourth) :
    Grows before.operations (SourceCurrentAllocatedScanWorker.decision p h budget paths value before memo).state.operations := by
  have first := conjunction p h budget value before memo
  unfold SourceCurrentAllocatedScanWorker.decision
  split <;> simp_all only [SourceCurrentAllocatedConjunctionWorker.Outcome.state,SourceCurrentAllocatedScanWorker.Outcome.state]

private theorem scan (g s p h n budget : Nat) (values : List Node) (classes) (before : Checked width) (memo : Fourth) :
    Grows before.operations (SourceCurrentAllocatedScanWorker.scan g s p h n budget values classes before memo).state.operations := by
  induction classes generalizing before memo with
  | nil => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | cons paths classes ih =>
    apply scan_bind _ _ (scan_gate true g values paths before memo)
    intro primary middle saved
    cases primary with
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      have rest := ih middle saved
      cases actual : SourceCurrentAllocatedScanWorker.scan g s p h n budget values classes middle saved with
      | failed => simpa only [actual,SourceCurrentAllocatedScanWorker.Outcome.state,SourceCurrentAllocatedScanWorker.Outcome.select] using rest
      | done value => cases value; simpa only [actual,SourceCurrentAllocatedScanWorker.Outcome.state,SourceCurrentAllocatedScanWorker.Outcome.select] using rest
    | true =>
      apply scan_bind _ _ (scan_gate false s values paths middle saved)
      intro secondary later current
      cases secondary with
      | true => exact ih later current
      | false =>
        apply scan_bind _ _ (scan_query p h n values paths later current)
        intro value checked fourth
        apply scan_bind _ _ (scan_decision p h budget paths value checked fourth)
        intro answer after final
        cases answer with
        | true => exact SourceEqualityConstraintMemoAllocation.grows_refl _
        | false => exact ih after final

private theorem record_scan (g s p h n budget : Nat) (values : List Node) (records) (before : Checked width) (memo : Fourth) :
    Grows before.operations (SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before memo).state.operations := by
  have first := scan g s p h n budget values (records.map SourceEqualityClassOrder.Record.paths) before memo
  have same := congrArg SourceCurrentAllocatedScanWorker.Outcome.state
    (SourceCurrentAllocatedRecordScanWorker.scan_mapPaths g s p h n budget values records before memo)
  rw [← same] at first
  cases actual : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before memo with
  | failed => exact first
  | done result => cases result; exact first

private theorem local_classes (g s r e p h m c n budget : Nat) (records) (values : List Node)
    (before : Checked width) (fourth : Fourth) (memo : Memo) :
    Grows before.operations (SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values before fourth memo).state.operations := by
  unfold SourceCurrentAllocatedLocalWorker.classes
  apply local_bind
  · have first := record_scan g s p h n budget values records before fourth
    unfold SourceCurrentAllocatedLocalWorker.scan
    split <;> simp_all only [SourceCurrentAllocatedScanWorker.Outcome.state,SourceCurrentAllocatedLocalWorker.Outcome.state]
  · intro result middle saved current
    cases result with
    | mk stopped selected =>
      cases stopped with
      | some paths => exact SourceEqualityConstraintMemoAllocation.grows_refl _
      | none =>
        apply local_bind
        · unfold SourceCurrentAllocatedLocalWorker.required
          split <;> exact SourceEqualityConstraintMemoAllocation.grows_refl _
        · intro results checked next warm
          have first := class_pass e p h m c n selected results checked warm
          unfold SourceCurrentAllocatedLocalWorker.pass
          split <;> simp_all only [SourceCurrentAllocatedClassWorker.Outcome.state,SourceCurrentAllocatedLocalWorker.Outcome.state]

private theorem local_reduce (g s r e p h m c n budget : Nat) (loaded) (inherited : EqValue) (values : List Node)
    (before : Checked width) (fourth : Fourth) (memo : Memo) :
    Grows before.operations (SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values before fourth memo).state.operations := by
  have first := SourceCurrentOperationGrowth.precheck loaded.stored loaded.guard inherited before.operations
  unfold SourceCurrentAllocatedLocalWorker.reduce
  dsimp only
  split
  · exact first
  · exact first
  · exact first
  · exact trans first (local_classes g s r e p h m c n budget _ values
      (SourceCurrentAllocatedQueryMemo.advancePhysical before ⟨before.native.machine.heap,
        (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.operations).2⟩) fourth memo)

/-- Every literal parent outcome retains all earlier operation allocations and memo entries. -/
theorem parent (g s r e p h m c n budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue)
    (values : List Node) (before : Checked width) (fourth : Fourth) (memo : Memo) :
    Grows before.operations (SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited values before fourth memo).state.operations := by
  unfold SourceCurrentAllocatedParentWorker.edge
  split
  · exact SourceCurrentOperationGrowth.emptyField _
  · split
    · exact SourceEqualityConstraintMemoAllocation.grows_refl _
    · exact SourceEqualityConstraintMemoAllocation.grows_refl _
    · rename_i loaded found
      have first := local_reduce g s r e p h m c n budget loaded inherited values before fourth memo
      unfold SourceCurrentAllocatedParentWorker.reduceChildren
      cases actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values before fourth memo with
      | failed => simpa only [actual,SourceCurrentAllocatedLocalWorker.Outcome.state,SourceCurrentAllocatedParentWorker.Outcome.bind,SourceCurrentAllocatedParentWorker.Outcome.state] using first
      | done results checked savedFourth saved =>
        have first : Grows before.operations checked.operations := by simpa only [actual,SourceCurrentAllocatedLocalWorker.Outcome.state] using first
        have last := SourceCurrentOperationGrowth.mkEdge symbol loaded.stored loaded.guard results checked.operations checked.native.machine.heap
        unfold SourceCurrentAllocatedParentWorker.Outcome.bind SourceCurrentAllocatedParentWorker.build SourceCurrentAllocatedMkEdge.build
        dsimp only
        split <;> simp_all only [SourceCurrentAllocatedParentWorker.Outcome.state]
        all_goals exact trans first last

end MicroCFTA.SourceCurrentWorkerOperationGrowth
