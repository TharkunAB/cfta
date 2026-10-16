import MicroCFTA.SourceCurrentAllocatedMergeWorkerCompletion

namespace MicroCFTA.AllocatedMergeCompletionKernels
open InternedConstructorTemplates
open SourceCurrentAllocatedMergeGraph (Code State Memo top body Run Call)
open SourceCurrentAllocatedMergeWorker (Outcome execute call)
open SourceCurrentAllocatedMergeWorkerCompletion
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A graph-derived stable Top instruction retains its literal equality allocation. -/
theorem top_row_exact (clear : Guard → Bool) (symbol : Symbol) (children : List (Value Symbol Guard))
    (before : State) (memo : Memo) :
    ∃ bound, ∀ fuel, bound ≤ fuel → execute clear fuel fuel (.topRow symbol children) before memo =
      .done (run (makeEdge symbol top children) before.heap).1
        ⟨(run (makeEdge symbol top children) before.heap).2, SourceEqualityMkEdgeAllocation.emptyField before.equality⟩ memo :=
  run_uniform (Run.topRow symbol children before memo)

/-- One shared selection bound serves the actual filter before the allocated Top continuation. -/
theorem selection_then_top {clear : Guard → Bool} {selection : Nat} {inputs values : List (Value Symbol Guard)}
    {before : State} {heap : InternedConstructorTemplates.State Symbol Guard} (symbol : Symbol) (memo : Memo)
    (selected : SourceMergedSelection.select clear selection inputs before.heap = .done values heap) :
    StableRun clear (.bind (.select inputs) (fun children => .topRow symbol children)) before memo
      (run (makeEdge symbol top values) heap).1
      ⟨(run (makeEdge symbol top values) heap).2, SourceEqualityMkEdgeAllocation.emptyField before.equality⟩ memo := by
  exact run_complete (.bind (.select selection selected) (.topRow symbol values ⟨heap, before.equality⟩ memo))

/-- A completed inner winner is reread after the actual recursive miss body. -/
theorem miss_rereads_inner_winner {clear : Guard → Bool} {input candidate : Value Symbol Guard}
    {before after : State} {memo current : Memo} {entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard}
    (absent : memo input.referenceOf = none) (actual : Run clear (body input) before memo candidate after current)
    (found : current input.referenceOf = some entry) :
    StableCall clear input before memo entry.result after current := by
  have stable := call_complete (Call.miss absent actual)
  have winner := SourceCurrentMemoMergeGraph.winner_existing current input candidate entry found
  simpa only [winner.1, winner.2] using stable

/-- A one-step warm hit needs no selection fuel and stays exact at every larger pair. -/
theorem warm_hit_no_selection {clear : Guard → Bool} {input : Value Symbol Guard} {before : State} {memo : Memo}
    {entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard} (found : memo input.referenceOf = some entry) :
    call clear 1 0 input before memo = .done entry.result before memo ∧
      ∀ work selection, 1 ≤ work → call clear work selection input before memo = .done entry.result before memo := by
  have actual := SourceCurrentAllocatedMergeWorker.call_hit clear 0 0 input before memo entry found
  refine ⟨actual, ?_⟩
  intro work selection enough
  exact call_done_stable actual enough (Nat.zero_le _)

/-- Different successful fuel pairs have the same result, full equality state, and merge memo. -/
theorem successful_observation_unique {clear : Guard → Bool} {input firstResult secondResult : Value Symbol Guard}
    {before firstAfter secondAfter : State} {memo firstSaved secondSaved : Memo}
    {firstWork firstSelection secondWork secondSelection : Nat}
    (first : call clear firstWork firstSelection input before memo = .done firstResult firstAfter firstSaved)
    (second : call clear secondWork secondSelection input before memo = .done secondResult secondAfter secondSaved) :
    firstResult = secondResult ∧ firstAfter = secondAfter ∧ firstSaved = secondSaved := by
  have firstLarger := call_done_stable first (Nat.le_max_left firstWork secondWork) (Nat.le_max_left firstSelection secondSelection)
  have secondLarger := call_done_stable second (Nat.le_max_right firstWork secondWork) (Nat.le_max_right firstSelection secondSelection)
  have same := firstLarger.symm.trans secondLarger
  cases same
  exact ⟨rfl, rfl, rfl⟩

/-- Literal comparison failures retain their exact diagnostic and reached operation state. -/
theorem selection_fault_preserved {clear : Guard → Bool} {selection work : Nat} {inputs : List (Value Symbol Guard)}
    {before : State} {memo : Memo} {fault : MergedSourceComparison.Fault}
    {heap : InternedConstructorTemplates.State Symbol Guard}
    (failed : SourceMergedSelection.select clear selection inputs before.heap = .failed fault heap) :
    execute clear (work + 1) selection (.select inputs) before memo = .failed fault ⟨heap, before.equality⟩ memo ∧
      ¬ ∃ output after saved, execute clear (work + 1) selection (.select inputs) before memo = .done output after saved := by
  have observed : execute clear (work + 1) selection (.select inputs) before memo =
      .failed fault ⟨heap, before.equality⟩ memo := by simp only [execute, failed]
  refine ⟨observed, ?_⟩
  rintro ⟨output, after, saved, impossible⟩
  rw [observed] at impossible
  cases impossible

#print axioms top_row_exact
#print axioms selection_then_top
#print axioms miss_rereads_inner_winner
#print axioms warm_hit_no_selection
#print axioms successful_observation_unique
#print axioms selection_fault_preserved
set_option pp.explicit true
#check @top_row_exact
#check @selection_then_top
#check @miss_rereads_inner_winner
#check @warm_hit_no_selection
#check @successful_observation_unique
#check @selection_fault_preserved
end MicroCFTA.AllocatedMergeCompletionKernels
