import MicroCFTA.SourceCurrentAllocatedMergeWorkerSound

namespace MicroCFTA.AllocatedMergeWorkerIntegration
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedMergeGraph (State Memo top Code small group)
open SourceCurrentAllocatedMergeWorker (execute call)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

 theorem zero_work_preserves_warm_hit
    (clear : Guard → Bool) (selectionFuel : Nat) (input : Value Symbol Guard) (state : State) (memo : Memo)
    (entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard) (found : memo input.referenceOf = some entry) :
    call clear 0 selectionFuel input state memo = .failed .exhausted state memo ∧
      call clear 1 selectionFuel input state memo = .done entry.result state memo :=
  ⟨rfl, SourceCurrentAllocatedMergeWorker.call_hit clear 0 selectionFuel input state memo entry found⟩

 theorem miss_does_not_complete_on_zero_body_fuel
    (clear : Guard → Bool) (selectionFuel : Nat) (input : Value Symbol Guard) (state : State) (memo : Memo)
    (absent : memo input.referenceOf = none) :
    call clear 1 selectionFuel input state memo = .failed .exhausted state memo := by
  simp only [call, absent, execute, SourceCurrentAllocatedMergeWorker.Outcome.bind]

 theorem top_allocation_and_graph
    (clear : Guard → Bool) (selectionFuel : Nat) (symbol : Symbol) (children : List (Value Symbol Guard))
    (state : State) (memo : Memo)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.equality) :
    let built := run (makeEdge symbol top children) state.heap
    let after : State := ⟨built.2, SourceEqualityMkEdgeAllocation.emptyField state.equality⟩
    execute clear 1 selectionFuel (.topRow symbol children) state memo = .done built.1 after memo ∧
      SourceCurrentAllocatedMergeGraph.Run clear (.topRow symbol children) state memo built.1 after memo ∧
      SourceEqualityConstraintMemoAllocation.Grows state.equality after.equality := by
  dsimp only
  have done := SourceCurrentAllocatedMergeWorker.topRow_done clear 0 selectionFuel symbol children state memo
  exact ⟨done, SourceCurrentAllocatedMergeWorkerSound.execute_sound done,
    (SourceEqualityMkEdgeAllocation.emptyField_correct state.equality valid).2.1⟩

 theorem allocation_survives_later_selection_failure
    (clear : Guard → Bool) (selectionFuel : Nat) (symbol : Symbol) (children inputs : List (Value Symbol Guard))
    (state : State) (memo : Memo) (fault : MergedSourceComparison.Fault)
    (heap : InternedConstructorTemplates.State Symbol Guard)
    (failed : SourceMergedSelection.select clear selectionFuel inputs
      (run (makeEdge symbol top children) state.heap).2 = .failed fault heap) :
    execute clear 2 selectionFuel (.bind (.topRow symbol children) (fun _ => .select inputs)) state memo =
      .failed fault ⟨heap, SourceEqualityMkEdgeAllocation.emptyField state.equality⟩ memo := by
  simp only [execute, SourceCurrentAllocatedMergeWorker.Outcome.bind, failed]


 theorem small_empty_row_retains_original_field
    (clear : Guard → Bool) (selectionFuel : Nat) (entry : Interned (EdgeKey Symbol Guard)) (state : State) (memo : Memo) :
    execute clear 2 selectionFuel (small (.mk entry [])) state memo =
      .done (run (makeEdge entry.key.symbol entry.key.constraint []) state.heap).1
        ⟨(run (makeEdge entry.key.symbol entry.key.constraint []) state.heap).2, state.equality⟩ memo := rfl

 theorem five_empty_rows_allocate_top
    (clear : Guard → Bool) (selectionFuel : Nat) (entry : Interned (EdgeKey Symbol Guard)) (state : State) (memo : Memo) :
    let edge : EdgeValue Symbol Guard := .mk entry []
    execute clear 3 selectionFuel (group [edge, edge, edge, edge, edge]) state memo =
      .done [(run (makeEdge entry.key.symbol top []) state.heap).1]
        ⟨(run (makeEdge entry.key.symbol top []) state.heap).2, SourceEqualityMkEdgeAllocation.emptyField state.equality⟩ memo := rfl

 theorem bound_request_hit_has_exact_call_graph
    (clear : Guard → Bool) (selectionFuel : Nat) (input : Value Symbol Guard) (state : State) (memo : Memo)
    (entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard) (found : memo input.referenceOf = some entry) :
    execute clear 2 selectionFuel (.request input) state memo = .done entry.result state memo ∧
      SourceCurrentAllocatedMergeGraph.Call clear input state memo entry.result state memo := by
  have done := SourceCurrentAllocatedMergeWorker.call_hit clear 0 selectionFuel input state memo entry found
  exact ⟨done, SourceCurrentAllocatedMergeWorkerSound.call_sound done⟩

 theorem top_prefix_then_pure_retains_exact_state
    (clear : Guard → Bool) (selectionFuel : Nat) (symbol : Symbol) (children : List (Value Symbol Guard))
    (state : State) (memo : Memo) :
    let built := run (makeEdge symbol top children) state.heap
    let after : State := ⟨built.2, SourceEqualityMkEdgeAllocation.emptyField state.equality⟩
    execute clear 2 selectionFuel (.bind (.topRow symbol children) Code.pure) state memo = .done built.1 after memo ∧
      SourceCurrentAllocatedMergeGraph.Run clear (.bind (.topRow symbol children) Code.pure) state memo built.1 after memo := by
  dsimp only
  have done : execute clear 2 selectionFuel (.bind (.topRow symbol children) Code.pure) state memo =
      .done (run (makeEdge symbol top children) state.heap).1
        (⟨(run (makeEdge symbol top children) state.heap).2, SourceEqualityMkEdgeAllocation.emptyField state.equality⟩ : State) memo := rfl
  exact ⟨done, SourceCurrentAllocatedMergeWorkerSound.execute_sound done⟩

end MicroCFTA.AllocatedMergeWorkerIntegration
