import MicroCFTA.SourceCurrentAllocatedMergeGraph

/-!
# Bounded merge execution with actual equality allocation

Every instruction retains the returned constructor heap, equality state,
and completed merge table. A Top row allocates its empty field at the
current operations before it constructs the raw edge. Only completed
stages execute their continuations. This is the graph's serial schedule;
it does not identify host forcing or pending memo publication.
-/
namespace MicroCFTA.SourceCurrentAllocatedMergeWorker
open InternedConstructorTemplates
open SourceCurrentAllocatedMergeGraph (Code State Memo top body)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Selection failures retain their exact source comparison reason. -/
abbrev Fault := MergedSourceComparison.Fault

/-- Completed and failed observations retain the full allocated state and merge table. -/
inductive Outcome (Output : Type) where
  | done (output : Output) (state : State) (memo : Memo)
  | failed (fault : Fault) (state : State) (memo : Memo)

def Outcome.state : Outcome Output → State
  | .done _ state _ | .failed _ state _ => state

def Outcome.memo : Outcome Output → Memo
  | .done _ _ memo | .failed _ _ memo => memo

/-- Failures stop at the literal returned state without entering the continuation. -/
def Outcome.bind (first : Outcome Input) (next : Input → State → Memo → Outcome Output) : Outcome Output :=
  match first with
  | .done value state memo => next value state memo
  | .failed fault state memo => .failed fault state memo

mutual
  /-- Interpret actual allocated instructions with separate work and comparison bounds. -/
  def execute [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
      (clear : Guard → Bool) : Nat → Nat → Code Output → State → Memo → Outcome Output
    | 0, _, _, state, memo => .failed .exhausted state memo
    | remaining + 1, selectionFuel, code, state, memo =>
        match code with
        | .pure value => .done value state memo
        | .work job =>
            let actual := run job state.heap
            .done actual.1 ⟨actual.2, state.equality⟩ memo
        | .topRow symbol children =>
            let operations := SourceEqualityMkEdgeAllocation.emptyField state.equality
            let actual := run (makeEdge symbol top children) state.heap
            .done actual.1 ⟨actual.2, operations⟩ memo
        | .select inputs =>
            match SourceMergedSelection.select clear selectionFuel inputs state.heap with
            | .done values heap => .done values ⟨heap, state.equality⟩ memo
            | .failed fault heap => .failed fault ⟨heap, state.equality⟩ memo
        | .request input => call clear remaining selectionFuel input state memo
        | .bind first next =>
            (execute clear remaining selectionFuel first state memo).bind fun value after saved =>
              execute clear remaining selectionFuel (next value) after saved

  /-- A miss executes its actual body and then rereads the retained first completed winner. -/
  def call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
      (clear : Guard → Bool) : Nat → Nat → Value Symbol Guard → State → Memo → Outcome (Value Symbol Guard)
    | 0, _, _, state, memo => .failed .exhausted state memo
    | remaining + 1, selectionFuel, input, state, memo =>
        match memo input.referenceOf with
        | some entry => .done entry.result state memo
        | none =>
            (execute clear remaining selectionFuel (body input) state memo).bind fun candidate after current =>
              .done (SourceCurrentMemoMergeGraph.winner current input candidate).result after
                (SourceCurrentMemoMergeGraph.remember current input candidate)
end

/-- Zero work fuel stops before request lookup and retains every initial component. -/
theorem call_zero [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (selectionFuel : Nat) (input : Value Symbol Guard) (state : State) (memo : Memo) :
    call clear 0 selectionFuel input state memo = .failed .exhausted state memo := rfl

/-- A successor-bound completed hit needs no body fuel and performs no allocation. -/
theorem call_hit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (remaining selectionFuel : Nat) (input : Value Symbol Guard) (state : State) (memo : Memo)
    (entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard) (found : memo input.referenceOf = some entry) :
    call clear (remaining + 1) selectionFuel input state memo = .done entry.result state memo := by
  simp only [call, found]

/-- Only the actual completed miss body can reach the first-writer reread. -/
theorem call_miss [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (remaining selectionFuel : Nat) (input : Value Symbol Guard) (state : State) (memo : Memo)
    (absent : memo input.referenceOf = none) :
    call clear (remaining + 1) selectionFuel input state memo =
      (execute clear remaining selectionFuel (body input) state memo).bind fun candidate after current =>
        .done (SourceCurrentMemoMergeGraph.winner current input candidate).result after
          (SourceCurrentMemoMergeGraph.remember current input candidate) := by
  simp only [call, absent]

/-- Top construction performs the literal empty-field allocation at the reached operation state. -/
theorem topRow_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (remaining selectionFuel : Nat) (symbol : Symbol) (children : List (Value Symbol Guard))
    (state : State) (memo : Memo) :
    execute clear (remaining + 1) selectionFuel (.topRow symbol children) state memo =
      .done (run (makeEdge symbol top children) state.heap).1
        ⟨(run (makeEdge symbol top children) state.heap).2, SourceEqualityMkEdgeAllocation.emptyField state.equality⟩ memo := rfl

end MicroCFTA.SourceCurrentAllocatedMergeWorker
