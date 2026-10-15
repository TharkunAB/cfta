import MicroCFTA.SourceCurrentMemoMergeGraph

/-!
# Executable completed memo-aware merging

The interpreter runs the literal Code and threads its completed result
table. A hit skips the body. A miss runs the recursive body, records the
first winner, and rereads that winner. Work fuel bounds instruction and
request expansion. Selection fuel bounds every actual comparison. Failures
retain the reached heap and completed table. This is not a pending-table
or delayed-runtime interpreter.
-/
namespace MicroCFTA.SourceCurrentMemoMergeWorker
open InternedConstructorTemplates SourceCurrentMemoMergeGraph
open MergedSourceComparison (Fault)

/-- Every observation retains the exact constructor heap and completed result table. -/
inductive Outcome (Symbol Guard Output : Type) where
  | done (output : Output) (heap : State Symbol Guard) (memo : Memo Symbol Guard)
  | failed (fault : Fault) (heap : State Symbol Guard) (memo : Memo Symbol Guard)

def Outcome.heap : Outcome Symbol Guard Output → State Symbol Guard
  | .done _ heap _ | .failed _ heap _ => heap

def Outcome.memo : Outcome Symbol Guard Output → Memo Symbol Guard
  | .done _ _ memo | .failed _ _ memo => memo

/-- A failed prefix retains its observation and does not execute its continuation. -/
def Outcome.bind (first : Outcome Symbol Guard Input)
    (next : Input → State Symbol Guard → Memo Symbol Guard → Outcome Symbol Guard Output) :
    Outcome Symbol Guard Output :=
  match first with
  | .done value heap memo => next value heap memo
  | .failed fault heap memo => .failed fault heap memo

mutual
  /-- Interpret actual instructions with one shared comparison bound and the reached table. -/
  def execute [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
      (clear : Guard → Bool) (top : Guard) : Nat → Nat → Code Symbol Guard Output →
        State Symbol Guard → Memo Symbol Guard → Outcome Symbol Guard Output
    | 0, _, _, heap, memo => .failed .exhausted heap memo
    | remaining + 1, selectionFuel, code, heap, memo =>
        match code with
        | .pure value => .done value heap memo
        | .work job =>
            let actual := run job heap
            .done actual.1 actual.2 memo
        | .select inputs =>
            match SourceMergedSelection.select clear selectionFuel inputs heap with
            | .done values after => .done values after memo
            | .failed fault after => .failed fault after memo
        | .request input => call clear top remaining selectionFuel input heap memo
        | .bind first next =>
            (execute clear top remaining selectionFuel first heap memo).bind fun value after saved =>
              execute clear top remaining selectionFuel (next value) after saved

  /-- A miss interprets the memo-aware body and returns the actual first-writer reread. -/
  def call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
      (clear : Guard → Bool) (top : Guard) : Nat → Nat → Value Symbol Guard →
        State Symbol Guard → Memo Symbol Guard → Outcome Symbol Guard (Value Symbol Guard)
    | 0, _, _, heap, memo => .failed .exhausted heap memo
    | remaining + 1, selectionFuel, input, heap, memo =>
        match memo input.referenceOf with
        | some entry => .done entry.result heap memo
        | none =>
            (execute clear top remaining selectionFuel (body top input) heap memo).bind fun candidate after current =>
              .done (winner current input candidate).result after (remember current input candidate)
end

/-- A returned table hit bypasses every body instruction and comparison. -/
theorem call_hit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (remaining selectionFuel : Nat)
    (input : Value Symbol Guard) (heap : State Symbol Guard) (memo : Memo Symbol Guard)
    (entry : Entry Symbol Guard) (found : memo input.referenceOf = some entry) :
    call clear top (remaining + 1) selectionFuel input heap memo = .done entry.result heap memo := by
  simp only [call, found]

/-- A miss preserves failures and completes only after its actual body returns. -/
theorem call_miss [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (remaining selectionFuel : Nat)
    (input : Value Symbol Guard) (heap : State Symbol Guard) (memo : Memo Symbol Guard)
    (absent : memo input.referenceOf = none) :
    call clear top (remaining + 1) selectionFuel input heap memo =
      (execute clear top remaining selectionFuel (body top input) heap memo).bind fun candidate after current =>
        .done (winner current input candidate).result after (remember current input candidate) := by
  simp only [call, absent]

end MicroCFTA.SourceCurrentMemoMergeWorker
