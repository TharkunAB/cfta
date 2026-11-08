import MicroCFTA.SourceCurrentConjunctionTuplePull

/-!
# Termination of sequential tuple demand

Each transition reduces a cursor in this relation. Operand reads can return
any finite row list. The proof does not use a heap or a row-count bound.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullProgress
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionTuplePull (Cursor Event)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

/-- These reductions include every continuation of the physical cursor. -/
inductive Next : Cursor Symbol Formula → Cursor Symbol Formula → Prop where
  | seed (node : Node) (rows : List Edge) : Next (.seedRows rows) (.seed node)
  | seedTail (edge : Edge) (rows : List Edge) : Next (.seedRows rows) (.seedRows (edge :: rows))
  | extendMore (node : Node) {inner next : Cursor Symbol Formula} (smaller : Next next inner) :
      Next (.extend node next) (.extend node inner)
  | extendYield (node : Node) {inner next : Cursor Symbol Formula} (tuple : List Edge)
      (smaller : Next next inner) : Next (.readOperand node next tuple) (.extend node inner)
  | readScan (node : Node) (inner : Cursor Symbol Formula) (tuple rows : List Edge) :
      Next (.scanOperand node inner tuple rows) (.readOperand node inner tuple)
  | readReset (node : Node) (inner : Cursor Symbol Formula) (tuple : List Edge) :
      Next (.extend node inner) (.readOperand node inner tuple)
  | scanTail (node : Node) (inner : Cursor Symbol Formula) (tuple : List Edge) (edge : Edge) (rows : List Edge) :
      Next (.scanOperand node inner tuple rows) (.scanOperand node inner tuple (edge :: rows))
  | scanReset (node : Node) (inner : Cursor Symbol Formula) (tuple rows : List Edge) :
      Next (.extend node inner) (.scanOperand node inner tuple rows)

private theorem seedRows_acc (rows : List Edge) : Acc Next (.seedRows rows) := by
  induction rows with
  | nil => exact Acc.intro _ (by intro next transition; cases transition)
  | cons edge rows ih =>
      exact Acc.intro _ (by intro next transition; cases transition; exact ih)

private theorem scan_acc (node : Node) (inner : Cursor Symbol Formula) (tuple : List Edge)
    (base : Acc Next (.extend node inner)) (rows : List Edge) : Acc Next (.scanOperand node inner tuple rows) := by
  induction rows with
  | nil =>
      apply Acc.intro
      intro next transition
      cases transition with
      | scanReset => exact base
  | cons edge rows ih =>
      apply Acc.intro
      intro next transition
      cases transition with
      | scanTail => exact ih
      | scanReset => exact base

private theorem read_acc (node : Node) (inner : Cursor Symbol Formula) (tuple : List Edge)
    (base : Acc Next (.extend node inner)) : Acc Next (.readOperand node inner tuple) := by
  apply Acc.intro
  intro next transition
  cases transition with
  | readScan _ _ _ rows => exact scan_acc node inner tuple base rows
  | readReset => exact base

private theorem extend_acc (node : Node) (inner : Cursor Symbol Formula) (base : Acc Next inner) :
    Acc Next (.extend node inner) := by
  induction base with
  | intro inner previous ih =>
      apply Acc.intro
      intro next transition
      cases transition with
      | extendMore _ smaller => exact ih _ smaller
      | extendYield _ tuple smaller => exact read_acc node _ tuple (ih _ smaller)

private theorem cursor_acc (cursor : Cursor Symbol Formula) : Acc Next cursor := by
  induction cursor with
  | empty => exact Acc.intro _ (by intro next transition; cases transition)
  | seed node =>
      exact Acc.intro _ (by intro next transition; cases transition with | seed _ rows => exact seedRows_acc rows)
  | seedRows rows => exact seedRows_acc rows
  | extend node inner ih => exact extend_acc node inner ih
  | readOperand node inner tuple ih => exact read_acc node inner tuple (extend_acc node inner ih)
  | scanOperand node inner tuple rows ih => exact scan_acc node inner tuple (extend_acc node inner ih) rows

/-- Every cursor is accessible, including cursors with arbitrary finite stored rows. -/
theorem wellFounded : WellFounded (@Next Symbol Formula) := ⟨cursor_acc⟩

/-- End has no continuation. Every other event reduces the cursor. -/
def Continues (cursor : Cursor Symbol Formula) : Event Symbol Formula → Prop
  | .more next | .yield _ next => Next next cursor
  | .ended => True

private def ProgressResult (cursor : Cursor Symbol Formula) : Outcome Symbol Formula (Event Symbol Formula) → Prop
  | .done event _ => Continues cursor event
  | .failed _ _ => True

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem step_progress (h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula) :
    ProgressResult cursor (SourceCurrentConjunctionTuplePull.step h cursor before) := by
  induction cursor generalizing before with
  | empty => trivial
  | seed node =>
      cases actual : SourceCurrentConjunctionTuplePull.expose h node before with
      | failed fault after => simp only [SourceCurrentConjunctionTuplePull.step, actual, Outcome.bind, ProgressResult]
      | done rows after =>
          simp only [SourceCurrentConjunctionTuplePull.step, actual, Outcome.bind, ProgressResult, Continues]
          exact Next.seed node rows
  | seedRows rows =>
      cases rows with
      | nil => trivial
      | cons edge rows => exact Next.seedTail edge rows
  | extend node inner ih =>
      have prior := ih before
      cases actual : SourceCurrentConjunctionTuplePull.step h inner before with
      | failed fault after => simp only [SourceCurrentConjunctionTuplePull.step, actual, Outcome.bind, ProgressResult]
      | done event after =>
          rw [actual] at prior
          simp only [SourceCurrentConjunctionTuplePull.step, actual, Outcome.bind, ProgressResult]
          cases event with
          | more next => exact Next.extendMore node prior
          | yield tuple next => exact Next.extendYield node tuple prior
          | ended => trivial
  | readOperand node inner tuple _ih =>
      cases tuple with
      | nil => exact Next.readReset node inner []
      | cons first rest =>
          cases actual : SourceCurrentConjunctionTuplePull.expose h node before with
          | failed fault after => simp only [SourceCurrentConjunctionTuplePull.step, actual, Outcome.bind, ProgressResult]
          | done rows after =>
              simp only [SourceCurrentConjunctionTuplePull.step, actual, Outcome.bind, ProgressResult, Continues]
              exact Next.readScan node inner (first :: rest) rows
  | scanOperand node inner tuple rows _ih =>
      cases tuple with
      | nil => exact Next.scanReset node inner [] rows
      | cons first rest =>
          cases rows with
          | nil => exact Next.scanReset node inner (first :: rest) []
          | cons edge rows =>
              simp only [SourceCurrentConjunctionTuplePull.step]
              split <;> (try split) <;> exact Next.scanTail node inner (first :: rest) edge rows

/-- Every actual successful transition has a strictly smaller continuation or ends. -/
theorem step_next (h : Nat) (cursor : Cursor Symbol Formula) (before after : Physical Symbol Formula)
    (event : Event Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePull.step h cursor before = .done event after) : Continues cursor event := by
  simpa only [actual, ProgressResult] using step_progress h cursor before

end MicroCFTA.SourceCurrentConjunctionTuplePullProgress
