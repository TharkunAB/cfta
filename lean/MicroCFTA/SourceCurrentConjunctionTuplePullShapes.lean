import MicroCFTA.SourceCurrentConjunctionTuplePullTotal

/-!
# Shapes of actual demanded tuples

The cursor width counts original operand positions. Duplicate operands
still occupy separate positions. Every yielded tuple is nonempty and has
one common symbol and arity. These facts follow from the actual cursor
transitions. They need no completed views or future read certificates.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullShapes
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionTuplePull (Cursor Event step expose start)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

/-- Width counts positions, while matching records the literal source filter. -/
def TupleGood (width : Nat) (tuple : List Edge) : Prop :=
  tuple.length = width ∧ SourceCurrentConjunctionTuples.Matching tuple ∧ tuple ≠ []

/-- Every retained inner tuple has the width of its own original operand fold. -/
def Aligned (width : Nat) : Cursor Symbol Formula → Prop
  | .empty => True
  | .seed _ | .seedRows _ => width = 1
  | .extend _ inner => ∃ innerWidth, width = innerWidth + 1 ∧ Aligned innerWidth inner
  | .readOperand _ inner tuple | .scanOperand _ inner tuple _ =>
      ∃ innerWidth, width = innerWidth + 1 ∧ Aligned innerWidth inner ∧ TupleGood innerWidth tuple

/-- A successful event preserves its cursor width and the yielded tuple shape. -/
def EventAligned (width : Nat) : Event Symbol Formula → Prop
  | .more next => Aligned width next
  | .yield tuple next => TupleGood width tuple ∧ Aligned width next
  | .ended => True

private def StepAligned (width : Nat) : Outcome Symbol Formula (Event Symbol Formula) → Prop
  | .done event _ => EventAligned width event
  | .failed _ _ => True

private theorem fold_aligned (nodes : List Node) (width : Nat) (cursor : Cursor Symbol Formula)
    (aligned : Aligned width cursor) : Aligned (nodes.length + width) (nodes.foldr Cursor.extend cursor) := by
  induction nodes with
  | nil => simpa only [List.length_nil, List.foldr_nil, Nat.zero_add] using aligned
  | cons node nodes ih =>
      refine ⟨nodes.length + width, ?_, ih⟩
      simp only [List.length_cons]
      omega

/-- Initialization counts all original positions, including equal operands. -/
theorem start_aligned (nodes : List Node) : Aligned nodes.length (start nodes) := by
  cases nodes with
  | nil => trivial
  | cons first rest =>
      simpa only [start, List.length_cons] using fold_aligned rest 1 (.seed first) rfl

private theorem matching_cons (edge first : Edge) (rest : List Edge)
    (matched : SourceCurrentConjunctionTuples.Matching (first :: rest))
    (symbol : edge.entry.key.symbol = first.entry.key.symbol)
    (arity : edge.children.length = first.children.length) :
    SourceCurrentConjunctionTuples.Matching (edge :: first :: rest) := by
  have same : SourceCurrentConjunctionTuples.shape edge = SourceCurrentConjunctionTuples.shape first :=
    Prod.ext symbol arity
  have pair := List.pairwise_cons.mp matched
  apply List.pairwise_cons.mpr
  refine ⟨?_, matched⟩
  intro other member
  rcases List.mem_cons.mp member with rfl | member
  · exact same
  · exact same.trans (pair.1 other member)

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem step_shapes (h width : Nat) (cursor : Cursor Symbol Formula)
    (before : Physical Symbol Formula) (aligned : Aligned width cursor) :
    StepAligned width (step h cursor before) := by
  induction cursor generalizing width before with
  | empty => trivial
  | seed node =>
      cases actual : expose h node before with
      | failed fault after => simp only [step, actual, Outcome.bind, StepAligned]
      | done rows after =>
          simpa only [step, actual, Outcome.bind, StepAligned, EventAligned, Aligned] using aligned
  | seedRows rows =>
      cases rows with
      | nil => trivial
      | cons edge rows =>
          refine ⟨?_, aligned⟩
          exact ⟨by simpa only [List.length_singleton] using aligned.symm,
            by simp [SourceCurrentConjunctionTuples.Matching], by simp⟩
  | extend node inner ih =>
      rcases aligned with ⟨innerWidth, rfl, prior⟩
      have first := ih innerWidth before prior
      cases actual : step h inner before with
      | failed fault after => simp only [step, actual, Outcome.bind, StepAligned]
      | done event after =>
          rw [actual] at first
          cases event with
          | ended => simp only [step, actual, Outcome.bind, StepAligned, EventAligned]
          | more next =>
              simp only [step, actual, Outcome.bind, StepAligned, EventAligned]
              exact ⟨innerWidth, rfl, first⟩
          | yield tuple next =>
              simp only [step, actual, Outcome.bind, StepAligned, EventAligned]
              exact ⟨innerWidth, rfl, first.2, first.1⟩
  | readOperand node inner tuple _ih =>
      rcases aligned with ⟨innerWidth, rfl, prior, length, matched, nonempty⟩
      cases tuple with
      | nil => exact False.elim (nonempty rfl)
      | cons first rest =>
          cases actual : expose h node before with
          | failed fault after => simp only [step, actual, Outcome.bind, StepAligned]
          | done rows after =>
              simp only [step, actual, Outcome.bind, StepAligned, EventAligned]
              exact ⟨innerWidth, rfl, prior, length, matched, nonempty⟩
  | scanOperand node inner tuple remaining _ih =>
      rcases aligned with ⟨innerWidth, rfl, prior, length, matched, nonempty⟩
      cases tuple with
      | nil => exact False.elim (nonempty rfl)
      | cons first rest =>
          cases remaining with
          | nil => exact ⟨innerWidth, rfl, prior⟩
          | cons edge rows =>
              have next : Aligned (innerWidth + 1) (.scanOperand node inner (first :: rest) rows) :=
                ⟨innerWidth, rfl, prior, length, matched, nonempty⟩
              simp only [step]
              split
              · rename_i symbol
                split
                · rename_i arity
                  exact ⟨⟨by simpa only [List.length_cons] using congrArg Nat.succ length,
                    matching_cons edge first rest matched symbol arity, by simp⟩, next⟩
                · exact next
              · exact next

/-- Each actual yielded tuple has original position width and one common symbol and arity. -/
theorem step_aligned (h width : Nat) (cursor : Cursor Symbol Formula)
    (before after : Physical Symbol Formula) (event : Event Symbol Formula)
    (aligned : Aligned width cursor) (actual : step h cursor before = .done event after) :
    EventAligned width event := by
  simpa only [actual, StepAligned] using step_shapes h width cursor before aligned

/-- Every tuple in an accumulated sample has the original position width and source shape. -/
def TuplesGood (width : Nat) (tuples : List (List Edge)) : Prop :=
  ∀ tuple ∈ tuples, TupleGood width tuple

private def StatusAligned (width : Nat) : SourceCurrentConjunctionTuplePullAdmission.Status Symbol Formula → Prop
  | .running cursor tuples | .overflow tuples cursor => Aligned width cursor ∧ TuplesGood width tuples
  | .fit tuples => TuplesGood width tuples

private def SampleAligned (width : Nat) :
    Outcome Symbol Formula (SourceCurrentConjunctionTuplePullAdmission.Status Symbol Formula) → Prop
  | .done status _ => StatusAligned width status
  | .failed _ _ => True

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem append_good (width : Nat) (tuples : List (List Edge)) (tuple : List Edge)
    (prior : TuplesGood width tuples) (own : TupleGood width tuple) :
    TuplesGood width (tuples ++ [tuple]) := by
  intro selected member
  rcases List.mem_append.mp member with member | member
  · exact prior selected member
  · simpa only [List.mem_singleton.mp member] using own

private theorem advance_shapes (h budget width : Nat) (cursor : Cursor Symbol Formula)
    (tuples : List (List Edge)) (before : Physical Symbol Formula)
    (aligned : Aligned width cursor) (prior : TuplesGood width tuples) :
    SampleAligned width (SourceCurrentConjunctionTuplePullAdmission.advance h budget cursor tuples before) := by
  have first := step_shapes h width cursor before aligned
  cases actual : step h cursor before with
  | failed fault after =>
      simp only [SourceCurrentConjunctionTuplePullAdmission.advance, actual, Outcome.bind, SampleAligned]
  | done event after =>
      rw [actual] at first
      cases event with
      | ended =>
          simpa only [SourceCurrentConjunctionTuplePullAdmission.advance, actual, Outcome.bind,
            SampleAligned, StatusAligned] using prior
      | more next =>
          simpa only [SourceCurrentConjunctionTuplePullAdmission.advance, actual, Outcome.bind,
            SampleAligned, StatusAligned, StepAligned, EventAligned] using And.intro first prior
      | yield tuple next =>
          have sampled := append_good width tuples tuple prior first.1
          simp only [SourceCurrentConjunctionTuplePullAdmission.advance, actual, Outcome.bind]
          split <;> exact ⟨first.2, sampled⟩

private theorem drive_shapes (steps h budget width : Nat) (cursor : Cursor Symbol Formula)
    (tuples : List (List Edge)) (before : Physical Symbol Formula)
    (aligned : Aligned width cursor) (prior : TuplesGood width tuples) :
    SampleAligned width (SourceCurrentConjunctionTuplePullAdmission.drive steps h budget cursor tuples before) := by
  induction steps generalizing cursor tuples before with
  | zero => exact ⟨aligned, prior⟩
  | succ steps ih =>
      have first := advance_shapes h budget width cursor tuples before aligned prior
      cases actual : SourceCurrentConjunctionTuplePullAdmission.advance h budget cursor tuples before with
      | failed fault after =>
          simp only [SourceCurrentConjunctionTuplePullAdmission.drive, actual, Outcome.bind, SampleAligned]
      | done status after =>
          rw [actual] at first
          cases status with
          | running next sampled =>
              simpa only [SourceCurrentConjunctionTuplePullAdmission.drive, actual, Outcome.bind] using
                ih next sampled after first.1 first.2
          | fit sampled =>
              simpa only [SourceCurrentConjunctionTuplePullAdmission.drive, actual, Outcome.bind] using first
          | overflow sampled next =>
              simpa only [SourceCurrentConjunctionTuplePullAdmission.drive, actual, Outcome.bind] using first

private theorem total_shapes (h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula) :
    SampleAligned nodes.length
      (SourceCurrentConjunctionTuplePullTotal.observe
        (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before)) := by
  obtain ⟨steps, observed⟩ := SourceCurrentConjunctionTuplePullTotal.sample_observation h budget nodes before
  have bounded := drive_shapes steps h budget nodes.length (start nodes) [] before (start_aligned nodes)
    (by intro tuple member; cases member)
  have actual := observed 0
  simp only [Nat.add_zero, SourceCurrentConjunctionTuplePullAdmission.sample] at actual
  rw [actual] at bounded
  exact bounded

/-- A completed fitting total sample retains every original operand position. -/
theorem sample_fit (h budget : Nat) (nodes : List Node) (before after : Physical Symbol Formula)
    (tuples : List (List Edge))
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done (.fit tuples) after) :
    ∀ tuple ∈ tuples, tuple.length = nodes.length ∧ SourceCurrentConjunctionTuples.Matching tuple ∧ tuple ≠ [] := by
  simpa only [actual, SourceCurrentConjunctionTuplePullTotal.observe,
    SourceCurrentConjunctionTuplePullTotal.Result.toStatus, SampleAligned, StatusAligned, TuplesGood, TupleGood]
    using total_shapes h budget nodes before

/-- Overflow tuples retain the same position count, and the unforced cursor stays aligned. -/
theorem sample_overflow (h budget : Nat) (nodes : List Node) (before after : Physical Symbol Formula)
    (tuples : List (List Edge)) (next : Cursor Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done (.overflow tuples next) after) :
    Aligned nodes.length next ∧
      ∀ tuple ∈ tuples, tuple.length = nodes.length ∧ SourceCurrentConjunctionTuples.Matching tuple ∧ tuple ≠ [] := by
  simpa only [actual, SourceCurrentConjunctionTuplePullTotal.observe,
    SourceCurrentConjunctionTuplePullTotal.Result.toStatus, SampleAligned, StatusAligned, TuplesGood, TupleGood]
    using total_shapes h budget nodes before

end MicroCFTA.SourceCurrentConjunctionTuplePullShapes
