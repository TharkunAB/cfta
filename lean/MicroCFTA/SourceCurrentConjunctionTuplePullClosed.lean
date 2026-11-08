import MicroCFTA.SourceCurrentConjunctionTuplePullEffects
import MicroCFTA.SourceCurrentConjunctionTuplePullProgress
import MicroCFTA.SourceEqualityProjectionRead

/-!
# Closed inputs and retained rows of the physical cursor

Closed operands justify demanded reads. Closed retained rows justify the
later tuple worker. The predicates are separate. Only an actual successful
singleton read supplies new closed rows. A read failure retains the existing
physical outcome and has no returned-row assertion.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullClosed
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionTuplePull (Cursor Event step expose start)
open SourceCurrentConjunctionTuplePullEffects (Inputs)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

/-- Every operand that can still be demanded has no free reference. -/
def ClosedOperands : Cursor Symbol Formula → Prop
  | .empty | .seedRows _ => True
  | .seed node => node.free = []
  | .extend node inner | .readOperand node inner _ | .scanOperand node inner _ _ =>
      node.free = [] ∧ ClosedOperands inner

/-- Every row retained by the cursor has closed children. -/
def ClosedRows : Cursor Symbol Formula → Prop
  | .empty | .seed _ => True
  | .seedRows rows => ClosedEdges rows
  | .extend _ inner => ClosedRows inner
  | .readOperand _ inner tuple => ClosedRows inner ∧ ClosedEdges tuple
  | .scanOperand _ inner tuple remaining => ClosedRows inner ∧ ClosedEdges tuple ∧ ClosedEdges remaining

/-- Successful events retain closed operands, retained rows, and any yielded tuple. -/
def EventClosed : Event Symbol Formula → Prop
  | .more next => ClosedOperands next ∧ ClosedRows next
  | .yield tuple next => ClosedEdges tuple ∧ ClosedOperands next ∧ ClosedRows next
  | .ended => True

/-- Each syntactic continuation retains the original closed-operand condition. -/
theorem next_closed {cursor next : Cursor Symbol Formula}
    (actual : SourceCurrentConjunctionTuplePullProgress.Next next cursor)
    (closed : ClosedOperands cursor) : ClosedOperands next := by
  revert closed
  induction actual with
  | seed | seedTail => intro _; trivial
  | extendMore _ _ ih => intro closed; exact ⟨closed.1, ih closed.2⟩
  | extendYield _ _ _ ih => intro closed; exact ⟨closed.1, ih closed.2⟩
  | readScan | readReset | scanTail | scanReset => intro closed; exact closed

private theorem fold_closed (nodes : List Node) (cursor : Cursor Symbol Formula)
    (base : ClosedOperands cursor) (closed : ClosedValues nodes) :
    ClosedOperands (nodes.foldr Cursor.extend cursor) := by
  revert closed
  induction nodes with
  | nil => intro _; exact base
  | cons node nodes ih =>
      intro closed
      exact ⟨closed node List.mem_cons_self, ih (fun node member => closed node (List.mem_cons_of_mem _ member))⟩

/-- The original closed input list derives every suspended operand premise. -/
theorem start_closed (nodes : List Node) (closed : ClosedValues nodes) : ClosedOperands (start nodes) := by
  cases nodes with
  | nil => trivial
  | cons first rest =>
      exact fold_closed rest (.seed first) (closed first List.mem_cons_self)
        (fun node member => closed node (List.mem_cons_of_mem _ member))

private theorem fold_rows (nodes : List Node) (cursor : Cursor Symbol Formula)
    (rows : ClosedRows cursor) : ClosedRows (nodes.foldr Cursor.extend cursor) := by
  induction nodes with
  | nil => exact rows
  | cons _ _ ih => exact ih

/-- Initialization has no retained-row obligation. -/
theorem start_rows (nodes : List Node) : ClosedRows (start nodes) := by
  cases nodes with
  | nil => trivial
  | cons first rest => exact fold_rows rest (.seed first) trivial

private def EventRows : Event Symbol Formula → Prop
  | .more next => ClosedRows next
  | .yield tuple next => ClosedEdges tuple ∧ ClosedRows next
  | .ended => True

private def ReturnedRows : Outcome Symbol Formula (Event Symbol Formula) → Prop
  | .done event _ => EventRows event
  | .failed _ _ => True

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

omit [DecidableEq Symbol] in
/-- An actual successful demanded read derives closed children from its original operand. -/
theorem expose_closed (h : Nat) (node : Node) (before after : Physical Symbol Formula) (rows : List Edge)
    (actual : expose h node before = .done rows after) (ready : Ready before)
    (available : Available before.heap node) (closed : node.free = []) : ClosedEdges rows := by
  have read : SourceEqualityProjectionRead.Read node before.heap rows after.heap := by
    cases observed : MergedFreshOrdinaryExposure.nodeEdges h node before.heap <;>
      simp only [expose, SourceCurrentConjunctionRowsWorker.exposures, observed, Outcome.bind,
        List.headD_cons] at actual <;> cases actual
    exact .done h observed
  exact (read.verified ready.semantic available closed).2.2.2

private theorem step_rows (h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula)
    (ready : Ready before) (inputs : Inputs before.heap cursor)
    (operands : ClosedOperands cursor) (rows : ClosedRows cursor) : ReturnedRows (step h cursor before) := by
  induction cursor generalizing before with
  | empty => trivial
  | seed node =>
      cases actual : expose h node before with
      | failed fault after => simp only [step, actual, Outcome.bind, ReturnedRows]
      | done selected after =>
          simp only [step, actual, Outcome.bind, ReturnedRows, EventRows, ClosedRows]
          exact expose_closed h node before after selected actual ready inputs operands
  | seedRows selected =>
      cases selected with
      | nil => trivial
      | cons edge rest =>
          refine ⟨?_, ?_⟩
          · intro selected member
            simpa only [List.mem_singleton.mp member] using rows edge List.mem_cons_self
          · exact fun selected member => rows selected (List.mem_cons_of_mem _ member)
  | extend node inner ih =>
      have prior := ih before ready inputs.2 operands.2 rows
      cases actual : step h inner before with
      | failed fault after => simp only [step, actual, Outcome.bind, ReturnedRows]
      | done event after =>
          rw [actual] at prior
          cases event with
          | ended => simp only [step, actual, Outcome.bind, ReturnedRows, EventRows]
          | more next =>
              simpa only [step, actual, Outcome.bind, ReturnedRows, EventRows, ClosedRows] using prior
          | yield tuple next =>
              simp only [step, actual, Outcome.bind, ReturnedRows, EventRows, ClosedRows]
              exact ⟨prior.2, prior.1⟩
  | readOperand node inner tuple _ih =>
      cases tuple with
      | nil => exact rows.1
      | cons first rest =>
          cases actual : expose h node before with
          | failed fault after => simp only [step, actual, Outcome.bind, ReturnedRows]
          | done selected after =>
              simp only [step, actual, Outcome.bind, ReturnedRows, EventRows, ClosedRows]
              exact ⟨rows.1, rows.2, expose_closed h node before after selected actual ready inputs.1 operands.1⟩
  | scanOperand node inner tuple remaining _ih =>
      cases tuple with
      | nil => exact rows.1
      | cons first rest =>
          cases remaining with
          | nil => exact rows.1
          | cons edge more =>
              have continued : ClosedRows (.scanOperand node inner (first :: rest) more) :=
                ⟨rows.1, rows.2.1, fun selected member => rows.2.2 selected (List.mem_cons_of_mem _ member)⟩
              have yielded : ClosedEdges (edge :: first :: rest) := by
                intro selected member
                rcases List.mem_cons.mp member with same | member
                · rw [same]
                  exact rows.2.2 edge List.mem_cons_self
                · exact rows.2.1 selected member
              simp only [step]
              split
              · split
                · exact ⟨yielded, continued⟩
                · exact continued
              · exact continued

/-- An actual successful transition returns closed tuple children and a closed continuation. -/
theorem step_closed (h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula)
    (ready : Ready before) (inputs : Inputs before.heap cursor)
    (operands : ClosedOperands cursor) (rows : ClosedRows cursor)
    (event : Event Symbol Formula) (after : Physical Symbol Formula)
    (actual : step h cursor before = .done event after) : EventClosed event := by
  have retained := step_rows h cursor before ready inputs operands rows
  rw [actual] at retained
  cases event with
  | ended => trivial
  | more next =>
      exact ⟨next_closed (SourceCurrentConjunctionTuplePullProgress.step_next h cursor before after (.more next) actual)
        operands, retained⟩
  | yield tuple next =>
      exact ⟨retained.1, next_closed (SourceCurrentConjunctionTuplePullProgress.step_next h cursor before after
        (.yield tuple next) actual) operands, retained.2⟩

end MicroCFTA.SourceCurrentConjunctionTuplePullClosed
