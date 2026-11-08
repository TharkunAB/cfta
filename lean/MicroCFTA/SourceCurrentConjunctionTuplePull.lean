import MicroCFTA.SourceCurrentConjunctionRowsWorker
import MicroCFTA.SourceCurrentConjunctionTuples

/-!
# Suspended physical demand for conjunction tuples

The cursor follows the source `foldr extend` order. An extension requests
its operand only after its inner cursor returns a nonempty tuple. It starts
that operand scan again for each inner tuple. A yield retains its unforced
continuation. Every exposure uses the existing physical singleton worker.

These transitions specify sequential source demand. They do not count GHC
evaluation steps or specify a global unsafe allocation schedule. An exposure
is still the existing complete operand view. Lazy processing and sharing of
the later requirement rows remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePull
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome Fault)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

/-- The cursor stores only operands and rows reached by previous transitions. -/
inductive Cursor (Symbol Formula : Type) where
  | empty
  | seed (node : Value Symbol (SourceSymbolicIndex.Constraint Formula))
  | seedRows (rows : List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula)))
  | extend (node : Value Symbol (SourceSymbolicIndex.Constraint Formula)) (inner : Cursor Symbol Formula)
  | readOperand (node : Value Symbol (SourceSymbolicIndex.Constraint Formula)) (inner : Cursor Symbol Formula)
      (tuple : List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula)))
  | scanOperand (node : Value Symbol (SourceSymbolicIndex.Constraint Formula)) (inner : Cursor Symbol Formula)
      (tuple remaining : List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula)))

/-- A transition can suspend, yield one raw tuple, or report the end. -/
inductive Event (Symbol Formula : Type) where
  | more (next : Cursor Symbol Formula)
  | yield (tuple : List (EdgeValue Symbol (SourceSymbolicIndex.Constraint Formula))) (next : Cursor Symbol Formula)
  | ended

/-- Construct the literal source fold without reading any operand. -/
def start : List Node → Cursor Symbol Formula
  | [] => .empty
  | first :: rest => rest.foldr Cursor.extend (.seed first)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Run the existing singleton exposure and retain its actual physical outcome. -/
def expose (h : Nat) (node : Node) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (List Edge) :=
  (SourceCurrentConjunctionRowsWorker.exposures h [node] before).bind fun rows after =>
    .done (rows.headD []) after

/-- Perform one sequential demand transition. A yield does not step its continuation. -/
def step (h : Nat) : Cursor Symbol Formula → Physical Symbol Formula → Outcome Symbol Formula (Event Symbol Formula)
  | .empty, before => .done .ended before
  | .seed node, before => (expose h node before).bind fun rows after => .done (.more (.seedRows rows)) after
  | .seedRows [], before => .done .ended before
  | .seedRows (edge :: rows), before => .done (.yield [edge] (.seedRows rows)) before
  | .extend node inner, before =>
      (step h inner before).bind fun event after => match event with
        | .more next => .done (.more (.extend node next)) after
        | .yield tuple next => .done (.more (.readOperand node next tuple)) after
        | .ended => .done .ended after
  | .readOperand node inner [], before => .done (.more (.extend node inner)) before
  | .readOperand node inner (first :: rest), before =>
      (expose h node before).bind fun rows after =>
        .done (.more (.scanOperand node inner (first :: rest) rows)) after
  | .scanOperand node inner [] _, before => .done (.more (.extend node inner)) before
  | .scanOperand node inner (_ :: _) [], before => .done (.more (.extend node inner)) before
  | .scanOperand node inner (first :: rest) (edge :: rows), before =>
      if edge.entry.key.symbol = first.entry.key.symbol then
        if edge.children.length = first.children.length then
          .done (.yield (edge :: first :: rest) (.scanOperand node inner (first :: rest) rows)) before
        else .done (.more (.scanOperand node inner (first :: rest) rows)) before
      else .done (.more (.scanOperand node inner (first :: rest) rows)) before

omit [DecidableEq Symbol] in
/-- A successful source singleton read is the cursor's exact exposure. -/
theorem expose_done (h : Nat) (node : Node) (before after : Physical Symbol Formula) (rows : List Edge)
    (actual : SourceCurrentConjunctionRowsWorker.exposures h [node] before = .done [rows] after) :
    expose h node before = .done rows after := by
  simp only [expose, actual, Outcome.bind, List.headD_cons]

omit [DecidableEq Symbol] in
/-- Exposure failure retains the existing fault and exact reached state. -/
theorem expose_failed (h : Nat) (node : Node) (before after : Physical Symbol Formula) (fault : Fault)
    (actual : SourceCurrentConjunctionRowsWorker.exposures h [node] before = .failed fault after) :
    expose h node before = .failed fault after := by
  simp only [expose, actual, Outcome.bind]

omit [DecidableEq Symbol] in
/-- No tuple demand changes the equality-operation cache. -/
theorem expose_equality (h : Nat) (node : Node) (before : Physical Symbol Formula) :
    (expose h node before).state.equality = before.equality := by
  unfold expose
  cases actual : MergedFreshOrdinaryExposure.nodeEdges h node before.heap <;>
    simp only [SourceCurrentConjunctionRowsWorker.exposures, actual, Outcome.bind, Outcome.state]

/-- Every completed or failed transition retains the original equality cache. -/
theorem step_equality (h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula) :
    (step h cursor before).state.equality = before.equality := by
  induction cursor generalizing before with
  | empty => rfl
  | seed node =>
      have same := expose_equality h node before
      cases actual : expose h node before <;> simpa only [step, actual, Outcome.bind, Outcome.state] using same
  | seedRows rows => cases rows <;> rfl
  | extend node inner ih =>
      have same := ih before
      cases actual : step h inner before with
      | failed fault after => simpa only [step, actual, Outcome.bind, Outcome.state] using same
      | done event after =>
          cases event <;> simpa only [step, actual, Outcome.bind, Outcome.state] using same
  | readOperand node inner tuple _ih =>
      cases tuple with
      | nil => rfl
      | cons first rest =>
          have same := expose_equality h node before
          cases actual : expose h node before <;> simpa only [step, actual, Outcome.bind, Outcome.state] using same
  | scanOperand node inner tuple rows _ih =>
      cases tuple with
      | nil => rfl
      | cons first rest =>
          cases rows with
          | nil => rfl
          | cons edge rows => simp only [step]; split <;> (try split) <;> rfl

/-- An exhausted inner stream does not read this operand. -/
theorem extend_end (h : Nat) (node : Node) (inner : Cursor Symbol Formula)
    (before after : Physical Symbol Formula) (actual : step h inner before = .done .ended after) :
    step h (.extend node inner) before = .done .ended after := by
  simp only [step, actual, Outcome.bind]

/-- An inner yield suspends this operand read until the next transition. -/
theorem extend_yield (h : Nat) (node : Node) (inner next : Cursor Symbol Formula) (tuple : List Edge)
    (before after : Physical Symbol Formula) (actual : step h inner before = .done (.yield tuple next) after) :
    step h (.extend node inner) before = .done (.more (.readOperand node next tuple)) after := by
  simp only [step, actual, Outcome.bind]

/-- Matching tests use the source symbol and arity, and retain the literal remaining scan. -/
theorem scan_yield (h : Nat) (node : Node) (inner : Cursor Symbol Formula) (first edge : Edge)
    (rest rows : List Edge) (before : Physical Symbol Formula)
    (symbol : edge.entry.key.symbol = first.entry.key.symbol) (arity : edge.children.length = first.children.length) :
    step h (.scanOperand node inner (first :: rest) (edge :: rows)) before =
      .done (.yield (edge :: first :: rest) (.scanOperand node inner (first :: rest) rows)) before := by
  simp only [step, symbol, arity, ite_true]

/-- A finished operand scan restarts the extension at the actual inner continuation. -/
theorem scan_end (h : Nat) (node : Node) (inner : Cursor Symbol Formula) (first : Edge) (rest : List Edge)
    (before : Physical Symbol Formula) :
    step h (.scanOperand node inner (first :: rest) []) before = .done (.more (.extend node inner)) before := rfl

omit [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
/-- A mathematical readback observes views; execution never receives this function. -/
def denote (views : Node → List Edge) : Cursor Symbol Formula → List (List Edge)
  | .empty => []
  | .seed node => (views node).map fun edge => [edge]
  | .seedRows rows => rows.map fun edge => [edge]
  | .extend node inner => SourceCurrentConjunctionTuples.extend (views node) (denote views inner)
  | .readOperand node inner tuple =>
      SourceCurrentConjunctionTuples.extend (views node) [tuple] ++
        SourceCurrentConjunctionTuples.extend (views node) (denote views inner)
  | .scanOperand node inner tuple rows =>
      SourceCurrentConjunctionTuples.extend rows [tuple] ++
        SourceCurrentConjunctionTuples.extend (views node) (denote views inner)

omit [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
private theorem denote_fold (views : Node → List Edge) (nodes : List Node) (cursor : Cursor Symbol Formula) :
    denote views (nodes.foldr Cursor.extend cursor) =
      (nodes.map views).foldr SourceCurrentConjunctionTuples.extend (denote views cursor) := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih => simp only [List.foldr_cons, List.map_cons, denote, ih]

omit [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
/-- Cursor initialization has the exact source fold, order, and multiplicity. -/
theorem start_order (views : Node → List Edge) (nodes : List Node) :
    denote views (start nodes) = SourceCurrentConjunctionTuples.tuples (nodes.map views) := by
  cases nodes with
  | nil => rfl
  | cons first rest =>
      simpa only [start, List.map_cons, SourceCurrentConjunctionTuples.tuples, denote] using
        denote_fold views rest (.seed first)

/-- Readback only constrains the operand that this transition actually demands. -/
def ReadAgreement (h : Nat) (views : Node → List Edge) :
    Cursor Symbol Formula → Physical Symbol Formula → Prop
  | .seed node, before => ∀ rows after, expose h node before = .done rows after → views node = rows
  | .extend _ inner, before => ReadAgreement h views inner before
  | .readOperand node _ (_ :: _), before =>
      ∀ rows after, expose h node before = .done rows after → views node = rows
  | _, _ => True

omit [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))] in
/-- A transition retains the ordered suffix or removes exactly its yielded head. -/
def Ordered (views : Node → List Edge) (cursor : Cursor Symbol Formula) : Event Symbol Formula → Prop
  | .more next => denote views cursor = denote views next
  | .yield tuple next => denote views cursor = tuple :: denote views next
  | .ended => denote views cursor = []

private def OrderedResult (views : Node → List Edge) (cursor : Cursor Symbol Formula) :
    Outcome Symbol Formula (Event Symbol Formula) → Prop
  | .done event _ => Ordered views cursor event
  | .failed _ _ => True

private theorem step_ordered (h : Nat) (views : Node → List Edge) (cursor : Cursor Symbol Formula)
    (before : Physical Symbol Formula) (reads : ReadAgreement h views cursor before) :
    OrderedResult views cursor (step h cursor before) := by
  induction cursor generalizing before with
  | empty => rfl
  | seed node =>
      cases actual : expose h node before with
      | failed fault after => simp only [step, actual, Outcome.bind, OrderedResult]
      | done rows after =>
          have same := reads rows after actual
          simp only [step, actual, Outcome.bind, OrderedResult, Ordered, denote, same]
  | seedRows rows => cases rows <;> rfl
  | extend node inner ih =>
      have prior := ih before reads
      cases actual : step h inner before with
      | failed fault after => simp only [step, actual, Outcome.bind, OrderedResult]
      | done event after =>
          rw [actual] at prior
          cases event with
          | more next =>
              simpa only [step, actual, Outcome.bind, OrderedResult, Ordered, denote] using
                congrArg (SourceCurrentConjunctionTuples.extend (views node)) prior
          | yield tuple next =>
              simp only [OrderedResult, Ordered] at prior
              simp only [step, actual, Outcome.bind, OrderedResult, Ordered, denote, prior]
              cases tuple <;> simp [SourceCurrentConjunctionTuples.extend]
          | ended =>
              simp only [OrderedResult, Ordered] at prior
              simp only [step, actual, Outcome.bind, OrderedResult, Ordered, denote, prior,
                SourceCurrentConjunctionTuples.extend, List.flatMap_nil]
  | readOperand node inner tuple _ih =>
      cases tuple with
      | nil => simp [step, OrderedResult, Ordered, denote, SourceCurrentConjunctionTuples.extend]
      | cons first rest =>
          cases actual : expose h node before with
          | failed fault after => simp only [step, actual, Outcome.bind, OrderedResult]
          | done rows after =>
              have same := reads rows after actual
              simp only [step, actual, Outcome.bind, OrderedResult, Ordered, denote, same]
  | scanOperand node inner tuple rows _ih =>
      cases tuple with
      | nil => simp [step, OrderedResult, Ordered, denote, SourceCurrentConjunctionTuples.extend]
      | cons first rest =>
          cases rows with
          | nil => simp [step, OrderedResult, Ordered, denote, SourceCurrentConjunctionTuples.extend]
          | cons edge rows =>
              by_cases symbol : edge.entry.key.symbol = first.entry.key.symbol <;>
                by_cases arity : edge.children.length = first.children.length <;>
                simp [step, symbol, arity, OrderedResult, Ordered, denote,
                  SourceCurrentConjunctionTuples.extend, SourceCurrentConjunctionTuples.shape]

/-- Actual demand preserves order and multiplicity under its observed readback. -/
theorem step_order (h : Nat) (views : Node → List Edge) (cursor : Cursor Symbol Formula)
    (before after : Physical Symbol Formula) (event : Event Symbol Formula)
    (actual : step h cursor before = .done event after) (reads : ReadAgreement h views cursor before) :
    Ordered views cursor event := by
  simpa only [actual, OrderedResult] using step_ordered h views cursor before reads

end MicroCFTA.SourceCurrentConjunctionTuplePull
