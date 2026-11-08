import MicroCFTA.SourceCurrentConjunctionTuplePullReads
import MicroCFTA.SourceCurrentConjunctionTuplePullTotal

/-!
# Heap preservation through actual tuple demand

Each cursor transition performs at most its requested native read. This
identity includes failed reads. The composition laws use the original
operand support and retain repeated demands. Their local preservation
premise is a component rule for the literal native reader. Selected
consumers must derive that rule from their actual heap invariants.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullHeapEffects
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionTuplePull (Cursor Event step expose start)
open SourceCurrentConjunctionTuplePullReads (requested Supported)
open SourceCurrentConjunctionTuplePullAdmission (advance drive)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

omit [DecidableEq Symbol] in
/-- Singleton exposure retains the exact native heap on every outcome. -/
theorem expose_heap (h : Nat) (node : Node) (before : Physical Symbol Formula) :
    (expose h node before).state.heap =
      (MergedFreshOrdinaryExposure.nodeEdges h node before.heap).state := by
  cases actual : MergedFreshOrdinaryExposure.nodeEdges h node before.heap <;>
    simp only [expose, SourceCurrentConjunctionRowsWorker.exposures, actual,
      Outcome.bind, Outcome.state, MergedSourceExposure.Result.state]

/-- A transition changes the heap only through its actual requested read. -/
theorem step_heap (h : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula) :
    (step h cursor before).state.heap =
      match requested cursor with
      | none => before.heap
      | some node => (MergedFreshOrdinaryExposure.nodeEdges h node before.heap).state := by
  induction cursor generalizing before with
  | empty => rfl
  | seed node =>
      have same := expose_heap h node before
      cases actual : expose h node before <;>
        simpa only [step, requested, actual, Outcome.bind, Outcome.state] using same
  | seedRows rows => cases rows <;> rfl
  | extend node inner ih =>
      have same := ih before
      cases actual : step h inner before with
      | failed fault after =>
          simpa only [step, requested, actual, Outcome.bind, Outcome.state] using same
      | done event after =>
          cases event <;>
            simpa only [step, requested, actual, Outcome.bind, Outcome.state] using same
  | readOperand node inner tuple _ih =>
      cases tuple with
      | nil => rfl
      | cons first rest =>
          have same := expose_heap h node before
          cases actual : expose h node before <;>
            simpa only [step, requested, actual, Outcome.bind, Outcome.state] using same
  | scanOperand node inner tuple rows _ih =>
      cases tuple with
      | nil => rfl
      | cons first rest =>
          cases rows with
          | nil => rfl
          | cons edge rows =>
              simp only [step, requested]
              split <;> (try split) <;> rfl

/-- A native heap invariant extends through one supported transition. -/
theorem step_preserves (property : State Symbol Guard → Prop) (h : Nat) (support : List Node)
    (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula)
    (supported : Supported support cursor) (initial : property before.heap)
    (preserve : ∀ heap node, node ∈ support → property heap →
      property (MergedFreshOrdinaryExposure.nodeEdges h node heap).state) :
    property (step h cursor before).state.heap := by
  rw [step_heap]
  cases actual : requested cursor with
  | none => exact initial
  | some node =>
      exact preserve before.heap node
        (SourceCurrentConjunctionTuplePullReads.requested_mem support cursor node supported actual) initial

/-- Every finite drive preserves the invariant, including suspension and faults. -/
theorem drive_preserves (property : State Symbol Guard → Prop) (steps h budget : Nat)
    (support : List Node) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) (supported : Supported support cursor)
    (initial : property before.heap)
    (preserve : ∀ heap node, node ∈ support → property heap →
      property (MergedFreshOrdinaryExposure.nodeEdges h node heap).state) :
    property (drive steps h budget cursor collected before).state.heap := by
  induction steps generalizing cursor collected before with
  | zero => exact initial
  | succ steps ih =>
      have first := step_preserves property h support cursor before supported initial preserve
      cases actual : step h cursor before with
      | failed fault after =>
          simpa only [drive, advance, actual, Outcome.bind, Outcome.state] using first
      | done event after =>
          have reached : property after.heap := by simpa only [actual, Outcome.state] using first
          have smaller := SourceCurrentConjunctionTuplePullProgress.step_next h cursor before after event actual
          cases event with
          | ended =>
              simpa only [drive, advance, actual, Outcome.bind, Outcome.state] using reached
          | more next =>
              have continued := SourceCurrentConjunctionTuplePullReads.next_supported support smaller supported
              simpa only [drive, advance, actual, Outcome.bind] using
                ih next collected after continued reached
          | yield tuple next =>
              have continued := SourceCurrentConjunctionTuplePullReads.next_supported support smaller supported
              by_cases full : budget < (collected ++ [tuple]).length
              · simpa only [drive, advance, actual, Outcome.bind, full, ite_true, Outcome.state] using reached
              · simpa only [drive, advance, actual, Outcome.bind, full, ite_false] using
                  ih next (collected ++ [tuple]) after continued reached

/-- The total cursor run derives its own finite invariant-preserving observation. -/
theorem run_preserves (property : State Symbol Guard → Prop) (h budget : Nat)
    (support : List Node) (cursor : Cursor Symbol Formula) (collected : List (List Edge))
    (before : Physical Symbol Formula) (supported : Supported support cursor)
    (initial : property before.heap)
    (preserve : ∀ heap node, node ∈ support → property heap →
      property (MergedFreshOrdinaryExposure.nodeEdges h node heap).state) :
    property (SourceCurrentConjunctionTuplePullTotal.run h budget cursor collected before).state.heap := by
  obtain ⟨steps, eventual⟩ :=
    SourceCurrentConjunctionTuplePullTotal.run_observation h budget cursor collected before
  have actual := eventual 0
  simp only [Nat.add_zero] at actual
  have kept := drive_preserves property steps h budget support cursor collected before supported initial preserve
  simpa only [actual, SourceCurrentConjunctionTuplePullTotal.observe_state] using kept

/-- Sampling preserves a native invariant using only the original operand support. -/
theorem sample_preserves (property : State Symbol Guard → Prop) (h budget : Nat) (nodes : List Node)
    (before : Physical Symbol Formula) (initial : property before.heap)
    (preserve : ∀ heap node, node ∈ nodes → property heap →
      property (MergedFreshOrdinaryExposure.nodeEdges h node heap).state) :
    property (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before).state.heap :=
  run_preserves property h budget nodes (start nodes) [] before
    (SourceCurrentConjunctionTuplePullReads.start_supported nodes) initial preserve

end MicroCFTA.SourceCurrentConjunctionTuplePullHeapEffects
