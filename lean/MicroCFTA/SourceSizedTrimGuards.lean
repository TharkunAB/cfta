import MicroCFTA.SourceSizedDecided
import MicroCFTA.SourceSizedEqualities
import MicroCFTA.GraphTrim

/-!
# The reference guard precheck on structurally trimmed rows

The source checks residual guards after structural trimming. The reference
worker still uses the original rows. Structural trimming does not inspect
guard decisions. Thus guard agreement on retained rows suffices for exact
root language agreement, even when discarded rows have residual guards.
-/

namespace MicroCFTA.SourceSizedTrimGuards

open Language Productivity SourceSizedDecided

variable {State Symbol Constraint : Type}

/-- Structural productivity is independent of every constraint decision. -/
theorem productive_independent
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (first second : Constraint → Term Symbol → Bool) :
    productive states (automaton rows first) = productive states (automaton rows second) := by
  have step : productiveStep (automaton rows first) = productiveStep (automaton rows second) := by
    funext known state
    simp [productiveStep, automaton, Row.edge, Function.comp_def]
  simp only [productive, step]

/-- Live structural successors do not depend on constraint decisions. -/
theorem live_successors_independent
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (first second : Constraint → Term Symbol → Bool) :
    successors (GraphTrim.live states (automaton rows first)) =
      successors (GraphTrim.live states (automaton rows second)) := by
  funext state
  simp only [successors, GraphTrim.live, productive_independent rows states first second]
  split
  · simp [automaton, Row.edge, List.filter_map, List.flatMap_map, Function.comp_def]
  · rfl

/-- Retain the raw source rows selected by structural productivity and reachability. -/
def trimmedRows [DecidableEq State] (rows : State → List (Row State Symbol Constraint))
    (states : List State) (root : State) : State → List (Row State Symbol Constraint) :=
  let shape := automaton rows (fun _ _ => true)
  let productive := Productivity.productive states shape
  let reached := reachClosure states (successors (GraphTrim.live states shape)) [root]
  fun state => if reached state && productive state then
    (rows state).filter fun row => row.children.all productive
  else []

/-- Interpretation commutes with the actual structural trim operation. -/
theorem trim_interpretation [DecidableEq State]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (root : State) (holds : Constraint → Term Symbol → Bool) :
    GraphTrim.trim states (automaton rows holds) root =
      automaton (trimmedRows rows states root) holds := by
  funext state
  simp only [GraphTrim.trim, GraphTrim.live,
    live_successors_independent rows states holds (fun _ _ => true),
    productive_independent rows states holds (fun _ _ => true)]
  simp [automaton, trimmedRows, Row.edge, List.filter_map, Function.comp_def]
  split <;> split <;> simp_all

/-- Guard agreement on the trimmed rows gives exact original root languages. -/
theorem guards_exact [DecidableEq State]
    (rows : State → List (Row State Symbol Constraint)) (states : List State)
    (complete : ∀ state, state ∈ states) (root : State)
    (first second : Constraint → Term Symbol → Bool)
    (agree : ∀ state row, row ∈ trimmedRows rows states root state →
      ∀ term, first row.constraint term = second row.constraint term)
    (term : Term Symbol) :
    Accepts (automaton rows first) root term ↔ Accepts (automaton rows second) root term := by
  rw [← GraphTrim.trim_exact states complete (automaton rows first) root term,
    ← GraphTrim.trim_exact states complete (automaton rows second) root term,
    trim_interpretation, trim_interpretation]
  have same : automaton (trimmedRows rows states root) first =
      automaton (trimmedRows rows states root) second := by
    funext state
    apply List.map_congr_left
    intro row member
    have guardSame : first row.constraint = second row.constraint :=
      funext (agree state row member)
    simp only [Row.edge, guardSame]
  rw [same]

/-- The source scans only structurally retained rows for residual syntax. -/
def residualScan [DecidableEq State]
    (rows : State → List (Row State Symbol (SourceSymbolicIndex.Constraint Formula)))
    (states : List State) (root : State) : Bool :=
  states.any fun state => (trimmedRows rows states root state).any fun row =>
    !(SourceCompactGuards.positive row.constraint.guard).isSome

/-- Passing the finite source scan establishes positivity on every retained row. -/
theorem residualScan_exact [DecidableEq State]
    (rows : State → List (Row State Symbol (SourceSymbolicIndex.Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states) (root : State) :
    residualScan rows states root = false ↔
      ∀ state row, row ∈ trimmedRows rows states root state →
        (SourceCompactGuards.positive row.constraint.guard).isSome = true := by
  constructor
  · intro passed state row member
    have noBad := List.any_eq_false.mp passed state (complete state)
    by_cases positive : (SourceCompactGuards.positive row.constraint.guard).isSome = true
    · exact positive
    · exact False.elim (noBad (List.any_eq_true.mpr ⟨row, member, by simpa using positive⟩))
  · intro positive
    apply List.any_eq_false.mpr
    intro state _ bad
    obtain ⟨row, member, failed⟩ := List.any_eq_true.mp bad
    rw [positive state row member] at failed
    cases failed

/-- A successful residual-guard precheck is sufficient on the trimmed rows only. -/
theorem reference_precheck_exact [DecidableEq State] [DecidableEq Formula]
    (formulas : SourceGuards.Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (rows : State → List (Row State (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states) (root : State)
    (active : ∀ state row, row ∈ trimmedRows rows states root state →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (noResidual : ∀ state row, row ∈ trimmedRows rows states root state →
      (SourceCompactGuards.positive row.constraint.guard).isSome = true)
    (size : Nat) (term : Term (SourceObservations.Label Formula)) :
    term ∈ SourceSizedReference.classes
      (automaton rows SourceSizedEqualities.constraintHolds) size root ↔
      Accepts (automaton rows (SourceSymbolicIndex.acceptsConstraint formulas solver)) root term ∧
        RecursiveSize.nodeSize term = size := by
  rw [SourceSizedReference.mem_classes_iff]
  apply and_congr_left
  intro _
  apply guards_exact rows states complete root
  intro state row member term
  exact SourceSizedEqualities.constraintHolds_exact formulas solver row.constraint
    (active state row member) (noResidual state row member) term

/-- A successful public residual scan gives the exact original root classes. -/
theorem reference_scan_exact [DecidableEq State] [DecidableEq Formula]
    (formulas : SourceGuards.Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (rows : State → List (Row State (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula)))
    (states : List State) (complete : ∀ state, state ∈ states) (root : State)
    (active : ∀ state row, row ∈ trimmedRows rows states root state →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (passed : residualScan rows states root = false)
    (size : Nat) (term : Term (SourceObservations.Label Formula)) :
    term ∈ SourceSizedReference.classes
      (automaton rows SourceSizedEqualities.constraintHolds) size root ↔
      Accepts (automaton rows (SourceSymbolicIndex.acceptsConstraint formulas solver)) root term ∧
        RecursiveSize.nodeSize term = size :=
  reference_precheck_exact formulas solver rows states complete root active
    ((residualScan_exact rows states complete root).mp passed) size term

end MicroCFTA.SourceSizedTrimGuards
