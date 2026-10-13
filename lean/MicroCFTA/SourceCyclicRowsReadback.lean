import MicroCFTA.SourceCyclicRows
import MicroCFTA.SourceDenseRowsRestrict

/-!
# Cyclic queries from actual shared-row readback

Completed toRows supplies the root and every finite key. Its closedness
theorem supplies child membership. These facts construct the finite input
to dense canonical preparation without a row-correspondence premise.
The native exposure and normalized-constraint invariants stay explicit.
-/
namespace MicroCFTA.SourceCyclicRowsReadback
open Language SourceGuards SourceObservations SourceSymbolicIndex SourceInternedRows
open SourceDenseRows RecursiveSize SizedRank RecursiveUnambiguous

/-- The raw shared adapter table retains complete source constraints. -/
abbrev Table (Formula : Type) := List (State × List (Transition (Label Formula) (Constraint Formula)))

/-- The two source row records contain the same three fields. -/
def cyclicRow (row : SourceSizedDecided.Row Node (Label Formula) (Constraint Formula)) :
    SourceCyclicAutomaton.Row Node Formula := ⟨row.label, row.children, row.constraint⟩

variable (heap : Heap (Label Formula) (Constraint Formula)) (fuel : Nat) (rootRef : Ref)
  (raw : Table Formula) (read : toRows heap fuel rootRef = some raw) (noEmpty : NoEmptyBelow heap rootRef)

include read noEmpty in
/-- The actual traversal and retained-child invariant derive the finite restriction domain. -/
theorem closed : SourceDenseRowsRestrict.Closed raw :=
  SourceDenseRowsRestrict.closed_of_interpreted (fun _ _ => true) raw
    (toRows_closed heap (fun _ _ => true) fuel rootRef raw read noEmpty)

/-- Construct the current cyclic input directly from the shared adapter's finite rows. -/
def input (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ lookup raw state → SourceCompactGuards.ActiveOption edge.constraint.equalities) :
    SourceCyclicRows.Input (SourceDenseRows.keys raw) Formula where
  root := SourceDenseRowsRestrict.root heap fuel rootRef raw read
  emptyRoot := rootRef.isNone
  freeVariables := freeVariables
  rows state := (SourceDenseRowsRestrict.rows raw (closed heap fuel rootRef raw read noEmpty) state).map cyclicRow
  emptyRows := by
    intro empty
    cases rootRef with
    | some identity => simp at empty
    | none =>
      have same : raw = [(.empty, [])] := (Option.some.inj read).symm
      subst raw
      simp [SourceDenseRowsRestrict.rows, SourceDenseRowsRestrict.root, lookup, stateOf]
  active := by
    intro state edge member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact active state.val (SourceDenseRowsRestrict.forget original)
      (SourceDenseRowsRestrict.rows_origin raw (closed heap fuel rootRef raw read noEmpty) state original present)

/-- Source constraint interpretation is unchanged by the row-record conversion. -/
theorem original_eq [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ lookup raw state → SourceCompactGuards.ActiveOption edge.constraint.equalities) :
    SourceCyclicRows.original formulas solver (input heap fuel rootRef raw read noEmpty freeVariables active) =
      SourceDenseRowsRestrict.automaton raw (closed heap fuel rootRef raw read noEmpty) (acceptsConstraint formulas solver) := by
  funext state
  simp only [SourceCyclicRows.original, input, SourceDenseRowsRestrict.automaton,
    SourceSizedDecided.automaton, List.map_map]
  rfl

/-- The constructed finite input has precisely the original guarded exposed-heap language. -/
theorem root_language [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ lookup raw state → SourceCompactGuards.ActiveOption edge.constraint.equalities)
    (term : Term (Label Formula)) :
    Accepts (SourceCyclicRows.original formulas solver (input heap fuel rootRef raw read noEmpty freeVariables active))
      (input heap fuel rootRef raw read noEmpty freeVariables active).root term ↔
      Accepts (graph heap (acceptsConstraint formulas solver)) (stateOf rootRef) term := by
  rw [original_eq]
  exact SourceDenseRowsRestrict.root_accepts heap (acceptsConstraint formulas solver)
    fuel rootRef raw read (closed heap fuel rootRef raw read noEmpty) term

/-- Exact guarded reference order is preserved before canonical sorting, including repeated input alternatives. -/
theorem reference_sequence [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ lookup raw state → SourceCompactGuards.ActiveOption edge.constraint.equalities)
    (size : Nat) :
    SourceSizedReference.classes
      (SourceCyclicRows.original formulas solver (input heap fuel rootRef raw read noEmpty freeVariables active))
      size (input heap fuel rootRef raw read noEmpty freeVariables active).root =
      SourceSizedReference.classes (graph heap (acceptsConstraint formulas solver)) size (stateOf rootRef) := by
  rw [original_eq]
  exact SourceDenseRowsRestrict.root_classes heap (acceptsConstraint formulas solver)
    fuel rootRef raw read (closed heap fuel rootRef raw read noEmpty) size

/-- The current compiled class contains exactly the guarded source terms and has finite count/decoder evaluation. -/
theorem class_correct [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ lookup raw state → SourceCompactGuards.ActiveOption edge.constraint.equalities)
    (order : Label Formula → Key) (output : Automaton (Member (SourceDenseRows.keys raw)) (Label Formula))
    (success : SourceCyclicRows.compile formulas solver
      (input heap fuel rootRef raw read noEmpty freeVariables active) order = some (.ok output)) (size : Nat) :
    let root := (input heap fuel rootRef raw read noEmpty freeVariables active).root
    SourceSizedTableEvaluation.Evaluation output (size + 1) size root (countAt output size root) (compileAt output size root) ∧
      (RecursiveSize.enumerate output size root).Nodup ∧
      (∀ term, term ∈ RecursiveSize.enumerate output size root ↔
        Accepts (graph heap (acceptsConstraint formulas solver)) (stateOf rootRef) term ∧ nodeSize term = size) ∧
      countAt output size root = (RecursiveSize.enumerate output size root).length ∧
      (∀ rank, Decoder.decode (compileAt output size root) rank = (RecursiveSize.enumerate output size root)[rank]?) := by
  obtain ⟨finite, unique, language, counted, decoded⟩ := SourceCyclicRows.class_correct formulas solver
    (input heap fuel rootRef raw read noEmpty freeVariables active) order output success size
  exact ⟨finite, unique, fun term => (language term).trans
    (and_congr (root_language heap fuel rootRef raw read noEmpty formulas solver freeVariables active term) Iff.rfl),
    counted, decoded⟩

/-- Both inverse laws and rejection refer to the original guarded heap language after actual row extraction. -/
theorem query_inverses [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (formulas : Formulas Formula) (solver : Entailment Formula) (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ lookup raw state → SourceCompactGuards.ActiveOption edge.constraint.equalities)
    (order : Label Formula → Key) (output : Automaton (Member (SourceDenseRows.keys raw)) (Label Formula))
    (success : SourceCyclicRows.compile formulas solver
      (input heap fuel rootRef raw read noEmpty freeVariables active) order = some (.ok output)) :
    let root := (input heap fuel rootRef raw read noEmpty freeVariables active).root
    (∀ position term, TablePosition.positionsOf output term root = some position ↔ replayPosition output root position = some term) ∧
      (∀ bound rank, (∃ term, selectAtMost output root bound rank = some term) ↔ rank < countAtMost output bound root) ∧
      (∀ bound rank term, rankAtMost output root bound term = some rank ↔ selectAtMost output root bound rank = some term) ∧
      (∀ bound term, rankAtMost output root bound term = none ↔
        ¬(Accepts (graph heap (acceptsConstraint formulas solver)) (stateOf rootRef) term ∧ nodeSize term ≤ bound)) := by
  obtain ⟨positions, total, inverse, rejected⟩ := SourceCyclicRows.query_inverses formulas solver
    (input heap fuel rootRef raw read noEmpty freeVariables active) order output success
  refine ⟨positions, total, inverse, ?_⟩
  intro bound term
  rw [rejected, root_language]

end MicroCFTA.SourceCyclicRowsReadback
