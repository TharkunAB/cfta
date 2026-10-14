import MicroCFTA.SourceCyclicRowsNativeGateCompile
import MicroCFTA.SourceCyclicRowsNativeGateRelational

/-!
# Sized compiler laws from related physical product rows

Related rows replace the functional product contract in the actual native
minimum callback. All compiler outcomes equal the existing reference result.
Successful outputs retain exact finite size classes and both rank inverses.
The physical relation and completed row extraction remain explicit premises.
-/
namespace MicroCFTA.SourceCyclicRowsNativeGate.Relational
open Language SourceGuards SourceObservations SourceSymbolicIndex SourceInternedRows
open SourceDenseRows SymbolicGraphView

section Readback
variable [DecidableEq Formula] [DecidableEq Key] [Ord Key]
  (heap : Heap (Label Formula) (Constraint Formula)) (fuel : Nat) (rootRef : Ref)
  (raw : SourceCyclicRowsReadback.Table Formula) (read : toRows heap fuel rootRef = some raw)
  (noEmpty : NoEmptyBelow heap rootRef) (formulas : Formulas Formula) (solver : Entailment Formula)
  (freeVariables : List Nat)
  (active : ∀ state edge, edge ∈ lookup raw state → SourceCompactGuards.ActiveOption edge.constraint.equalities)
  (order : Label Formula → Key)
  (meet : State → State → State)
  (intersectionFuel : Member (SourceDenseRows.keys raw) → Member (SourceDenseRows.keys raw) → Nat)
  (intersectionRows : State → State → SourceCyclicRowsReadback.Table Formula)
  (related : (Member (SourceDenseRows.keys raw) × Member (SourceDenseRows.keys raw)) → State → Prop)
  (roots : ∀ left right, related (left, right) (meet left.val right.val))

include roots

local notation "sourceInput" => SourceCyclicRowsReadback.input heap fuel rootRef raw read noEmpty freeVariables active
local notation "source" => SourceCyclicRows.original formulas solver sourceInput
local notation "base" => SourceCyclicRows.preparedInput sourceInput order (fun _ => 0)

omit [DecidableEq Key] in
/-- The native scan equals hasAmbiguity after the actual constraint precheck. -/
theorem checked_scan (checked : SourceCyclicAutomaton.hasConstraints base = false)
    (product : RelatedRows.Readback (DiagonalProduct.graph source) (graph heap (fun _ _ => true)) related)
    (readback : ∀ left right, toRows heap (intersectionFuel left right)
      (SourceRowsMinimumGate.reference (meet left.val right.val)) = some (intersectionRows left.val right.val)) :
    nativeScan heap (SourceDenseRows.keys raw) meet intersectionRows =
      SourceCyclicAutomaton.hasAmbiguity formulas solver base (SourceCyclicRows.pairs (SourceDenseRows.keys raw))
        (SourceCyclicRows.pairs_complete (SourceDenseRows.keys raw)) := by
  have plain := SourceCyclicAutomaton.checked_plain formulas solver base checked
  exact related_scan_eq (SourceDenseRows.keys raw) source plain heap
    (checked_readback heap fuel rootRef raw read noEmpty formulas solver freeVariables active order checked)
    meet related product roots intersectionFuel intersectionRows readback

/-- Every compiler result is unchanged when the native callback replaces the reference callback. -/
theorem compile_eq
    (product : SourceCyclicAutomaton.hasConstraints base = false →
      RelatedRows.Readback (DiagonalProduct.graph source) (graph heap (fun _ _ => true)) related)
    (readback : SourceCyclicAutomaton.hasConstraints base = false → ∀ left right,
      toRows heap (intersectionFuel left right) (SourceRowsMinimumGate.reference (meet left.val right.val)) =
        some (intersectionRows left.val right.val)) :
    compile heap (SourceDenseRows.keys raw) formulas solver sourceInput order meet intersectionRows =
      SourceCyclicRows.compile formulas solver sourceInput order := by
  by_cases checked : SourceCyclicAutomaton.hasConstraints base = false
  · unfold compile SourceCyclicRows.compile
    rw [checked_scan heap fuel rootRef raw read noEmpty formulas solver freeVariables active order meet
      intersectionFuel intersectionRows related roots checked (product checked) (readback checked)]
  · have rejected : SourceCyclicAutomaton.hasConstraints base = true := by
      cases value : SourceCyclicAutomaton.hasConstraints base <;> simp_all
    simp only [compile, SourceCyclicRows.compile, rejected, ite_true]

/-- Finite completed callback readbacks yield a completed cyclic compiler result. -/
theorem compile_finite
    (product : SourceCyclicAutomaton.hasConstraints base = false →
      RelatedRows.Readback (DiagonalProduct.graph source) (graph heap (fun _ _ => true)) related)
    (readback : SourceCyclicAutomaton.hasConstraints base = false → ∀ left right,
      toRows heap (intersectionFuel left right) (SourceRowsMinimumGate.reference (meet left.val right.val)) =
        some (intersectionRows left.val right.val)) :
    ∃ result, compile heap (SourceDenseRows.keys raw) formulas solver sourceInput order meet intersectionRows = some result := by
  rw [compile_eq heap fuel rootRef raw read noEmpty formulas solver freeVariables active order meet
    intersectionFuel intersectionRows related roots product readback]
  exact SourceCyclicRows.compile_finite formulas solver sourceInput order


/-- The native callback compiler keeps exact guarded size classes and finite decoding. -/
theorem class_correct
  (product : SourceCyclicAutomaton.hasConstraints base = false →
    RelatedRows.Readback (DiagonalProduct.graph source) (graph heap (fun _ _ => true)) related)
  (readback : SourceCyclicAutomaton.hasConstraints base = false → ∀ left right,
    toRows heap (intersectionFuel left right) (SourceRowsMinimumGate.reference (meet left.val right.val)) =
      some (intersectionRows left.val right.val))
    (output : Automaton (Member (SourceDenseRows.keys raw)) (Label Formula))
    (success : compile heap (SourceDenseRows.keys raw) formulas solver sourceInput order meet intersectionRows =
      some (.ok output)) (size : Nat) :
    SourceSizedTableEvaluation.Evaluation output (size + 1) size (sourceInput).root
      (RecursiveSize.countAt output size (sourceInput).root)
      (RecursiveSize.compileAt output size (sourceInput).root) ∧
      (RecursiveSize.enumerate output size (sourceInput).root).Nodup ∧
      (∀ term, term ∈ RecursiveSize.enumerate output size (sourceInput).root ↔
        Accepts (graph heap (acceptsConstraint formulas solver)) (stateOf rootRef) term ∧
          RecursiveSize.nodeSize term = size) ∧
      RecursiveSize.countAt output size (sourceInput).root =
        (RecursiveSize.enumerate output size (sourceInput).root).length ∧
      (∀ rank, Decoder.decode (RecursiveSize.compileAt output size (sourceInput).root) rank =
        (RecursiveSize.enumerate output size (sourceInput).root)[rank]?) := by
  rw [compile_eq heap fuel rootRef raw read noEmpty formulas solver freeVariables active order meet
    intersectionFuel intersectionRows related roots product readback] at success
  exact SourceCyclicRowsReadback.class_correct heap fuel rootRef raw read noEmpty formulas solver
    freeVariables active order output success size

/-- Both distinct-term rank inverse laws remain valid with the actual minimum-row callback. -/
theorem query_inverses
  (product : SourceCyclicAutomaton.hasConstraints base = false →
    RelatedRows.Readback (DiagonalProduct.graph source) (graph heap (fun _ _ => true)) related)
  (readback : SourceCyclicAutomaton.hasConstraints base = false → ∀ left right,
    toRows heap (intersectionFuel left right) (SourceRowsMinimumGate.reference (meet left.val right.val)) =
      some (intersectionRows left.val right.val))
    (output : Automaton (Member (SourceDenseRows.keys raw)) (Label Formula))
    (success : compile heap (SourceDenseRows.keys raw) formulas solver sourceInput order meet intersectionRows =
      some (.ok output)) :
    (∀ position term, TablePosition.positionsOf output term (sourceInput).root = some position ↔
      SizedRank.replayPosition output (sourceInput).root position = some term) ∧
      (∀ bound rank, (∃ term, RecursiveUnambiguous.selectAtMost output (sourceInput).root bound rank = some term) ↔
        rank < RecursiveSize.countAtMost output bound (sourceInput).root) ∧
      (∀ bound rank term, RecursiveUnambiguous.rankAtMost output (sourceInput).root bound term = some rank ↔
        RecursiveUnambiguous.selectAtMost output (sourceInput).root bound rank = some term) ∧
      (∀ bound term, RecursiveUnambiguous.rankAtMost output (sourceInput).root bound term = none ↔
        ¬(Accepts (graph heap (acceptsConstraint formulas solver)) (stateOf rootRef) term ∧
          RecursiveSize.nodeSize term ≤ bound)) := by
  rw [compile_eq heap fuel rootRef raw read noEmpty formulas solver freeVariables active order meet
    intersectionFuel intersectionRows related roots product readback] at success
  exact SourceCyclicRowsReadback.query_inverses heap fuel rootRef raw read noEmpty formulas solver
    freeVariables active order output success

end Readback
end MicroCFTA.SourceCyclicRowsNativeGate.Relational
