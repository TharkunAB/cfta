import MicroCFTA.SourceCyclicRowsNativeGate

/-!
# Cyclic compiler result with the native row callback

The native overlap callback replaces only the synchronous reference check.
The empty, open, and constrained branches retain their source precedence.
After the constraint precheck, ordered actual row readback derives the
finite plain source region. Native product construction is still explicit.
-/
namespace MicroCFTA.SourceCyclicRowsNativeGate
open Language SourceGuards SourceObservations SourceSymbolicIndex SourceInternedRows
open SourceDenseRows SymbolicGraphView

/-- The current cyclic control flow with actual native minimum-row callbacks. -/
noncomputable def compile [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    (heap : Heap (Label Formula) (Constraint Formula)) (keys : List State)
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (input : SourceCyclicRows.Input keys Formula) (order : Label Formula → Key)
    (meet : State → State → State)
    (intersectionRows : State → State → SourceCyclicRowsReadback.Table Formula) :
    Option (Except SourceCyclicAutomaton.Error (Automaton (Member keys) (Label Formula))) :=
  let base := SourceCyclicRows.preparedInput input order (fun _ => 0)
  if input.emptyRoot then some (.ok (fun _ => []))
  else if !input.freeVariables.isEmpty then some (.error .openAutomaton)
  else if SourceCyclicAutomaton.hasConstraints base then some (.error .constrainedEdges)
  else if nativeScan heap keys meet intersectionRows then some (.error .ambiguousAutomaton)
  else (SourceCyclicRows.canonical formulas solver input order).map fun classes =>
    .ok (SourceCyclicAutomaton.ordered formulas solver (SourceCyclicRows.preparedInput input order classes))

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

local notation "sourceInput" => SourceCyclicRowsReadback.input heap fuel rootRef raw read noEmpty freeVariables active
local notation "source" => SourceCyclicRows.original formulas solver sourceInput
local notation "base" => SourceCyclicRows.preparedInput sourceInput order (fun _ => 0)

omit [DecidableEq Key] in
/-- The native scan equals hasAmbiguity after the actual constraint precheck. -/
theorem checked_scan (checked : SourceCyclicAutomaton.hasConstraints base = false)
    (product : ProductReadback source (graph heap (fun _ _ => true)) Subtype.val
      (fun left right => meet left.val right.val))
    (readback : ∀ left right, toRows heap (intersectionFuel left right)
      (SourceRowsMinimumGate.reference (meet left.val right.val)) = some (intersectionRows left.val right.val)) :
    nativeScan heap (SourceDenseRows.keys raw) meet intersectionRows =
      SourceCyclicAutomaton.hasAmbiguity formulas solver base (SourceCyclicRows.pairs (SourceDenseRows.keys raw))
        (SourceCyclicRows.pairs_complete (SourceDenseRows.keys raw)) := by
  have plain := SourceCyclicAutomaton.checked_plain formulas solver base checked
  exact scan_eq (SourceDenseRows.keys raw) source plain heap
    (checked_readback heap fuel rootRef raw read noEmpty formulas solver freeVariables active order checked)
    meet product intersectionFuel intersectionRows readback

/-- Every compiler result is unchanged when the native callback replaces the reference callback. -/
theorem compile_eq
    (product : SourceCyclicAutomaton.hasConstraints base = false →
      ProductReadback source (graph heap (fun _ _ => true)) Subtype.val
        (fun left right => meet left.val right.val))
    (readback : SourceCyclicAutomaton.hasConstraints base = false → ∀ left right,
      toRows heap (intersectionFuel left right) (SourceRowsMinimumGate.reference (meet left.val right.val)) =
        some (intersectionRows left.val right.val)) :
    compile heap (SourceDenseRows.keys raw) formulas solver sourceInput order meet intersectionRows =
      SourceCyclicRows.compile formulas solver sourceInput order := by
  by_cases checked : SourceCyclicAutomaton.hasConstraints base = false
  · unfold compile SourceCyclicRows.compile
    rw [checked_scan heap fuel rootRef raw read noEmpty formulas solver freeVariables active order meet
      intersectionFuel intersectionRows checked (product checked) (readback checked)]
  · have rejected : SourceCyclicAutomaton.hasConstraints base = true := by
      cases value : SourceCyclicAutomaton.hasConstraints base <;> simp_all
    simp only [compile, SourceCyclicRows.compile, rejected, ite_true]

/-- Finite completed callback readbacks yield a completed cyclic compiler result. -/
theorem compile_finite
    (product : SourceCyclicAutomaton.hasConstraints base = false →
      ProductReadback source (graph heap (fun _ _ => true)) Subtype.val
        (fun left right => meet left.val right.val))
    (readback : SourceCyclicAutomaton.hasConstraints base = false → ∀ left right,
      toRows heap (intersectionFuel left right) (SourceRowsMinimumGate.reference (meet left.val right.val)) =
        some (intersectionRows left.val right.val)) :
    ∃ result, compile heap (SourceDenseRows.keys raw) formulas solver sourceInput order meet intersectionRows = some result := by
  rw [compile_eq heap fuel rootRef raw read noEmpty formulas solver freeVariables active order meet
    intersectionFuel intersectionRows product readback]
  exact SourceCyclicRows.compile_finite formulas solver sourceInput order


/-- The native callback compiler keeps exact guarded size classes and finite decoding. -/
theorem class_correct
  (product : SourceCyclicAutomaton.hasConstraints base = false →
    ProductReadback source (graph heap (fun _ _ => true)) Subtype.val
      (fun left right => meet left.val right.val))
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
    intersectionFuel intersectionRows product readback] at success
  exact SourceCyclicRowsReadback.class_correct heap fuel rootRef raw read noEmpty formulas solver
    freeVariables active order output success size

/-- Both distinct-term rank inverse laws remain valid with the actual minimum-row callback. -/
theorem query_inverses
  (product : SourceCyclicAutomaton.hasConstraints base = false →
    ProductReadback source (graph heap (fun _ _ => true)) Subtype.val
      (fun left right => meet left.val right.val))
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
    intersectionFuel intersectionRows product readback] at success
  exact SourceCyclicRowsReadback.query_inverses heap fuel rootRef raw read noEmpty formulas solver
    freeVariables active order output success

end Readback
end MicroCFTA.SourceCyclicRowsNativeGate
