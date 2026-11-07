import MicroCFTA.SourceSizedConjunctionCurrent
import MicroCFTA.SourceSizedGroupedUnique
import MicroCFTA.SourceSizedScopedTrimClosure

/-!
# Exact grouped classes for current raw input constraints

Actual scoped trimming preserves the original root language under any guard
interpreter. Successful conjunction preparation then preserves the current
accessor-based constraint evaluator. The grouped worker lists each accepted
term of the requested node count exactly once. Raw inputs need no normalized
field condition. Native index operations and total work remain separate.
-/
namespace MicroCFTA.SourceSizedGroupedCurrent
open Language SourceSizedDecided SourceSizedFiniteKeys SourceDenseRows
open SourceGuards SourceObservations SourceSymbolicIndex

variable {State Symbol Payload Formula : Type} [DecidableEq State] [Ord State]

/-- Actual structural trimming preserves the root under any complete guard interpreter. -/
theorem trimmed_language (table : Table State Symbol Payload) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (holds : Payload → Term Symbol → Bool) (term : Term Symbol) :
    Accepts (automaton (lookup (SourceSizedScopedTrimInventory.trimmedTable table root)) holds) root term ↔
      Accepts (automaton (lookup table) holds) root term := by
  let closed := SourceSizedStructuralKeys.validated_closed table root validated
  let finiteRoot : Member (keys table) :=
    ⟨root, SourceSizedStructuralKeys.validated_root table root validated⟩
  have trimmed :
      Accepts (GraphTrim.trim (keys table) (automaton (lookup table) holds) root) root term ↔
        Accepts (GraphTrim.trim (keys table).attach (automaton (restricted table closed) holds)
          finiteRoot) finiteRoot term := by
    refine SymbolicGraphView.rowsCorrespond_exact
      (GraphTrim.trim (keys table).attach (automaton (restricted table closed) holds) finiteRoot)
      (GraphTrim.trim (keys table) (automaton (lookup table) holds) root)
      Subtype.val ?_ finiteRoot term
    intro state edge
    rw [SourceSizedFiniteKeysTrim.restricted_trim table closed holds finiteRoot state]
    simp only [List.mem_map, eq_comm]
  have interpretedTrim :
      automaton (lookup (SourceSizedScopedTrimInventory.trimmedTable table root)) holds =
        GraphTrim.trim (keys table) (automaton (lookup table) holds) root := by
    rw [SourceSizedTrimGuards.trim_interpretation]
    funext state
    simp only [automaton, SourceSizedScopedTrimInventory.trimmed_lookup]
  rw [interpretedTrim]
  exact trimmed.trans
    ((GraphTrim.trim_exact (keys table).attach (member_complete (keys table))
      (automaton (restricted table closed) holds) finiteRoot term).trans
        (SourceSizedFiniteKeys.accepts_exact table closed holds finiteRoot term))

variable [DecidableEq Formula] [Ord (Label Formula)] [Ord (List State)]

/-- Complete preparation of the actual scoped table retains current original acceptance. -/
theorem prepared_root_language (formulas : Formulas Formula) (solver : Entailment Formula)
    (table : Table State (Label Formula) (Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (output : SourceSizedConjunctionWorklist.Stored State (Label Formula))
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (term : Term (Label Formula)) :
    Accepts (SourceSizedConjunctionLanguage.graph (lookup output)) [root] term ↔
      Accepts (SourceSizedConjunctionCurrent.originalGraph formulas solver table) root term :=
  (SourceSizedConjunctionCurrent.root_language formulas solver
    (SourceSizedScopedTrimInventory.trimmedTable table root) root output success term).trans
      (trimmed_language table root validated (SourceConstraintEntryRaw.acceptsConstraint formulas solver) term)

/-- The computed grouped evaluator returns each current original term of the requested size once. -/
theorem prepared_root_exact (formulas : Formulas Formula) (solver : Entailment Formula)
    (table : Table State (Label Formula) (Constraint Formula)) (root : State)
    (validated : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedScopedUnambiguity.unambiguousRows table root validated = true)
    (output : SourceSizedConjunctionWorklist.Stored State (Label Formula))
    (success : SourceSizedConjunctionPreparation.prepare
      (SourceSizedScopedTrimInventory.trimmedTable table root) root = some output)
    (size : Nat) :
    (SourceSizedGroupedClasses.run (lookup output) size [root]).Nodup ∧
      ∀ term, term ∈ SourceSizedGroupedClasses.run (lookup output) size [root] ↔
        Accepts (SourceSizedConjunctionCurrent.originalGraph formulas solver table) root term ∧
          RecursiveSize.nodeSize term = size := by
  obtain ⟨unique, language⟩ := SourceSizedGroupedUnique.prepared_run_exact
    table root validated passed output success size [root]
  refine ⟨unique, fun term => (language term).trans ?_⟩
  exact and_congr (prepared_root_language formulas solver table root validated output success term) Iff.rfl

end MicroCFTA.SourceSizedGroupedCurrent
