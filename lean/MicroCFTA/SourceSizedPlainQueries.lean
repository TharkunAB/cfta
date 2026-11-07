import MicroCFTA.SourceSizedScopedUnambiguity
import MicroCFTA.SourceSizedRunPermutation
import MicroCFTA.SourceSizedGuardedDeterminization
import MicroCFTA.SourceSizedAnnotationErasure

/-!
# Exact queries of the current scoped plain counting route

The source checks plainness and unambiguity on the query's trimmed rows.
Its plain count table uses every original erased row in the one shared
canonical order. The scoped Boolean checks derive original root uniqueness
and guard erasure. Sorting retains every run with its multiplicity.

These facts give all signed query laws for the original guarded language.
No global original plainness, global uniqueness, finite raw state type,
completed count table, or caller sort permutation is required. The full
dispatcher, native storage, and original-input work bound remain separate.
-/
namespace MicroCFTA.SourceSizedPlainQueries
open Language SourceSizedDecided SourceSizedFiniteKeys
open SourceObservations SourceSymbolicIndex SourceGuards

/-- Source erasure before sorting gives the same exact raw count-table rows. -/
theorem source_sort_readback {State Symbol Payload : Type} [DecidableEq State] [Ord State]
    [DecidableEq Symbol] [Ord Symbol] [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol]
    (table : Table State Symbol Payload) (initial : State)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (state : SourceDenseRows.Member (SourceDenseRows.keys table)) :
    (automaton (SourceSizedPreprocessing.sortedRows
      (SourceSizedAnnotationErasure.eraseInput (SourceSizedStructuralKeys.input table initial success)))
      (fun _ _ => true) state).map (SymbolicGraphView.renameEdge Subtype.val) =
        automaton (SourceSizedStructuralKeys.nativeSorted table initial success) (fun _ _ => true) state.val := by
  rw [SourceSizedAnnotationErasure.sorted_automaton]
  simp only [automaton]
  rw [← SourceSizedStructuralKeys.sorted_readback table initial success state]
  simp only [List.map_map, Function.comp_def]
  rfl

variable {State Formula : Type} [DecidableEq State] [Ord State]
  [DecidableEq Formula] [Ord (Label Formula)]

/-- Read the shared plain count table in the original graph's canonical order. -/
def api (table : Table State (Label Formula) (Constraint Formula)) (initial : State)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (root : State) :
    SourceSizedDispatcher.Api (Label Formula) :=
  SourceSizedDispatcher.optimizedApi
    (automaton (SourceSizedStructuralKeys.nativeSorted table initial success) (fun _ _ => true)) root

/-- Actual scoped checks derive every exact query law for the original guarded root. -/
theorem queries_exact (table : Table State (Label Formula) (Constraint Formula))
    (initial root : State) (formulas : Formulas Formula) (solver : Entailment Formula)
    (success : SourceFTAValidation.validateRows initial (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (present : root ∈ SourceDenseRows.keys table)
    (plain : SourceSizedGuardedDeterminization.plainCheck table root = true)
    (unique : SourceSizedScopedUnambiguity.unambiguousRows table root
      (SourceSizedSharedSorting.reroot_valid table initial root success present) = true) :
    SourceSizedApiLaws.Exact (api table initial success root)
      (Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root) := by
  classical
  let valid := SourceSizedSharedSorting.reroot_valid table initial root success present
  let sorted := automaton (SourceSizedStructuralKeys.nativeSorted table initial success) (fun _ _ => true)
  have originalUnique := SourceSizedScopedUnambiguity.root_unique table root valid unique
  have sortedUnique (size : Nat) : (RecursiveSize.enumerate sorted size root).Nodup :=
    (SourceSizedRunPermutation.nativeSorted_enumerate table initial success
      (fun _ _ => true) size root).nodup_iff.mpr (originalUnique size)
  have permutation (state : State) :
      (sorted state).Perm (SourceSizedDeterminizationTableInput.rows table state) :=
    (SourceSizedStructuralKeys.nativeSorted_perm table initial success state).map (Row.edge (fun _ _ => true))
  have correct (term : Term (Label Formula)) :
      Accepts sorted root term ↔
        Accepts (automaton (lookup table) (acceptsConstraint formulas solver)) root term :=
    (SourceCyclicAutomaton.permutation_language
      (SourceSizedDeterminizationTableInput.rows table) sorted permutation root term).trans
        (SourceSizedScopedErasure.erasure_exact table root SourceSizedDispatcher.noConstraint
          (acceptsConstraint formulas solver) valid plain
          (fun candidate => SourceEqualityConstraintConstructors.top_true formulas solver candidate) term).symm
  exact SourceSizedRootQueryLaws.optimized_exact sorted
    (SourceSizedDispatcher.ordinary_plain _) root sortedUnique _ correct

end MicroCFTA.SourceSizedPlainQueries
