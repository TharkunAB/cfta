import MicroCFTA.SourceSizedConjunctionGuarded
import MicroCFTA.SourceSizedConjunctionSortedLanguage

/-!
# Complete source conjunction-row preparation

Classify every original row, explore at the source limit 1024, then decorate,
canonically sort, and restore symbols. Only classification and actual cap
failure return none. The explorer's proved terminal bound excludes exhaustion.
Successful preparation supplies structural closure and root validation.
The guarded language law retains its internal normalized-field invariant.
Grouped counting, fromTable, public routing, native containers, and machine
arithmetic remain separate.
-/
namespace MicroCFTA.SourceSizedConjunctionPreparation
open Language SourceSizedDecided SourceSizedFiniteKeys SourceGuards SourceObservations
open SourceSymbolicIndex
open SourceSizedConjunctionWorklist (Classified Stored)

variable {State Symbol Formula : Type}
  [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol] [Ord Symbol]

/-- Execute the complete classification, capped exploration, and decorated sort. -/
noncomputable def prepare (original : Table State Symbol (Constraint Formula)) (root : State) :
    Option (Stored State Symbol) :=
  match SourceSizedConjunctionClassified.classifyTable original with
  | none => none
  | some classified =>
      match ready : SourceSizedConjunctionWorklist.prepare classified root with
      | .ready returned => some (SourceSizedConjunctionSorted.sortedTable classified root returned ready)
      | .limitExceeded => none
      | .exhausted => False.elim (SourceSizedConjunctionWorklist.prepare_terminal classified root ready)

/-- Actual classifier and explorer successes return the exact decorated sorted table. -/
theorem prepare_of_ready (original : Table State Symbol (Constraint Formula)) (root : State)
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (returned : Stored State Symbol)
    (ready : SourceSizedConjunctionWorklist.prepare classified root = .ready returned) :
    prepare original root = some (SourceSizedConjunctionSorted.sortedTable classified root returned ready) := by
  simp only [prepare, classification]
  split
  · rename_i actual found
    have same : actual = returned :=
      SourceSizedConjunctionWorklist.Outcome.ready.inj (found.symm.trans ready)
    subst actual
    rfl
  · rename_i capped
    cases capped.symm.trans ready
  · rename_i exhausted
    exact (SourceSizedConjunctionWorklist.prepare_terminal classified root exhausted).elim

/-- Every successful output originates in actual classification, exploration, and the final sort. -/
theorem success_origin (original : Table State Symbol (Constraint Formula)) (root : State)
    (output : Stored State Symbol) (success : prepare original root = some output) :
    ∃ classified, SourceSizedConjunctionClassified.classifyTable original = some classified ∧
      ∃ returned, ∃ ready : SourceSizedConjunctionWorklist.prepare classified root = .ready returned,
        output = SourceSizedConjunctionSorted.sortedTable classified root returned ready := by
  unfold prepare at success
  split at success
  · cases success
  · rename_i classified classification
    split at success
    · rename_i returned ready
      exact ⟨classified, classification, returned, ready, Option.some.inj success.symm⟩
    · cases success
    · rename_i exhausted
      exact (SourceSizedConjunctionWorklist.prepare_terminal classified root exhausted).elim

/-- The source returns none exactly for classifier failure or an actual exploration cap failure. -/
theorem none_iff (original : Table State Symbol (Constraint Formula)) (root : State) :
    prepare original root = none ↔
      SourceSizedConjunctionClassified.classifyTable original = none ∨
        ∃ classified, SourceSizedConjunctionClassified.classifyTable original = some classified ∧
          SourceSizedConjunctionWorklist.prepare classified root = .limitExceeded := by
  constructor
  · intro failure
    unfold prepare at failure
    split at failure
    · rename_i classification
      exact .inl classification
    · rename_i classified classification
      split at failure
      · cases failure
      · rename_i capped
        exact .inr ⟨classified, classification, capped⟩
      · rename_i exhausted
        exact (SourceSizedConjunctionWorklist.prepare_terminal classified root exhausted).elim
  · rintro (classification | ⟨classified, classification, capped⟩)
    · unfold prepare
      rw [classification]
    · simp only [prepare, classification]
      split
      · rename_i returned ready
        cases ready.symm.trans capped
      · rfl
      · rename_i exhausted
        exact (SourceSizedConjunctionWorklist.prepare_terminal classified root exhausted).elim

/-- A successful final table declares the original singleton root key. -/
theorem root_keys (original : Table State Symbol (Constraint Formula)) (root : State)
    (output : Stored State Symbol) (success : prepare original root = some output) :
    [root] ∈ SourceDenseRows.keys output := by
  obtain ⟨classified, _, returned, ready, same⟩ := success_origin original root output success
  rw [same, SourceSizedConjunctionSorted.sortedTable_keys]
  exact SourceSizedConjunctionClosure.prepare_root_keys classified root returned ready

/-- Actual source success derives final child closure without an output-closure premise. -/
theorem closed (original : Table State Symbol (Constraint Formula)) (root : State)
    (output : Stored State Symbol) (success : prepare original root = some output) : Closed output := by
  obtain ⟨classified, _, returned, ready, same⟩ := success_origin original root output success
  rw [same]
  exact SourceSizedConjunctionSorted.sortedTable_closed classified root returned ready

/-- Current structural validation accepts every actual successful final table. -/
theorem validation (original : Table State Symbol (Constraint Formula)) (root : State)
    (output : Stored State Symbol) (success : prepare original root = some output) :
    SourceFTAValidation.validateRows [root] (interpreted output (fun _ _ => true)) =
      .ok (interpreted output (fun _ _ => true)) := by
  obtain ⟨classified, _, returned, ready, same⟩ := success_origin original root output success
  rw [same]
  exact SourceSizedConjunctionSorted.sortedTable_validation classified root returned ready

section Guarded
variable [DecidableEq Formula] [Ord (Label Formula)]

/-- Each returned key denotes the conjunction of its original guarded state languages. -/
theorem key_language (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (active : ∀ owner row, row ∈ lookup original owner →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (root : State) (output : Stored State (Label Formula))
    (success : prepare original root = some output)
    (key : List State) (present : key ∈ output.map Prod.fst) (term : Term (Label Formula)) :
    Accepts (SourceSizedConjunctionLanguage.graph (lookup output)) key term ↔
      ∀ owner ∈ key, Accepts (SourceSizedConjunctionGuarded.originalGraph formulas solver original) owner term := by
  obtain ⟨classified, classification, returned, ready, same⟩ := success_origin original root output success
  have originalPresent : key ∈ returned.map Prod.fst := by
    rw [same, SourceSizedConjunctionSorted.sortedTable_key_sequence] at present
    exact present
  rw [same]
  exact (SourceSizedConjunctionSortedLanguage.sorted_table_language
    classified root returned ready key term).trans
      (SourceSizedConjunctionGuarded.prepare_language formulas solver original classified classification active
        root returned ready key originalPresent term)

/-- The complete successful source pipeline preserves the original guarded root language. -/
theorem root_language (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (active : ∀ owner row, row ∈ lookup original owner →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (root : State) (output : Stored State (Label Formula))
    (success : prepare original root = some output) (term : Term (Label Formula)) :
    Accepts (SourceSizedConjunctionLanguage.graph (lookup output)) [root] term ↔
      Accepts (SourceSizedConjunctionGuarded.originalGraph formulas solver original) root term := by
  obtain ⟨classified, classification, returned, ready, same⟩ := success_origin original root output success
  rw [same]
  exact (SourceSizedConjunctionSortedLanguage.sorted_table_language
    classified root returned ready [root] term).trans
      (SourceSizedConjunctionGuarded.prepare_root_language formulas solver original classified classification active
        root returned ready term)

/-- Ready physical stored fields discharge the internal invariant for the complete root pipeline. -/
theorem root_language_of_ready (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (inventory : ∀ owner row, row ∈ lookup original owner →
      ∃ (stored : SourceEqualityConstraintAllocation.Value) (guard : Guard Formula),
        SourceEqualityConstraintAllocation.Ready cache stored ∧
          row.constraint = SourceEqualityAccessorAllocation.constraint stored guard)
    (root : State) (output : Stored State (Label Formula))
    (success : prepare original root = some output) (term : Term (Label Formula)) :
    Accepts (SourceSizedConjunctionLanguage.graph (lookup output)) [root] term ↔
      Accepts (SourceSizedConjunctionGuarded.originalGraph formulas solver original) root term :=
  root_language formulas solver original
    (SourceSizedConjunctionGuarded.active_of_ready original cache inventory) root output success term

end Guarded
end MicroCFTA.SourceSizedConjunctionPreparation
