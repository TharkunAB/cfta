import MicroCFTA.SourceSizedConjunctionLanguage
import MicroCFTA.SourceSizedConjunctionSorted

/-!
# Language after decorated conjunction sorting

The final sort permutes complete rows. It preserves the language at every
key. The actual preparation and classification receipts therefore extend
the conjunction language theorem to the final returned sorted table.
This file does not identify the order of the grouped enumerator.
-/
namespace MicroCFTA.SourceSizedConjunctionSortedLanguage
open Language SourceSizedDecided SourceSizedFiniteKeys SourceSizedConjunctionWorklist
open SourceSizedConjunctionLanguage (graph)
open SourceSizedConjunctionSorted (sortedRows sortedTable)

variable {State Symbol Formula : Type} [DecidableEq State] [Ord State]
  [Ord (List State)] [DecidableEq Symbol] [Ord Symbol]

/-- Decorated sorting and symbol restoration preserve the language at every key. -/
theorem sorted_rows_language (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned)
    (key : List State) (term : Term Symbol) :
    Accepts (graph (sortedRows classified root returned success)) key term ↔
      Accepts (graph (lookup returned)) key term := by
  have same : ∀ owner edge,
      edge ∈ graph (sortedRows classified root returned success) owner ↔
        edge ∈ graph (lookup returned) owner := by
    intro owner edge
    exact ((SourceSizedConjunctionSorted.sorted_permutation
      classified root returned success owner).map
        (Row.edge SourceSizedConjunctionSemantics.holds)).mem_iff
  exact ⟨FTAValidation.accepts_transfer _ _ (fun owner edge member => (same owner edge).mp member),
    FTAValidation.accepts_transfer _ _ (fun owner edge member => (same owner edge).mpr member)⟩

/-- Exact sorted-table lookup gives the same language as the explored table. -/
theorem sorted_table_language (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned)
    (key : List State) (term : Term Symbol) :
    Accepts (graph (lookup (sortedTable classified root returned success))) key term ↔
      Accepts (graph (lookup returned)) key term := by
  have readback : lookup (sortedTable classified root returned success) =
      sortedRows classified root returned success :=
    funext (SourceSizedConjunctionSorted.sortedTable_lookup classified root returned success)
  rw [readback]
  exact sorted_rows_language classified root returned success key term

/-- Every actual stored key has the conjunction language after the final sort. -/
theorem prepared_language (classified : Classified State Symbol)
    (valid : ∀ owner row, row ∈ lookup classified owner →
      CompactGroups.ValidClasses row.children.length row.constraint)
    (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned)
    (key : List State) (present : key ∈ returned.map Prod.fst) (term : Term Symbol) :
    Accepts (graph (lookup (sortedTable classified root returned success))) key term ↔
      ∀ original ∈ key, Accepts (graph (lookup classified)) original term :=
  (sorted_table_language classified root returned success key term).trans
    (SourceSizedConjunctionLanguage.prepare_language classified valid root returned success key present term)

/-- The actual sorted initial singleton key preserves the classified root language. -/
theorem prepared_root_language (classified : Classified State Symbol)
    (valid : ∀ owner row, row ∈ lookup classified owner →
      CompactGroups.ValidClasses row.children.length row.constraint)
    (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) (term : Term Symbol) :
    Accepts (graph (lookup (sortedTable classified root returned success))) [root] term ↔
      Accepts (graph (lookup classified)) root term :=
  (sorted_table_language classified root returned success [root] term).trans
    (SourceSizedConjunctionLanguage.prepare_root_language classified valid root returned success term)

/-- Actual complete classification derives the final sorted key's language facts. -/
theorem classified_prepared_language
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned)
    (key : List State) (present : key ∈ returned.map Prod.fst) (term : Term Symbol) :
    Accepts (graph (lookup (sortedTable classified root returned success))) key term ↔
      ∀ state ∈ key, Accepts (graph (lookup classified)) state term :=
  (sorted_table_language classified root returned success key term).trans
    (SourceSizedConjunctionLanguage.classify_prepare_language
      original classified classification root returned success key present term)

/-- The actual classification, exploration, and decorated sort preserve the classified root. -/
theorem classified_prepared_root_language
    (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (classified : Classified State Symbol)
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (root : State) (returned : Stored State Symbol)
    (success : prepare classified root = .ready returned) (term : Term Symbol) :
    Accepts (graph (lookup (sortedTable classified root returned success))) [root] term ↔
      Accepts (graph (lookup classified)) root term :=
  (sorted_table_language classified root returned success [root] term).trans
    (SourceSizedConjunctionLanguage.classify_prepare_root_language
      original classified classification root returned success term)

end MicroCFTA.SourceSizedConjunctionSortedLanguage
