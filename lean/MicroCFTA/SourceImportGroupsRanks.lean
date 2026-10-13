import MicroCFTA.SourceImportGroupsFallback
import MicroCFTA.FinalObservationRanks

/-!
# Finite observation-group query records

Each finite part constructs its selector and all three inverse query views
from the same members. The final merge uses the existing source Choice
wrappers and cardinality offsets. The native per-part decoder adapter
remains separate from this finite reference construction.
-/

namespace MicroCFTA.SourceImportGroupsRanks

open Language Observation ObservationGraph SourceImportGroups
open FinalObservationRanks IntegerTermViews

/-- Imported user terms retain every constructor below user engine labels. -/
def userTerm : Term Symbol → Term (GeneratorCombinators.Label Symbol)
  | .node symbol children => .node (.user symbol) (children.map userTerm)

/-- Inverse query fields enumerate exactly the finite selector's replay positions. -/
def finiteIndex [DecidableEq Symbol] (terms : List (Term (GeneratorCombinators.Label Symbol))) :
    FinalObservationRanks.Index Symbol where
  count := terms.length
  select := fun rank => terms[rank]?
  ranks := fun view wanted => (List.range terms.length).filter fun rank =>
    match terms[rank]? with
    | none => false
    | some term => decide (project view term = wanted)

/-- Constructed finite fields satisfy every selector and inverse-view law. -/
theorem finiteIndex_exact [DecidableEq Symbol] (terms : List (Term (GeneratorCombinators.Label Symbol))) :
    Exact (finiteIndex terms) := by
  constructor
  · intro rank
    constructor
    · rintro ⟨term, found⟩
      exact (List.getElem?_eq_some_iff.mp found).1
    · intro inside
      exact ⟨terms[rank], List.getElem?_eq_getElem inside⟩
  · intro view wanted rank
    change rank ∈ (List.range terms.length).filter _ ↔ _
    simp only [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨inside, matched⟩
      cases found : terms[rank]? with
      | none => simp [found] at matched
      | some term => exact ⟨term, found, by simpa [found] using matched⟩
    · rintro ⟨term, found, matched⟩
      change terms[rank]? = some term at found
      exact ⟨(List.getElem?_eq_some_iff.mp found).1, by simpa [found] using matched⟩

/-- One imported observation part has the source user-label term view. -/
def partIndex [DecidableEq Symbol] (terms : List (Term Symbol)) : FinalObservationRanks.Index Symbol :=
  finiteIndex (terms.map userTerm)

/-- Group collection and ungrouping use exact source singleton and Choice merge cases. -/
def merged [DecidableEq Symbol] (groups : List (List (Term Symbol))) : FinalObservationRanks.Index Symbol :=
  mergeIndex ((live groups).map partIndex)

/-- Final source-shaped callbacks require no assumed local bounds or inverse laws. -/
theorem merged_exact [DecidableEq Symbol] (groups : List (List (Term Symbol))) : Exact (merged groups) := by
  apply merge_exact
  intro index present
  obtain ⟨terms, _, rfl⟩ := List.mem_map.mp present
  exact finiteIndex_exact _

/-- Private Choice wrappers do not change the number of member positions. -/
theorem merged_count [DecidableEq Symbol] (groups : List (List (Term Symbol))) :
    (merged groups).count = groups.flatten.length := by
  rw [merged, merge_count]
  simp only [totalCount, List.map_map, partIndex, finiteIndex, List.length_map, Function.comp_def]
  rw [← List.length_flatten, live_flatten]

variable [DecidableEq Symbol] [DecidableEq Refinement]
  [Ord (Term (Label Symbol Refinement))] [Ord (Option (Term (Label Symbol Refinement)))]
  (input : List (Term (Label Symbol Refinement)))
  (table : FTAValidation.Rows (Option (Term (Label Symbol Refinement))) (Label Symbol Refinement))
  (success : SourceFromTerms.build input = .ok table)
  (requested : List Path)
  (before : Variant (Option (Term (Label Symbol Refinement))) Symbol Refinement →
    Variant (Option (Term (Label Symbol Refinement))) Symbol Refinement → Bool)

include success

/-- A completed fallback index has precisely the distinct original cardinality as its rank interval. -/
theorem fallback_interval (rank : Nat) :
    (∃ term, (merged (groups (FTAValidation.rowFor table) requested none before input)).select rank = some term) ↔
      rank < input.eraseDups.length := by
  rw [(merged_exact _).bounds, merged_count,
    (SourceImportGroupsFallback.partition input table success requested before).1.length_eq]

omit [Ord (Term (Label Symbol Refinement))] [Ord (Option (Term (Label Symbol Refinement)))] success in
/-- All three final query views return exactly the replay preimages of their private terms. -/
theorem fallback_views (view : View)
    (wanted : List (Term (GeneratorCombinators.Label (Label Symbol Refinement)))) (rank : Nat) :
    rank ∈ (merged (groups (FTAValidation.rowFor table) requested none before input)).ranks view wanted ↔
      ∃ term, (merged (groups (FTAValidation.rowFor table) requested none before input)).select rank = some term ∧
        project view term = wanted :=
  (merged_exact _).ranks view wanted rank

end MicroCFTA.SourceImportGroupsRanks
