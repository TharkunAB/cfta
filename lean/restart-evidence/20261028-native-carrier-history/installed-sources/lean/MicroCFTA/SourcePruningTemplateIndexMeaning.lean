import MicroCFTA.SourcePruningTemplates

/-!
# Original catalog membership of indexed pruning templates

The actual tagged lookup selects only original catalog entries.
No semantic match or future execution is assumed.
-/
namespace MicroCFTA.SourcePruningTemplates

private theorem found_template_mem (templates : List (Template.Pattern Symbol))
    (select : Template.Pattern Symbol × Nat → Bool) (position : Nat)
    (entry : Template.Pattern Symbol × Nat)
    (found : ((templates.zipIdx.filter select).find? (fun entry => entry.2 == position)) = some entry) :
    entry.1 ∈ templates := by
  exact List.fst_mem_of_mem_zipIdx (List.mem_filter.mp (List.mem_of_find?_eq_some found)).1

/-- An actual indexed candidate belongs to the original catalog, including repeated entries. -/
theorem indexTemplates_mem (templates : List (Template.Pattern Symbol)) (term : PartialTerm)
    (pattern : Template.Pattern Symbol) (member : pattern ∈ indexTemplates templates term) :
    pattern ∈ templates := by
  cases spine : partialSpine term with
  | none => simpa only [indexTemplates, spine] using member
  | some key =>
      simp only [indexTemplates, spine] at member
      obtain ⟨position, _inside, found⟩ := List.mem_filterMap.mp member
      cases generic : ((templates.zipIdx.filter (fun entry => (templateSpine entry.1).isNone)).find?
          (fun entry => entry.2 == position)) with
      | some entry =>
          simp only [generic, Option.map_some, Option.orElse_some] at found
          have same : entry.1 = pattern := Option.some.inj found
          rw [← same]
          exact found_template_mem templates _ position entry generic
      | none =>
          simp only [generic, Option.map_none, Option.orElse_none] at found
          cases fixed : ((templates.zipIdx.filter (fun entry => decide (templateSpine entry.1 = some key))).find?
              (fun entry => entry.2 == position)) with
          | none => simp only [fixed, Option.map_none] at found; cases found
          | some entry =>
              simp only [fixed, Option.map_some] at found
              have same : entry.1 = pattern := Option.some.inj found
              rw [← same]
              exact found_template_mem templates _ position entry fixed

end MicroCFTA.SourcePruningTemplates
