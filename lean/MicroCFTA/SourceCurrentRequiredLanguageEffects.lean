import MicroCFTA.SourceCurrentRequiredComplete

/-!
# Actual required-child and row effects on the maximal-tip domain

Each selected original child has its stored Needed domain. Completed node
requests derive their effects from finite completion. Actual child and row
graphs then retain semantic readiness, availability, and constructor history.
No output-closedness or later support premise is supplied.
-/
namespace MicroCFTA.SourceCurrentRequiredLanguageEffects
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (edge_grows)
open SourceEqualityNeeded SourceEqualityNeededNonnegative SourceEqualityRequiredGraph
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceCurrentRequiredSupport

/-- Each existing child uses the stored requirement at its original offset. -/
def ChildrenSupport [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (entries : List (Int × Needed)) (offset : Nat) (values : List (Value Symbol Guard)) : Prop :=
  ∀ query needed, SourceEqualityNeededMap.lookup (Int.ofNat (offset + query)) entries = some needed →
    ∀ value, values[query]? = some value → NodeSupport unconstrained anchor needed value

/-- Removing the first original child increments its actual source offset. -/
theorem children_tail [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    {entries : List (Int × Needed)} {offset : Nat} {value : Value Symbol Guard} {values : List (Value Symbol Guard)}
    (support : ChildrenSupport unconstrained anchor entries offset (value :: values)) :
    ChildrenSupport unconstrained anchor entries (offset + 1) values := by
  intro query needed found child selected
  exact support (query + 1) needed
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found) child selected

/-- Every actual supported child scan retains the exact returned semantic heap and values. -/
theorem children_verified [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard}
    (trace : RequireChildren entries index values before results after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (support : ChildrenSupport unconstrained anchor entries index values) :
    Keeps before after ∧ SemanticReady after ∧ Values after results := by
  induction values generalizing index results before after with
  | nil =>
      cases trace
      exact ⟨pure_keeps before semantic.ready, semantic, by simp [Values]⟩
  | cons value values ih =>
      have firstAvailable := available value List.mem_cons_self
      have restAvailable : Values before values := fun child member => available child (List.mem_cons_of_mem _ member)
      cases trace with
      | unselected index absent rest =>
          obtain ⟨kept, afterSemantic, resident⟩ := ih rest semantic restAvailable growth (children_tail support)
          refine ⟨kept, afterSemantic, ?_⟩
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact kept.available _ firstAvailable
          · exact resident child member
      | selected index found first rest =>
          have member := SourceEqualityNeededMap.lookup_mem _ entries _ found
          have childValid := (show SourceEqualityNeededMap.Ascending entries ∧
            ∀ key child, (key, child) ∈ entries → SourceEqualityNeeded.Valid child from
            by simpa only [SourceEqualityNeeded.Valid] using valid).2 _ _ member
          have childNonnegative := (show ∀ key child, (key, child) ∈ entries → 0 ≤ key ∧ Nonnegative child from
            by simpa only [Nonnegative] using nonnegative) _ _ member
          obtain ⟨firstKept, middleSemantic, resident⟩ := SourceCurrentRequiredComplete.node_verified unconstrained anchor
            anchorSemantic first childValid childNonnegative.2 semantic firstAvailable growth
              (support 0 _ (by simpa using found) value rfl)
          obtain ⟨restKept, afterSemantic, restResident⟩ := ih rest middleSemantic
            (fun child member => firstKept.available _ (restAvailable child member))
            (grows_trans growth firstKept.growth) (children_tail support)
          refine ⟨firstKept.trans restKept, afterSemantic, ?_⟩
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact restKept.available _ resident
          · exact restResident child member

/-- Every actual supported row graph retains the exact semantic heap and resident rebuilt edges. -/
theorem rows_verified [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
    {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (trace : RequireRows entries edges before results after)
    (valid : SourceEqualityNeeded.Valid (.node entries)) (nonnegative : Nonnegative (.node entries))
    (semantic : SemanticReady before) (resident : Edges before edges) (growth : Grows anchor before)
    (support : RowsSupport unconstrained anchor (.node entries) edges) :
    Keeps before after ∧ SemanticReady after ∧ Edges after results := by
  induction edges generalizing results before after with
  | nil =>
      cases trace
      exact ⟨pure_keeps before semantic.ready, semantic, by simp [Edges]⟩
  | cons edge edges ih =>
      have restResident : Edges before edges := fun original member => resident original (List.mem_cons_of_mem _ member)
      have restSupport : RowsSupport unconstrained anchor (.node entries) edges :=
        fun original member => support original (List.mem_cons_of_mem _ member)
      cases trace with
      | rejected doesNotFit rest => exact ih rest semantic restResident growth restSupport
      | @kept _ _ values middle result afterEdge _ _ _ _ doesFit children rebuilt rest =>
          have available : Values before edge.children := semantic.ready.semantic.1.normal.facts.cached.edges
            edge.entry.key edge (resident edge List.mem_cons_self)
          obtain ⟨childKept, middleSemantic, valuesAvailable⟩ := children_verified unconstrained anchor anchorSemantic
            children valid nonnegative semantic available growth
              (by simpa only [ChildrenSupport, ForestSupport, Nat.zero_add] using support edge List.mem_cons_self)
          have built := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle
            middleSemantic.ready valuesAvailable
          have afterSemantic : SemanticReady afterEdge := by
            simpa only [rebuilt] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol
              edge.entry.key.constraint values middle middleSemantic valuesAvailable
          have edgeKept : Keeps middle afterEdge := by simpa only [rebuilt] using built.1
          have edgeResident : InternedEdgeResidency.EdgeResident afterEdge result := by
            simpa only [rebuilt] using built.2.1
          have firstKept := childKept.trans edgeKept
          obtain ⟨restKept, ready, residentResults⟩ := ih rest afterSemantic
            (fun original member => edge_grows before afterEdge firstKept.growth original (restResident original member))
            (grows_trans growth firstKept.growth) restSupport
          refine ⟨firstKept.trans restKept, ready, ?_⟩
          intro original member
          rcases List.mem_cons.mp member with rfl | member
          · exact edge_grows afterEdge after restKept.growth _ edgeResident
          · exact residentResults original member

end MicroCFTA.SourceCurrentRequiredLanguageEffects
