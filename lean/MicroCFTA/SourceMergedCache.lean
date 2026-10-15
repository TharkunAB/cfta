import MicroCFTA.SourceMergedSelectionLanguage
import MicroCFTA.MergedColdMerge

/-!
# General semantic caches for retained merged columns

Actual union construction preserves all semantic heaps. The ordinary
column branch concatenates stored edges only after its boundary check.
Its independent language is exactly the union of its closed operands.
-/
namespace MicroCFTA.SourceMergedCache
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open InternedGuardedLanguage (meaning)
open InternedEdgeResidency (nodeEdges)
open MergedOrdinaryHeight

/-- Actual retained union construction preserves complete semantic caches and closed availability. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values) :
    let result := run (makeUnion values) before
    Effect before result.2 ∧ Available result.2 result.1 ∧ result.1.free = [] := by
  have facts := semantic.ready.semantic.1.normal.facts
  have checked := InternedNestedFacts.union_verified values before facts available
  have unchanged := InternedShallowHeap.makeUnion_noNewMu values before
  have ready : Ready (run (makeUnion values) before).2 :=
    ⟨SourceRecursiveIntersectionSemanticHeap.union values before semantic.ready.semantic available,
      InternedNestedCoverage.run_covered _ before facts.coherent.valid semantic.ready.covered,
      InternedOpenDepthReadback.preserve before _ semantic.ready.depth unchanged⟩
  exact ⟨⟨⟨ready, checked.growth, checked.history⟩,
    ⟨ready, InternedGuardedProbeHeap.preserve before _ semantic.guarded unchanged,
      InternedGuardedBudgetProbeHeap.preserve before _ semantic.budget unchanged⟩⟩,
    checked.result _ _ rfl, MergedColdReaderClosedInputs.makeUnion_closed values before facts available closed⟩

/-- Stored ordinary edges inherit the actual closed operand invariants. -/
theorem ordinary_rows (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    Edges before (values.flatMap nodeEdges) ∧ ClosedEdges (values.flatMap nodeEdges) := by
  have facts := semantic.ready.semantic.1.normal.facts
  constructor
  · intro edge member
    obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
    exact InternedEdgeResidency.resident_edges before facts.linked value (available value included).resident edge present
  · intro edge member child selected
    obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
    cases value with
    | node entry edges depth free =>
        exact closed_child before facts.coherent entry edges depth free (available _ included).resident
          (closed _ included) edge present child selected
    | empty | reference | mu | union => simp [nodeEdges] at present

/-- The boundary-checked ordinary union has exactly the independent operand language. -/
theorem ordinary_exact [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) (boundary : values.any recursiveBoundary = false) :
    let result := run (ordinaryUnion values) before
    Effect before result.2 ∧ Available result.2 result.1 ∧ result.1.free = [] ∧
      ∀ term, meaning holds ambient result.1 term ↔ ∃ value ∈ values, meaning holds ambient value term := by
  have rows := ordinary_rows values before semantic available closed
  have checked := SourceEqualityRequiredCache.node _ before semantic.ready rows.1 rows.2
  refine ⟨⟨checked.1, SourceEqualityRequiredSemanticCache.node _ before semantic rows.1 rows.2⟩,
    checked.2.1, checked.2.2.1, ?_⟩
  intro term
  unfold ordinaryUnion
  rw [MergedColdInterpretation.makeNode_exact before semantic.ready.semantic.1.normal.facts
    (meaning holds ambient) _ rows.1 holds (InternedGuardedLanguage.laws holds ambient) term]
  constructor
  · rintro ⟨edge, member, accepted⟩
    obtain ⟨value, included, present⟩ := List.mem_flatMap.mp member
    rcases ordinary_operand value (closed value included) (Bool.eq_false_iff.mpr ((List.any_eq_false.mp boundary) value included)) with same | ⟨entry, edges, depth, free, same⟩
    · subst value; simp [nodeEdges] at present
    · subst value
      exact ⟨_, included, ((InternedGuardedLanguage.laws holds ambient).node entry edges depth free term).mpr ⟨edge, present, accepted⟩⟩
  · rintro ⟨value, included, accepted⟩
    rcases ordinary_operand value (closed value included) (Bool.eq_false_iff.mpr ((List.any_eq_false.mp boundary) value included)) with same | ⟨entry, edges, depth, free, same⟩
    · subst value; exact False.elim ((InternedGuardedLanguage.laws holds ambient).empty term accepted)
    · subst value
      obtain ⟨edge, present, accepted⟩ := ((InternedGuardedLanguage.laws holds ambient).node entry edges depth free term).mp accepted
      exact ⟨edge, List.mem_flatMap.mpr ⟨_, included, present⟩, accepted⟩

end MicroCFTA.SourceMergedCache
