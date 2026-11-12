import MicroCFTA.SourceNativeOrdinaryRows
import MicroCFTA.SourceNativeReadArityHeap
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds
import MicroCFTA.NumberedTerms
import MicroCFTA.GraphBudget

/-!
# Accepted-term size in the current ordinary native component

Every selected edge retains the current physical child-count cap.
The existing ordinary-height recurrence bounds all accepted constructors.
The theorem observes the current component and keeps the full guards.
-/
namespace MicroCFTA.SourceNativeOrdinaryTermSize
open Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceNativeBoundDepthMeaning (DeepOrdinary)
open SourceNativeReadArityHeap (Heap)
open InternedGuardedLanguage (meaning Env)
open SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds (nodeCount nodeCount_mono)

private theorem forestSize_eq_sum (terms : List (Term Symbol)) :
    NumberedTerms.forestSize terms = (terms.map NumberedTerms.size).sum := by
  induction terms with
  | nil => rfl
  | cons first rest ih =>
      simp only [NumberedTerms.forestSize, List.map_cons, List.sum_cons, ih]

private theorem all₂_right {relation : A → B → Prop} {as : List A} {bs : List B}
    (related : All₂ relation as bs) (value : B) (member : value ∈ bs) :
    ∃ state ∈ as, relation state value := by
  induction related with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, by simp, head⟩
      · obtain ⟨state, present, accepted⟩ := ih member
        exact ⟨state, by simp [present], accepted⟩

/-- Every accepted term has the size bound of the same current ordinary component. -/
theorem accepted_size (state : State Symbol Guard) (semantic : SemanticReady state)
    (arity : Nat) (heap : Heap arity state) (value : Value Symbol Guard)
    (available : Available state value) (ordinary : DeepOrdinary value)
    (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (term : Term Symbol) (accepted : meaning holds ambient value term) :
    NumberedTerms.size term ≤ nodeCount 1 arity (MergedOrdinaryHeight.height value) := by
  let facts := semantic.ready.semantic.1.normal.facts
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, ∀ value, Available state value → DeepOrdinary value →
      meaning holds ambient value term →
        NumberedTerms.size term ≤ nodeCount 1 arity (MergedOrdinaryHeight.height value)) generalizing value with
  | node symbol children ih =>
      cases ordinary with
      | empty =>
          exact False.elim ((InternedGuardedLanguage.laws holds ambient).empty (.node symbol children) accepted)
      | node entry edges depth free deepChildren =>
          obtain ⟨edge, member, terms, root, runs, _guard⟩ :=
            ((InternedGuardedLanguage.laws holds ambient).node entry edges depth free (.node symbol children)).mp accepted
          have sameTerms : terms = children := (Term.node.inj root).2.symm
          subst terms
          have edgeBound : edge.children.length ≤ arity :=
            heap edge.entry.key edge
              (resident_edges state facts.linked (.node entry edges depth free) available.resident edge member)
          have childBound : ∀ child ∈ children, NumberedTerms.size child ≤
              nodeCount 1 arity (MergedOrdinaryHeight.edgesHeight edges) := by
            intro child included
            obtain ⟨original, present, childAccepted⟩ := all₂_right runs child included
            have childAvailable := SourceNativeOrdinaryRows.child_available state facts
              (.node entry edges depth free) available edge member original present
            have smaller := MergedOrdinaryHeight.child_lt entry edges depth free edge member original present
            have heightBound : MergedOrdinaryHeight.height original ≤ MergedOrdinaryHeight.edgesHeight edges := by
              simp only [MergedOrdinaryHeight.height] at smaller
              omega
            exact Nat.le_trans
              (ih child included original childAvailable (deepChildren edge member original present) childAccepted)
              (nodeCount_mono 1 arity heightBound)
          have lengthBound : children.length ≤ arity :=
            Nat.le_trans (Nat.le_of_eq (All₂.length_eq runs).symm) edgeBound
          have forestBound : NumberedTerms.forestSize children ≤
              arity * nodeCount 1 arity (MergedOrdinaryHeight.edgesHeight edges) := by
            rw [forestSize_eq_sum]
            exact Nat.le_trans (GraphBudget.sum_bound children NumberedTerms.size _ childBound)
              (Nat.mul_le_mul_right _ lengthBound)
          simpa only [NumberedTerms.size, MergedOrdinaryHeight.height, nodeCount, Nat.one_mul] using
            Nat.add_le_add_left forestBound 1
  | nil => simp_all
  | cons first rest head tail =>
      rename_i term member value available ordinary accepted
      rcases List.mem_cons.mp member with rfl | member
      · exact head value available ordinary accepted
      · exact tail term member value available ordinary accepted

end MicroCFTA.SourceNativeOrdinaryTermSize
