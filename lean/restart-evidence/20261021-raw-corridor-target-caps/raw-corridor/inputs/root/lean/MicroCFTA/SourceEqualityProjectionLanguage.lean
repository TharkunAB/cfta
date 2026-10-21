import MicroCFTA.SourceEqualityProjectionComplete

/-!
# Accepted subterms remain in general source path projections

Projection discards ancestor guards. Its language can contain more terms
than the subterms of accepted original terms. The theorem proves inclusion.
-/
namespace MicroCFTA.SourceEqualityProjectionLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open InternedGuardedLanguage (meaning)

/-- Ordered forest acceptance retains a selected child and its term. -/
theorem all₂_selected {values : List A} {terms : List B} {relation : A → B → Prop}
    (accepted : All₂ relation values terms) (index : Nat) (term : B) (found : terms[index]? = some term) :
    ∃ value, values[index]? = some value ∧ relation value term := by
  induction accepted generalizing index with
  | nil => simp at found
  | @cons value term' values terms first rest ih =>
      cases index with
      | zero => cases Option.some.inj found; exact ⟨value, rfl, first⟩
      | succ index => exact ih index found

/-- Signed forest selection retains the source negative-index behavior. -/
theorem all₂_signed {values : List A} {terms : List B} {relation : A → B → Prop}
    (accepted : All₂ relation values terms) (index : Int) (term : B) (found : select terms index = some term) :
    ∃ value, select values index = some value ∧ relation value term := by
  unfold select at found ⊢
  split at found
  · cases found
  · rename_i nonnegative
    obtain ⟨value, selected, related⟩ := all₂_selected accepted index.toNat term found
    exact ⟨value, by simp only [nonnegative, ite_false, selected], related⟩

private def NodeIncluded (path : List Int) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) : Prop :=
  SemanticReady before → Available before value → value.free = [] →
    ∀ holds ambient term part, meaning holds ambient value term → SymbolicSignedPaths.lookup term path = some part →
      meaning holds ambient result part

private def RowsIncluded (path : List Int) (index : Int) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) : Prop :=
  SemanticReady before → Edges before edges → ClosedEdges edges →
    ∀ holds ambient edge, edge ∈ edges → ∀ child, select edge.children index = some child →
      ∀ term part, meaning holds ambient child term → SymbolicSignedPaths.lookup term path = some part →
        ∃ result ∈ results, meaning holds ambient result part

private theorem included [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after → NodeIncluded path value before result) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsIncluded path index edges before results) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeIncluded [] value state value := by
    intro value state _ _ _ holds ambient term part accepted selected
    cases Option.some.inj selected
    exact accepted
  have emptyCase : ∀ {index path state}, NodeIncluded (index :: path) (.empty : Value Symbol Guard) state .empty := by
    intro index path state _ _ _ holds ambient term part impossible
    exact False.elim ((InternedGuardedLanguage.laws holds ambient).empty term impossible)
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      SourceEqualityProjectionUnion.Union values middle result after → RowsIncluded path index edges before values →
      NodeIncluded (index :: path) (.node entry edges depth free) before result := by
    intro path index edges before values middle result after entry depth free rows union ih semantic available closed holds ambient term part accepted selected
    have facts := semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
    have closedEdges := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
    have effects := SourceEqualityProjectionEffects.rows rows semantic resident closedEdges
    have unionExact := (union.verified effects.2.1 effects.2.2.1 effects.2.2.2).2.2.2.2 holds ambient part
    obtain ⟨edge, member, terms, rfl, children, guard⟩ := (InternedGuardedLanguage.laws holds ambient).node entry edges depth free term |>.mp accepted
    rw [SourceEqualityNeededMeaning.lookup_cons] at selected
    obtain ⟨subterm, atIndex, atPath⟩ := Option.bind_eq_some_iff.mp selected
    have atIndex' : select terms index = some subterm := atIndex
    obtain ⟨child, childFound, childAccepted⟩ := all₂_signed children index subterm atIndex'
    exact unionExact.mpr (ih semantic resident closedEdges holds ambient edge member child childFound subterm part childAccepted atPath)
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeIncluded (index :: path) exposed middle result → NodeIncluded (index :: path) original before result := by
    intro original before exposed middle path index result after _ head _ ih semantic available closed holds ambient term part accepted selected
    have checked := head.verified semantic.ready available closed
    exact ih (SourceEqualityRequiredSemanticCache.head head semantic available closed) checked.2.1 checked.2.2.1 holds ambient term part
      ((SourceEqualityRequiredHeadLanguage.head_exact head semantic available closed holds ambient term).mpr accepted) selected
  have nilCase : ∀ {path index state}, RowsIncluded path index ([] : List (EdgeValue Symbol Guard)) state [] := by
    intro path index state _ _ _ holds ambient edge impossible
    cases impossible
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsIncluded path index edges before results → RowsIncluded path index (edge :: edges) before results := by
    intro edge path index edges before results after absent _ ih semantic resident closed holds ambient original member child found term part accepted selected
    rcases List.mem_cons.mp member with rfl | tail
    · rw [absent] at found; cases found
    · exact ih semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member))
        (fun edge member => closed edge (List.mem_cons_of_mem _ member)) holds ambient original tail child found term part accepted selected
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeIncluded path child before result →
      RowsIncluded path index edges middle results → RowsIncluded path index (edge :: edges) before (result :: results) := by
    intro edge index child path before result middle edges results after found first rest firstIH restIH semantic resident closed holds ambient original member selectedChild selectedAt term part accepted selected
    have childMember := select_member found
    have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child childMember
    have childClosed := closed edge List.mem_cons_self child childMember
    rcases List.mem_cons.mp member with rfl | tail
    · have same := Option.some.inj (found.symm.trans selectedAt)
      subst selectedChild
      exact ⟨result, List.mem_cons_self, firstIH semantic childAvailable childClosed holds ambient term part accepted selected⟩
    · have firstEffects := SourceEqualityProjectionEffects.node first semantic childAvailable childClosed
      obtain ⟨value, member, accepted⟩ := restIH firstEffects.2.1
        (fun edge member => InternedEdgeResidency.edge_grows before middle firstEffects.1.growth edge (resident edge (List.mem_cons_of_mem _ member)))
        (fun edge member => closed edge (List.mem_cons_of_mem _ member)) holds ambient original tail selectedChild selectedAt term part accepted selected
      exact ⟨value, List.mem_cons_of_mem _ member, accepted⟩
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun path value before result _ _ => NodeIncluded path value before result)
      (motive_2 := fun path index edges before results _ _ => RowsIncluded path index edges before results)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun path value before result _ _ => NodeIncluded path value before result)
      (motive_2 := fun path index edges before results _ _ => RowsIncluded path index edges before results)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Every selected subterm of an accepted original term is accepted by the actual projection. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) : NodeIncluded path value before result := included.1 _ _ _ _ _ trace

end MicroCFTA.SourceEqualityProjectionLanguage
