import MicroCFTA.SourceInternedIntersectionRowsAcyclic

/-!
# Plain acyclic records and the existing physical graph

Plain records contain only EmptyNode and ordinary nodes. They have no union
or binder exposure. The structural language is therefore the existing
physical epsilon language. The ordinary intersection kernel returns this
same record class through actual canonical cache readback.
-/
namespace MicroCFTA.SourceInternedIntersectionRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency MergedPhysicalGroupCalls Language

/-- Plain acyclic input consists of finite empty and ordinary stored records. -/
inductive Plain : Value Symbol Unit → Prop
  | empty : Plain .empty
  | node (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Unit))
      (depth : Nat) (free : List InternedBinderProtocol.Reference) :
      (∀ edge ∈ edges, ∀ child ∈ edge.children, Plain child) → Plain (.node entry edges depth free)

/-- Every ordinary child of a plain record is plain. -/
theorem Plain.children (value : Value Symbol Unit) (plain : Plain value)
    (edge : EdgeValue Symbol Unit) (member : edge ∈ nodeEdges value) (child : Value Symbol Unit)
    (inside : child ∈ edge.children) : Plain child := by
  cases plain with
  | empty => cases member
  | node entry edges depth free children => exact children edge member child inside

/-- Available plain records have no free reference in their actual cached metadata. -/
theorem plain_closed (value : Value Symbol Unit) (plain : Plain value)
    (state : State Symbol Unit) (facts : Facts state) (available : Available state value) : value.free = [] := by
  cases plain with
  | empty => rfl
  | node entry edges depth free children =>
      rw [Value.free, InternedNormalizationFree.node_free state facts.coherent entry edges depth free available.resident]
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro name member
      obtain ⟨child, included, present⟩ := (childFree_member _ name).mp member
      obtain ⟨edge, selected, inside⟩ := List.mem_flatMap.mp included
      have closed := plain_closed child (children edge selected child inside) state facts
        (available.children child (List.mem_flatMap.mpr ⟨edge, selected, inside⟩))
      rw [closed] at present
      cases present
termination_by sizeOf value
decreasing_by
  subst value
  exact child_smaller (.node entry edges depth free) edge selected child inside

/-- Actual physical constructor rows coincide with the ordinary structural reader. -/
theorem physical_rows (value : Value Symbol Unit) :
    MergedPhysicalComparison.constructorRows (fun (_ : Unit) (_ : Term Symbol) => true) value = rows value := by
  cases value <;> rfl

/-- Structural finite runs are physical runs without epsilon steps. -/
theorem structural_physical [DecidableEq Symbol] (state : State Symbol Unit) (value : Value Symbol Unit)
    (term : Term Symbol) (accepted : Accepts value term) :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true)) value term := by
  induction accepted using Language.Accepts.rec
    (motive_2 := fun values terms _ => All₂ (EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true))) values terms) with
  | node edge terms member children guard ih =>
      exact .node edge terms (by simpa only [MergedPhysicalLanguage.graph, physical_rows] using member) ih guard
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

/-- Plain records have no physical epsilon successor. -/
theorem plain_noEpsilon [DecidableEq Symbol] (state : State Symbol Unit) (value : Value Symbol Unit) (plain : Plain value) :
    MergedPhysicalComparison.successors state value = [] := by
  cases plain <;> rfl

/-- No physical run from a plain root needs binder or union exposure. -/
theorem physical_structural [DecidableEq Symbol] (state : State Symbol Unit) (value : Value Symbol Unit)
    (term : Term Symbol) (accepted : EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true)) value term)
    (plain : Plain value) : Accepts value term := by
  revert plain
  induction accepted using EpsilonUnion.Accepts.rec
    (motive_2 := fun values terms _ => (∀ value ∈ values, Plain value) → All₂ Accepts values terms) with
  | @reference value target term member accepted ih =>
      intro plain
      have none := plain_noEpsilon state value plain
      change target ∈ MergedPhysicalComparison.successors state value at member
      rw [none] at member
      cases member
  | @node value edge terms member children guard ih =>
      intro plain
      have original : edge ∈ rows value := by
        simpa only [MergedPhysicalLanguage.graph, physical_rows] using member
      apply Language.Accepts.node edge terms original _ guard
      apply ih
      intro child inside
      obtain ⟨stored, selected, rfl⟩ := List.mem_map.mp original
      exact plain.children value stored selected child inside
  | nil => exact .nil
  | @cons value term values terms head tail ihHead ihTail =>
      rename_i plain
      exact .cons (ihHead (plain value List.mem_cons_self))
        (ihTail (fun child member => plain child (List.mem_cons_of_mem _ member)))

/-- Plain physical and ordinary structural finite-term languages agree exactly. -/
theorem plain_exact [DecidableEq Symbol] (state : State Symbol Unit) (value : Value Symbol Unit)
    (plain : Plain value) (term : Term Symbol) :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true)) value term ↔ Accepts value term :=
  ⟨fun accepted => physical_structural state value term accepted plain, structural_physical state value term⟩

/-- Physical node readback preserves the plain record class, including cache hits. -/
theorem makeNode_plain [DecidableEq Symbol] (edges : List (EdgeValue Symbol Unit)) (state : State Symbol Unit)
    (facts : Facts state) (resident : Edges state edges)
    (plain : ∀ edge ∈ edges, ∀ child ∈ edge.children, Plain child) : Plain (run (makeNode edges) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have children : ∀ edge ∈ canonicalEdges (surviving edges), ∀ child ∈ edge.children, Plain child := by
    intro edge member
    exact plain edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa only [same] using selected)
    simp only [run, exactResult, identifyNode]
    exact .node _ _ _ _ (by simpa only [same] using children)

/-- Positionwise plain results make every returned child record plain. -/
theorem all₂_plain (requests : List A) (values : List (Value Symbol Unit))
    (related : All₂ (fun _ value => Plain value) requests values) : ∀ value ∈ values, Plain value := by
  induction related with
  | nil => simp
  | cons head tail ih =>
      intro value member
      rcases List.mem_cons.mp member with rfl | later
      · exact head
      · exact ih value later

/-- The finite recursive kernel returns only plain records. -/
theorem intersect_plain [DecidableEq Symbol] (fuel : Nat) (pair : Value Symbol Unit × Value Symbol Unit)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) :
    Facts (run (intersect fuel pair) state).2 ∧ Available (run (intersect fuel pair) state).2 (run (intersect fuel pair) state).1 ∧
      Plain (run (intersect fuel pair) state).1 := by
  induction fuel generalizing pair state with
  | zero => exact ⟨facts, empty_available state, .empty⟩
  | succ fuel ih =>
      let relation := fun (_ : EdgeValue Symbol Unit × EdgeValue Symbol Unit) (edge : EdgeValue Symbol Unit) =>
        ∀ child ∈ edge.children, Plain child
      have checked : ∀ edgePair ∈ pairs (nodeEdges pair.1) (nodeEdges pair.2), ∀ next, Facts next → EdgeInputs next edgePair →
          Facts (run (edge (intersect fuel) edgePair) next).2 ∧
            EdgeResident (run (edge (intersect fuel) edgePair) next).2 (run (edge (intersect fuel) edgePair) next).1 ∧
            relation edgePair (run (edge (intersect fuel) edgePair) next).1 := by
        intro edgePair _ next nextFacts nextInputs
        have built := edge_checked (intersect fuel) edgePair (fun _ value => Plain value)
          (fun request _ current currentFacts currentInputs => ih request current currentFacts currentInputs)
          next nextFacts nextInputs
        refine ⟨built.1, built.2.1, ?_⟩
        have children := built.2.2.2.2
        split at children
        · exact all₂_plain _ _ children
        · intro child member
          rw [children] at member
          rw [List.mem_singleton.mp member]
          exact .empty
      have edgeInputs : ∀ edgePair ∈ pairs (nodeEdges pair.1) (nodeEdges pair.2), EdgeInputs state edgePair := by
        intro edgePair member
        have original := (pairs_member _ _ edgePair).mp member
        exact ⟨resident_edges state facts.linked pair.1 inputs.1.resident _ original.1,
          resident_edges state facts.linked pair.2 inputs.2.resident _ original.2.1⟩
      have built := map_checked (edge (intersect fuel)) _ EdgeInputs EdgeResident relation
        edgeInputs_stable resident_stable checked state facts edgeInputs
      have result := node_verified _ _ built.1 built.2.1
      simp only [intersect, node, run_bind]
      refine ⟨result.facts, result.result _ _ rfl, makeNode_plain _ _ built.1 built.2.1 ?_⟩
      have rightProperty : ∀ (requests : List (EdgeValue Symbol Unit × EdgeValue Symbol Unit)) (edges : List (EdgeValue Symbol Unit)),
          All₂ relation requests edges → ∀ edge ∈ edges, ∀ child ∈ edge.children, Plain child := by
        intro requests edges related
        induction related with
        | nil => simp
        | cons head tail ih =>
            intro edge member
            rcases List.mem_cons.mp member with rfl | member
            · exact head
            · exact ih edge member
      exact rightProperty _ _ built.2.2

/-- The acyclic plain kernel computes common language in the existing physical graph. -/
theorem physical_finite_exact [DecidableEq Symbol] (left right : Value Symbol Unit) (state : State Symbol Unit)
    (facts : Facts state) (leftAvailable : Available state left) (rightAvailable : Available state right)
    (leftPlain : Plain left) (rightPlain : Plain right) :
    let result := run (intersect (sizeOf left) (left, right)) state
    Facts result.2 ∧ Available result.2 result.1 ∧ Plain result.1 ∧
      ∀ term, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph result.2 (fun _ _ => true)) result.1 term ↔
        EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true)) left term ∧
        EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true)) right term := by
  have exact := finite_exact left right state facts leftAvailable rightAvailable
  have plain := intersect_plain (sizeOf left) (left, right) state facts ⟨leftAvailable, rightAvailable⟩
  refine ⟨exact.1, exact.2.1, plain.2.2, ?_⟩
  intro term
  rw [plain_exact _ _ plain.2.2, plain_exact state left leftPlain, plain_exact state right rightPlain]
  exact exact.2.2 term

end MicroCFTA.SourceInternedIntersectionRows
