import MicroCFTA.MergedPhysicalGroupEdges

/-!
# Actual four-edge group processing

Small groups rebuild every row in source order. Large groups build one
unconstrained row. The constructor computations retain the actual cache
state. Child-call certificates are local to the requests that occur.
-/
namespace MicroCFTA.MergedPhysicalGroup
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalLanguage MergedPhysicalMergeContext MergedPhysicalUnion
open MergedPhysicalGroupCalls MergedPhysicalGroupEdges Language

/-- The complete small-group loop preserves each original row's fields and language. -/
theorem small_correct [DecidableEq (EdgeKey Symbol Guard)]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (certified : ∀ edge ∈ edges, ∀ child ∈ edge.children, CallLaw merge (fun value => [value]) child outputs meaning)
    (state : InternedConstructorTemplates.State Symbol Guard) (context : Context state outputs) (resident : Edges state edges) :
    let result := run (mapCalls (smallEdge merge) edges) state
    Context result.2 outputs ∧ Edges result.2 result.1 ∧
      ∀ original ∈ edges, ∃ edge ∈ result.1,
        edge.entry.key.symbol = original.entry.key.symbol ∧ edge.entry.key.constraint = original.entry.key.constraint ∧
        edge.children.length = original.children.length ∧
        ∀ term, EdgeAccepts state meaning original term → EdgeAccepts result.2 meaning edge term := by
  induction edges generalizing state with
  | nil => exact ⟨context, by simp [Edges, mapCalls, run], by simp⟩
  | cons first rest ih =>
      let head := run (smallEdge merge first) state
      let tail := run (mapCalls (smallEdge merge) rest) head.2
      have firstChecked := smallEdge_correct merge first outputs meaning (certified first List.mem_cons_self)
        state context (resident first List.mem_cons_self)
      have headGrowth := (InternedConstructorTemplates.run_correct (smallEdge merge first) state context.facts.coherent.valid).2
      have tailInputs : Edges head.2 rest := by
        intro edge member
        exact edge_grows state head.2 headGrowth edge (resident edge (List.mem_cons_of_mem _ member))
      have restChecked := ih (fun edge member => certified edge (List.mem_cons_of_mem _ member)) head.2 firstChecked.1 tailInputs
      have tailGrowth := (InternedConstructorTemplates.run_correct (mapCalls (smallEdge merge) rest) head.2 firstChecked.1.facts.coherent.valid).2
      simp only [mapCalls, run_bind, run]
      refine ⟨restChecked.1, ?_, ?_⟩
      · intro edge member
        rcases List.mem_cons.mp member with same | member
        · rw [same]; exact edge_grows head.2 tail.2 tailGrowth head.1 firstChecked.2.1
        · exact restChecked.2.1 edge member
      · intro original member
        rcases List.mem_cons.mp member with same | member
        · subst original
          refine ⟨head.1, List.mem_cons_self, firstChecked.2.2.1, firstChecked.2.2.2.1, firstChecked.2.2.2.2.1, ?_⟩
          intro term accepted
          exact edge_grow head.2 tail.2 outputs firstChecked.1 tailGrowth meaning head.1 firstChecked.2.1 term
            (firstChecked.2.2.2.2.2 term accepted)
        · obtain ⟨edge, included, symbol, guard, arity, covers⟩ := restChecked.2.2 original member
          refine ⟨edge, List.mem_cons_of_mem _ included, symbol, guard, arity, ?_⟩
          intro term accepted
          exact covers term (edge_grow state head.2 outputs context headGrowth meaning original
            (resident original (List.mem_cons_of_mem _ member)) term accepted)

/-- The source threshold counts the actual canonical rows supplied to this group. -/
def group (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (top : Guard) (edges : List (EdgeValue Symbol Guard)) : Work Symbol Guard (List (EdgeValue Symbol Guard)) :=
  if edges.length ≤ 4 then mapCalls (smallEdge merge) edges
  else match edges with
  | [] => .pure []
  | first :: rest => (largeEdge mergeUnion top first rest).bind fun edge => .pure [edge]

/-- The actual group output has at most four row occurrences before parent normalization. -/
theorem group_bound [DecidableEq (EdgeKey Symbol Guard)]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (top : Guard) (edges : List (EdgeValue Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard) :
    (run (group merge mergeUnion top edges) state).1.length ≤ 4 := by
  unfold group
  split
  · rw [mapCalls_length]; assumption
  · cases edges <;> simp [run_bind, run]

/-- Both source threshold branches derive complete available output edges and language coverage. -/
theorem group_correct [DecidableEq (EdgeKey Symbol Guard)]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool) (clear : ∀ term, meaning top term = true)
    (smallCalls : ∀ edge ∈ edges, ∀ child ∈ edge.children, CallLaw merge (fun value => [value]) child outputs meaning)
    (largeCalls : ∀ first rest, edges = first :: rest →
      ∀ column ∈ MergedAlternativesGroups.columns (edges.map EdgeValue.children) first.children.length,
        CallLaw mergeUnion id column outputs meaning)
    (state : InternedConstructorTemplates.State Symbol Guard) (context : Context state outputs)
    (resident : Edges state edges) (sameKey : SameKey edges) :
    let result := run (group merge mergeUnion top edges) state
    Context result.2 outputs ∧ Edges result.2 result.1 ∧ result.1.length ≤ 4 ∧
      ∀ original ∈ edges, ∃ edge ∈ result.1,
        edge.entry.key.symbol = original.entry.key.symbol ∧ edge.children.length = original.children.length ∧
        (edge.entry.key.constraint = original.entry.key.constraint ∨ edge.entry.key.constraint = top) ∧
        ∀ term, EdgeAccepts state meaning original term → EdgeAccepts result.2 meaning edge term := by
  have bound := group_bound merge mergeUnion top edges state
  by_cases small : edges.length ≤ 4
  · simp only [group, small, ↓reduceIte] at bound ⊢
    have checked := small_correct merge edges outputs meaning smallCalls state context resident
    refine ⟨checked.1, checked.2.1, bound, ?_⟩
    intro original member
    obtain ⟨edge, included, symbol, guard, arity, covers⟩ := checked.2.2 original member
    exact ⟨edge, included, symbol, arity, Or.inl guard, covers⟩
  · cases edges with
    | nil => simp at small
    | cons first rest =>
        have checked := largeEdge_correct mergeUnion top first rest outputs meaning clear (largeCalls first rest rfl)
          state context resident sameKey
        simp only [group, small, ↓reduceIte, run_bind, run]
        refine ⟨checked.1, ?_, by simp, ?_⟩
        · intro edge included
          rw [List.mem_singleton.mp included]
          exact checked.2.1
        · intro original member
          obtain ⟨symbol, arity⟩ := sameKey original member first List.mem_cons_self
          exact ⟨_, List.mem_singleton_self _, checked.2.2.1.trans symbol.symm,
            checked.2.2.2.2.1.trans arity.symm, Or.inr checked.2.2.2.1, checked.2.2.2.2.2 original member⟩

/-- Parent construction interns the actual group output after every child and edge effect. -/
def build (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (top : Guard) (edges : List (EdgeValue Symbol Guard)) : Work Symbol Guard (Value Symbol Guard) :=
  (group merge mergeUnion top edges).bind makeNode

/-- A completed group and actual parent node include every original group's accepted term. -/
theorem build_covers [DecidableEq (EdgeKey Symbol Guard)]
    (merge : Value Symbol Guard → Work Symbol Guard (Value Symbol Guard))
    (mergeUnion : List (Value Symbol Guard) → Work Symbol Guard (Value Symbol Guard))
    (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool) (clear : ∀ term, meaning top term = true)
    (smallCalls : ∀ edge ∈ edges, ∀ child ∈ edge.children, CallLaw merge (fun value => [value]) child outputs meaning)
    (largeCalls : ∀ first rest, edges = first :: rest →
      ∀ column ∈ MergedAlternativesGroups.columns (edges.map EdgeValue.children) first.children.length,
        CallLaw mergeUnion id column outputs meaning)
    (state : InternedConstructorTemplates.State Symbol Guard) (context : Context state outputs)
    (resident : Edges state edges) (sameKey : SameKey edges) :
    let result := run (build merge mergeUnion top edges) state
    Context result.2 outputs ∧ Available result.2 result.1 ∧
      ∀ original ∈ edges, ∀ term, EdgeAccepts state meaning original term →
        EpsilonUnion.Accepts (graph result.2 meaning) result.1 term := by
  let merged := run (group merge mergeUnion top edges) state
  have checked := group_correct merge mergeUnion top edges outputs meaning clear smallCalls largeCalls state context resident sameKey
  have built := checked.1.makeNode merged.2 outputs merged.1 checked.2.1
  have growth := (InternedConstructorTemplates.run_correct (makeNode merged.1) merged.2 checked.1.facts.coherent.valid).2
  simp only [build, run_bind]
  refine ⟨built.1, built.2, ?_⟩
  intro original member term accepted
  obtain ⟨edge, included, _, _, _, covers⟩ := checked.2.2.2 original member
  apply (makeNode_exact merged.2 _ checked.1.facts merged.1 checked.2.1 meaning term).mpr
  exact ⟨edge, included, edge_grow merged.2 _ outputs checked.1 growth meaning edge (checked.2.1 edge included) term (covers term accepted)⟩

end MicroCFTA.MergedPhysicalGroup
