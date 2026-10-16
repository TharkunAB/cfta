import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors

namespace MicroCFTA.OutputConstructorKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedRecordCoherence
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile

private def nullary : EdgeValue Nat Nat × State Nat Nat := run (makeEdge 7 91 []) empty
private def parent : Value Nat Nat × State Nat Nat := run (makeNode [nullary.1, nullary.1]) nullary.2
private def sentinel : EdgeValue Nat Nat × State Nat Nat := run (makeEdge 8 92 [.empty]) empty

/-- Duplicate literal rows normalize to one resident row and then replay at the same whole heap. -/
theorem nullary_duplicate_and_replay :
    EdgeShape 2 0 nullary.1 ∧ NodeShape 2 0 parent.1 ∧
      (canonicalEdges (surviving [nullary.1, nullary.1])).length = 1 ∧
      run (makeNode [nullary.1, nullary.1]) parent.2 = (parent.1, parent.2) := by
  have initial : Coherent (empty (Symbol := Nat) (Guard := Nat)) := empty_correct.1
  have built := makeEdge_available 7 91 [] empty initial empty_cached (by simp)
  have linked := makeEdge_linked 7 91 [] empty initial empty_linked
  have edgeProfile : EdgeShape 2 0 nullary.1 :=
    SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeEdge 7 91 [] empty initial empty_cached
      (by simp) True.intro (by decide)
  have resident : ∀ edge ∈ [nullary.1, nullary.1], EdgeResident nullary.2 edge := by
    intro edge member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact linked.2
  have nodeProfile : NodeShape 2 0 parent.1 :=
    SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeNode [nullary.1, nullary.1] nullary.2
      built.1 linked.1 resident
      ⟨edgeProfile, edgeProfile, True.intro⟩ (by decide)
  have childless : nullary.1.children = [] :=
    InternedShallowValues.makeEdge_children 7 91 [] empty initial empty_cached (by simp)
  have normalized : canonicalEdges (surviving [nullary.1, nullary.1]) = [nullary.1] := by
    simp [surviving, childless, canonicalEdges, EnumerationBuilderCaches.canonicalIds, List.eraseDups_cons]
  exact ⟨edgeProfile, nodeProfile, by rw [normalized]; rfl,
    replay (makeNode [nullary.1, nullary.1]) nullary.2 parent.2 built.1.valid (grows_refl _)⟩

/-- An actual one-child sentinel retains arity one before node construction removes it. -/
theorem sentinel_erasure :
    EdgeShape 0 1 sentinel.1 ∧ ¬ EdgeShape 0 0 sentinel.1 ∧
      run (makeNode [sentinel.1]) sentinel.2 = (.empty, sentinel.2) := by
  have initial : Coherent (empty (Symbol := Nat) (Guard := Nat)) := empty_correct.1
  have available : ∀ value ∈ ([.empty] : List (Value Nat Nat)), Available empty value := by
    intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact empty_available _
  have edgeProfile := SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeEdge 8 92 [.empty] empty
    initial empty_cached available (rowLimit := 0) (arityLimit := 1) ⟨True.intro, True.intro⟩ (by decide)
  refine ⟨edgeProfile, ?_, ?_⟩
  · intro impossible
    have bounded := EdgeShape.arity sentinel.1 impossible
    change 1 ≤ 0 at bounded
    omega
  · have children : sentinel.1.children = [.empty] :=
      InternedShallowValues.makeEdge_children 8 92 [.empty] empty initial empty_cached available
    have erased := InternedErasedEdgeReplay.makeNode_erases ([] : List (EdgeValue Nat Nat)) sentinel.1
      (by rw [children]; simp [Value.referenceOf])
    change run (makeNode ([] ++ [sentinel.1])) sentinel.2 = _
    rw [erased]
    simp [makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds, run]

/-- Every actual normalized node output retains the same profile on a whole-heap warm replay. -/
theorem arbitrary_warm_node {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    {rows arity : Nat} (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (coherent : Coherent before) (linked : Linked before)
    (resident : ∀ edge ∈ edges, EdgeResident before edge)
    (profile : RowsShape rows arity edges) (rowBound : edges.length ≤ rows) :
    let built := run (makeNode edges) before
    NodeShape rows arity built.1 ∧
      run (makeNode edges) built.2 = (built.1, built.2) ∧
      NodeShape rows arity (run (makeNode edges) built.2).1 := by
  dsimp only
  have result := SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeNode edges before coherent linked resident profile rowBound
  have repeated := replay (makeNode edges) before (run (makeNode edges) before).2 coherent.valid (grows_refl _)
  exact ⟨result, repeated, by rw [repeated]; exact result⟩

/-- Positional child results derive the actual edge profile without an equal-arity or closure premise. -/
theorem ordered_child_constructor {Symbol Guard Input : Type} [DecidableEq (EdgeKey Symbol Guard)]
    {rows arity : Nat} {inputs : List Input} {values : List (Value Symbol Guard)}
    (actual : Language.All₂ (fun _ value => NodeShape rows arity value) inputs values)
    (bound : inputs.length ≤ arity) (symbol : Symbol) (guard : Guard) (before : State Symbol Guard)
    (coherent : Coherent before) (cached : Cached before)
    (available : ∀ value ∈ values, Available before value) :
    EdgeShape rows arity (run (makeEdge symbol guard values) before).1 := by
  obtain ⟨profile, length⟩ := SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.children_of_all₂ actual
  exact SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeEdge symbol guard values before coherent cached available
    profile (length ▸ bound)

#print axioms nullary_duplicate_and_replay
#check @nullary_duplicate_and_replay
#print axioms sentinel_erasure
#check @sentinel_erasure
#print axioms arbitrary_warm_node
#check @arbitrary_warm_node
#print axioms ordered_child_constructor
#check @ordered_child_constructor
end MicroCFTA.OutputConstructorKernels
