import MicroCFTA.SourceRecursiveIntersectionKernelCalls
import MicroCFTA.InternedShallowValues

/-!
# Actual leaf-row products without recursive child requests

A zero-arity row either meets another zero-arity row or takes the
arity-mismatch branch. Neither case evaluates a recursive child request.
The ordered row walk therefore completes. Node normalization removes the
mismatch rows and returns a closed value. The optional binder then returns
that value without further constructor effects. All actual edge and node
cache effects remain in the returned machine.
-/
namespace MicroCFTA.SourceRecursiveIntersectionLeafNode
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedEdgeResidency InternedNormalizationFree
open SourceRecursiveIntersectionKernel
open EqualityLeafProjectionPhysical (dead)

variable {Symbol Guard : Type}

private theorem edge_work [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : Machine Symbol Guard) (facts : Facts state.heap)
    (inputs : ∀ value ∈ values, Available state.heap value)
    (shape : values = [] ∨ values = [.empty]) :
    ∃ row after, work (makeEdge symbol guard values) state = .done row after ∧
      Facts after.heap ∧ Grows state.heap after.heap ∧ EdgeResident after.heap row ∧
      (dead row = false → row.children = []) := by
  let made := run (makeEdge symbol guard values) state.heap
  have checked := edge_verified symbol guard values state.heap facts inputs
  have children := InternedShallowValues.makeEdge_children symbol guard values state.heap
    facts.coherent facts.cached inputs
  refine ⟨made.1, {state with heap := made.2}, rfl, checked.facts, checked.growth,
    checked.result _ _ rfl, ?_⟩
  intro live
  rcases shape with nil | singleton
  · exact children.trans nil
  · have impossible : dead made.1 = true := by
      change (run (makeEdge symbol guard values) state.heap).1.children.any
        (fun child => child.referenceOf == .empty) = true
      rw [children, singleton]
      rfl
    simp [impossible] at live

/-- Every actual leaf edge completes without evaluating its supplied child caller. -/
theorem edge_leaf_complete [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard →
      Result Symbol Guard (Value Symbol Guard))
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard)
    (facts : Facts state.heap) (leaf : left.children = []) :
    ∃ row after, edge emptyGuard conjoin call left right state = .done row after ∧
      Facts after.heap ∧ Grows state.heap after.heap ∧ EdgeResident after.heap row ∧
      (dead row = false → row.children = []) := by
  by_cases arity : left.children.length = right.children.length
  · have exactCall : edge emptyGuard conjoin call left right state =
        work (makeEdge left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint) []) state := by
      unfold edge
      simp only [arity, ↓reduceIte]
      rw [leaf]
      rfl
    rw [exactCall]
    exact edge_work _ _ [] state facts (by intro value member; cases member) (Or.inl rfl)
  · have exactCall : edge emptyGuard conjoin call left right state =
        work (makeEdge left.entry.key.symbol emptyGuard [.empty]) state := by
      simp only [edge, arity, ↓reduceIte]
    rw [exactCall]
    exact edge_work _ _ [.empty] state facts (by
      intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact empty_available state.heap) (Or.inr rfl)

/-- A right leaf also prevents every recursive child request, regardless of operand order. -/
theorem edge_right_leaf_complete [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard →
      Result Symbol Guard (Value Symbol Guard))
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard)
    (facts : Facts state.heap) (leaf : right.children = []) :
    ∃ row after, edge emptyGuard conjoin call left right state = .done row after ∧
      Facts after.heap ∧ Grows state.heap after.heap ∧ EdgeResident after.heap row ∧
      (dead row = false → row.children = []) := by
  by_cases arity : left.children.length = right.children.length
  · have leftLeaf : left.children = [] := by
      cases selected : left.children with
      | nil => rfl
      | cons first rest => simp [selected, leaf] at arity
    exact edge_leaf_complete emptyGuard conjoin call left right state facts leftLeaf
  · have exactCall : edge emptyGuard conjoin call left right state =
        work (makeEdge left.entry.key.symbol emptyGuard [.empty]) state := by
      simp only [edge, arity, ↓reduceIte]
    rw [exactCall]
    exact edge_work _ _ [.empty] state facts (by
      intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact empty_available state.heap) (Or.inr rfl)

private theorem walk_leaf_complete [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard →
      Result Symbol Guard (Value Symbol Guard))
    (jobs : List (EdgeValue Symbol Guard × EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (facts : Facts state.heap)
    (leaves : ∀ job ∈ jobs, job.1.children = [] ∨ job.2.children = []) :
    ∃ rows final,
      walk (fun job => edge emptyGuard conjoin call job.1 job.2) jobs state = .done rows final ∧
      Facts final.heap ∧ Grows state.heap final.heap ∧
      (∀ row ∈ rows, EdgeResident final.heap row) ∧
      (∀ row ∈ rows, dead row = false → row.children = []) := by
  induction jobs generalizing state with
  | nil =>
      refine ⟨[], state, rfl, facts, grows_refl _, ?_, ?_⟩
      · intro row member
        cases member
      · intro row member
        cases member
  | cons first rest ih =>
      have firstComplete : ∃ row after,
          edge emptyGuard conjoin call first.1 first.2 state = .done row after ∧
          Facts after.heap ∧ Grows state.heap after.heap ∧ EdgeResident after.heap row ∧
          (dead row = false → row.children = []) := by
        rcases leaves first List.mem_cons_self with left | right
        · exact edge_leaf_complete emptyGuard conjoin call first.1 first.2 state facts left
        · exact edge_right_leaf_complete emptyGuard conjoin call first.1 first.2 state facts right
      obtain ⟨row, after, firstDone, afterFacts, firstGrowth, resident, leaf⟩ := firstComplete
      obtain ⟨rows, final, restDone, finalFacts, restGrowth, residents, remaining⟩ :=
        ih after afterFacts (fun job member => leaves job (List.mem_cons_of_mem _ member))
      refine ⟨row :: rows, final, ?_, finalFacts, grows_trans firstGrowth restGrowth, ?_, ?_⟩
      · simp only [walk, firstDone, Result.bind, restDone]
      · intro actual member
        rcases List.mem_cons.mp member with rfl | tail
        · exact edge_grows after.heap final.heap restGrowth actual resident
        · exact residents actual tail
      · intro actual member
        rcases List.mem_cons.mp member with rfl | tail
        · exact leaf
        · exact remaining actual tail

/-- Actual node normalization removes every non-leaf row in this product. -/
theorem makeNode_leaf_free [DecidableEq (EdgeKey Symbol Guard)]
    (rows : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (residents : ∀ row ∈ rows, EdgeResident state row)
    (leaves : ∀ row ∈ rows, dead row = false → row.children = []) :
    (run (makeNode rows) state).1.free = [] := by
  rw [makeNode_free rows state facts.coherent facts.linked residents]
  have noChildren : (canonicalEdges (surviving rows)).flatMap EdgeValue.children = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro row member
    have original := List.mem_filter.mp (canonicalEdges_member _ row member)
    apply leaves row original.1
    have selected : (!dead row) = true := original.2
    cases value : dead row <;> simp_all
  simp [noChildren, childFree, canonicalFree]

/-- The actual equal-symbol row walk and final node complete with a closed value. -/
theorem node_leaf_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard →
      Result Symbol Guard (Value Symbol Guard))
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (facts : Facts state.heap)
    (leaves : (∀ row ∈ left, row.children = []) ∨ (∀ row ∈ right, row.children = [])) :
    ∃ value final, node emptyGuard conjoin call left right state = .done value final ∧
      Facts final.heap ∧ Available final.heap value ∧ value.free = [] := by
  have pairsLeaf : ∀ job ∈ pairs left right, job.1.children = [] ∨ job.2.children = [] := by
    intro job member
    obtain ⟨first, included, second, selected, _, same⟩ :=
      (SymbolicHashJoin.hashJoin_member (fun row : EdgeValue Symbol Guard => row.entry.key.symbol)
        Prod.mk left right job).mp member
    rw [← same]
    exact leaves.elim (fun leaf => Or.inl (leaf first included))
      (fun leaf => Or.inr (leaf second selected))
  obtain ⟨rows, after, walked, afterFacts, _, residents, rowsLeaf⟩ :=
    walk_leaf_complete emptyGuard conjoin call (pairs left right) state facts pairsLeaf
  let made := run (makeNode rows) after.heap
  have checked := node_verified rows after.heap afterFacts residents
  refine ⟨made.1, {after with heap := made.2}, ?_, checked.facts, checked.result _ _ rfl, ?_⟩
  · simp only [node, walked, Result.bind, work]
    rfl
  · exact makeNode_leaf_free rows after.heap afterFacts residents rowsLeaf

/-- The actual optional-Mu continuation completes without adding a binder. -/
theorem node_leaf_optional [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard →
      Result Symbol Guard (Value Symbol Guard))
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (facts : Facts state.heap)
    (leaves : (∀ row ∈ left, row.children = []) ∨ (∀ row ∈ right, row.children = []))
    (key : Nat × Nat) :
    ∃ value final,
      (node emptyGuard conjoin call left right state).bind
        (fun value after => construction
          (SourceRecursiveIntersectionMaybeMu.maybeMu key value after.heap) after) = .done value final ∧
      Facts final.heap ∧ Available final.heap value ∧ value.free = [] := by
  obtain ⟨value, final, done, finalFacts, available, closed⟩ :=
    node_leaf_complete emptyGuard conjoin call left right state facts leaves
  refine ⟨value, final, ?_, finalFacts, available, closed⟩
  rw [done]
  simp only [Result.bind, SourceRecursiveIntersectionMaybeMu.unused key value final.heap
    (by simp [closed]), construction]

end MicroCFTA.SourceRecursiveIntersectionLeafNode
