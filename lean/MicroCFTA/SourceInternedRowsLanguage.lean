import MicroCFTA.SourceInternedRowsFinite

/-!
# Guarded language of the actual row readback

The adapter never evaluates or drops a constraint. Any interpretation of
the stored constraints therefore gives the same root language before and
after a completed traversal. Empty child references do not make new terms.
Their omission from a nonempty table is handled separately by validation.
-/
namespace MicroCFTA.SourceInternedRows
open Language FTAValidation

/-- Interpret the retained constraint only when a complete term is checked. -/
def interpret (holds : Constraint → Term Symbol → Bool) (edge : Transition Symbol Constraint) :
    Edge State Symbol := ⟨edge.label, edge.children, holds edge.constraint⟩

/-- Apply the same interpretation to every source table edge. -/
def interpretedRows (holds : Constraint → Term Symbol → Bool)
    (table : List (State × List (Transition Symbol Constraint))) : Rows State Symbol :=
  table.map fun (state, edges) => (state, edges.map (interpret holds))

/-- The original exposed heap has no transitions at EmptyState. -/
def graph (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool) : Automaton State Symbol
  | .empty => []
  | .interned identity => (heap identity).map (fun edge => interpret holds (transition edge))

/-- Interpretation commutes with exact ordered table lookup. -/
theorem interpreted_lookup (holds : Constraint → Term Symbol → Bool)
    (table : List (State × List (Transition Symbol Constraint))) (state : State) :
    rowFor (interpretedRows holds table) state = (lookup table state).map (interpret holds) := by
  simp only [rowFor, interpretedRows, lookup, List.flatMap_map, List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro row member
  split <;> simp_all

/-- A completed nonempty table keeps a complete source row exactly at each visited identity. -/
theorem interpreted_table (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool)
    (visited : List Nat) (identity : Nat) :
    rowFor (interpretedRows holds (table heap visited)) (.interned identity) =
      if identity ∈ visited then graph heap holds (.interned identity) else [] := by
  rw [interpreted_lookup, table_lookup]
  split <;> simp_all [graph, List.map_map]

/-- EmptyState never obtains a constructor row from a nonempty source identity. -/
theorem interpreted_empty (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool)
    (visited : List Nat) : rowFor (interpretedRows holds (table heap visited)) .empty = [] := by
  simp [interpreted_lookup, table_empty]

/-- The extracted table never invents a symbol, child, guard, or alternative. -/
theorem table_subset (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool)
    (visited : List Nat) (state : State) (edge : Edge State Symbol)
    (member : edge ∈ rowFor (interpretedRows holds (table heap visited)) state) : edge ∈ graph heap holds state := by
  cases state with
  | empty => simp [interpreted_empty] at member
  | interned identity =>
    rw [interpreted_table] at member
    split at member
    · exact member
    · simp at member

/-- The child run at an empty state cannot exist. -/
theorem empty_rejects (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool) (term : Term Symbol) :
    ¬Accepts (graph heap holds) .empty term := by
  intro accepted
  cases accepted with
  | node edge children member runs guard => simp [graph] at member

/-- The graph relation transports a successful run to all reached row identities. -/
theorem table_complete (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool)
    (fuel : Nat) (roots : List Ref) (visited : List Nat) (done : collect heap fuel [] roots = some visited)
    {state : State} {term : Term Symbol} (accepted : Accepts (graph heap holds) state term) :
    (∀ identity, state = .interned identity → Reaches heap roots identity) →
      Accepts (rowFor (interpretedRows holds (table heap visited))) state term := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ =>
      (∀ state ∈ states, ∀ identity, state = .interned identity → Reaches heap roots identity) →
        All₂ (Accepts (rowFor (interpretedRows holds (table heap visited)))) states terms) with
  | @node state edge terms member runs guard ih =>
    intro reached
    cases state with
    | empty => simp [graph] at member
    | interned identity =>
      have current := reached identity rfl
      have visitedIn := (collect_exact heap fuel roots visited done identity).mpr current
      refine .node edge terms (by simpa [interpreted_table, visitedIn] using member) (ih ?_) guard
      intro child childIn next same
      subst child
      obtain ⟨raw, rawIn, sameEdge⟩ := List.mem_map.mp member
      subst edge
      obtain ⟨ref, refIn, sameRef⟩ := List.mem_map.mp childIn
      cases ref with
      | none => cases sameRef
      | some rawId =>
        have equal : rawId = next := State.interned.inj sameRef
        subst rawId
        exact .child current ((mem_successors heap identity next).mpr (List.mem_flatMap.mpr ⟨raw, rawIn, refIn⟩))
  | nil => exact .nil
  | cons head tail ihHead ihTail =>
    rename_i reached
    exact .cons (ihHead (reached _ (by simp))) (ihTail (fun state member => reached state (by simp [member])))

/-- Complete source `toRows` readback preserves every guarded finite root term. -/
theorem toRows_language (heap : Heap Symbol Constraint) (holds : Constraint → Term Symbol → Bool)
    (fuel : Nat) (root : Ref) (result : List (State × List (Transition Symbol Constraint)))
    (done : toRows heap fuel root = some result) (term : Term Symbol) :
    Accepts (rowFor (interpretedRows holds result)) (stateOf root) term ↔ Accepts (graph heap holds) (stateOf root) term := by
  cases root with
  | none =>
    have same : result = [(.empty, [])] := (Option.some.inj done).symm
    subst result
    constructor
    · intro accepted
      cases accepted with
      | node edge children member runs guard => simp [interpretedRows, rowFor, stateOf] at member
    · exact False.elim ∘ empty_rejects heap holds term
  | some identity =>
    obtain ⟨visited, walked, same⟩ := Option.map_eq_some_iff.mp done
    subst result
    constructor
    · exact accepts_transfer _ _ (table_subset heap holds visited)
    · intro accepted
      exact table_complete heap holds fuel [some identity] visited walked accepted
        (by intro next same; have equal : identity = next := State.interned.inj same; subst next; exact .root (by simp))

/-- The source root remains declared even when it has no accepted term. -/
theorem toRows_initial (heap : Heap Symbol Constraint) (fuel : Nat) (root : Ref)
    (result : List (State × List (Transition Symbol Constraint))) (done : toRows heap fuel root = some result) :
    stateOf root ∈ result.map Prod.fst := by
  cases root with
  | none => cases Option.some.inj done; simp [stateOf]
  | some identity =>
    obtain ⟨visited, walked, same⟩ := Option.map_eq_some_iff.mp done
    subst result
    have present := (collect_exact heap fuel [some identity] visited walked identity).mpr (.root (by simp))
    simp [table, List.map_map, Function.comp_def, stateOf, CanonicalClasses.mem_sortedSet, present]

end MicroCFTA.SourceInternedRows
