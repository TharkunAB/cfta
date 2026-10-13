import MicroCFTA.LevelEnumeration
import MicroCFTA.SourceSizedReference

/-!
# The ordinary three-table level recurrence

This is the table recurrence in Internal.Tree.termLevelsBy after row
exposure and trimming. The set traversal fixes the order within a level.
The source does not specify that order. The recurrence remains finite for
each requested depth even when the graph has cycles.
-/

namespace MicroCFTA.SourceDenotationLevels

open Language LevelEnumeration

/-- Each source iteration retains its exact level, accumulated levels, and preceding accumulated levels. -/
structure Tables (State Symbol : Type) where
  current : State → List (Term Symbol)
  atMost : State → List (Term Symbol)
  shallower : State → List (Term Symbol)

/-- The source bypasses set construction when outgoing symbols are globally distinct. -/
def clean (setList : List (Term Symbol) → List (Term Symbol)) (unambiguous : Bool)
    (terms : List (Term Symbol)) : List (Term Symbol) :=
  if unambiguous then terms else setList terms

/-- Set readback changes neither membership nor the shortcut's input order. -/
theorem mem_clean (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms)
    (unambiguous : Bool) (terms : List (Term Symbol)) (term : Term Symbol) :
    term ∈ clean setList unambiguous terms ↔ term ∈ terms := by
  cases unambiguous <;> simp [clean, setExact]

/-- The initial source table contains exactly leaf rows. -/
def leaves (automaton : Automaton State Symbol) (state : State) : List (Term Symbol) :=
  (automaton state).flatMap fun edge => if edge.children.isEmpty then [.node edge.label []] else []

/-- Initialize the source triple before its first iteration. -/
def initial (automaton : Automaton State Symbol) (setList : List (Term Symbol) → List (Term Symbol))
    (unambiguous : Bool) : Tables State Symbol :=
  let first := fun state => clean setList unambiguous (leaves automaton state)
  ⟨first, first, fun _ => []⟩

/-- Build the next exact level with the source first-deepest-child product. -/
def deeper (automaton : Automaton State Symbol) (before : Tables State Symbol) (state : State) : List (Term Symbol) :=
  (automaton state).flatMap fun edge =>
    (childLists before.current before.atMost before.shallower edge.children).map (Term.node edge.label)

/-- New terms precede old terms in the accumulated source table. -/
def next (automaton : Automaton State Symbol) (setList : List (Term Symbol) → List (Term Symbol))
    (unambiguous : Bool) (before : Tables State Symbol) : Tables State Symbol :=
  let level := fun state => clean setList unambiguous (deeper automaton before state)
  ⟨level, fun state => level state ++ before.atMost state, before.atMost⟩

/-- A finite number of source iterations; its index is leaf-zero depth. -/
def tables (automaton : Automaton State Symbol) (setList : List (Term Symbol) → List (Term Symbol))
    (unambiguous : Bool) : Nat → Tables State Symbol
  | 0 => initial automaton setList unambiguous
  | depth + 1 => next automaton setList unambiguous (tables automaton setList unambiguous depth)

/-- The meanings of the three concrete source tables at a positive language height. -/
def Exact (automaton : Automaton State Symbol) (height : Nat) (table : Tables State Symbol) : Prop :=
  (∀ state term, term ∈ table.current state ↔ Accepts automaton state term ∧ term.height = height) ∧
  (∀ state term, term ∈ table.atMost state ↔ Accepts automaton state term ∧ term.height ≤ height) ∧
  (∀ state term, term ∈ table.shallower state ↔ Accepts automaton state term ∧ term.height < height)

/-- Height one is exactly an accepted leaf in a graph with no guards. -/
theorem leaves_exact (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (state : State) (term : Term Symbol) :
    term ∈ leaves automaton state ↔ Accepts automaton state term ∧ term.height = 1 := by
  constructor
  · intro present
    obtain ⟨edge, member, built⟩ := List.mem_flatMap.mp present
    by_cases empty : edge.children = []
    · have same : term = .node edge.label [] := by simpa [empty] using built
      subst term
      refine ⟨.node edge [] member ?_ (plain state edge member _), by simp [Term.height]⟩
      rw [empty]
      exact .nil
    · simp [empty] at built
  · rintro ⟨accepted, height⟩
    cases accepted with
    | node edge children member accepted guarded =>
        have empty : children = [] := by
          cases children with
          | nil => rfl
          | cons child rest =>
              have positive := child.height_pos
              simp only [Term.height, List.foldr_cons] at height
              omega
        subst children
        have keys : edge.children = [] := List.length_eq_zero_iff.mp (by simpa using accepted.length_eq)
        exact List.mem_flatMap.mpr ⟨edge, member, by simp [keys]⟩

/-- The initial triple has the required leaf-level meanings. -/
theorem initial_exact (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms) (unambiguous : Bool) :
    Exact automaton 1 (initial automaton setList unambiguous) := by
  refine ⟨?_, ?_, ?_⟩
  · intro state term
    exact (mem_clean setList setExact unambiguous _ term).trans (leaves_exact automaton plain state term)
  · intro state term
    have positive := term.height_pos
    change term ∈ clean setList unambiguous (leaves automaton state) ↔ _
    rw [mem_clean setList setExact, leaves_exact automaton plain]
    exact and_congr Iff.rfl (by omega)
  · intro state term
    have positive := term.height_pos
    change term ∈ ([] : List (Term Symbol)) ↔ _
    simp only [List.not_mem_nil, false_iff]
    omega

/-- The source product constructs precisely the next non-leaf height. -/
theorem deeper_exact (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (height : Nat) (positive : 0 < height) (before : Tables State Symbol) (exact : Exact automaton height before)
    (state : State) (term : Term Symbol) :
    term ∈ deeper automaton before state ↔ Accepts automaton state term ∧ term.height = height + 1 := by
  have productsExact := childLists_exact before.current before.atMost before.shallower (Accepts automaton)
    Term.height height exact.1 exact.2.1 exact.2.2
  constructor
  · intro member
    obtain ⟨edge, present, children, built, same⟩ := (by simpa [deeper] using member :
      ∃ edge ∈ automaton state, ∃ children ∈ childLists before.current before.atMost before.shallower edge.children,
        Term.node edge.label children = term)
    subst term
    obtain ⟨accepted, reaches⟩ := (productsExact edge.children children).mp built
    obtain ⟨accepted, bounded⟩ := (all₂_height_iff (Accepts automaton) edge.children children height).mp accepted
    have exactHeight := (forestHeight_exact children height positive).mpr
      ⟨fun child present => Nat.le_trans (height_le_forestHeight children child present) bounded, reaches⟩
    exact ⟨.node edge children present accepted (plain state edge present _),
      by simpa [Term.height, forestHeight] using exactHeight⟩
  · rintro ⟨accepted, depth⟩
    cases accepted with
    | node edge children present accepted guarded =>
        have exactHeight : forestHeight children = height := by
          have depth : forestHeight children + 1 = height + 1 := by simpa only [Term.height, forestHeight] using depth
          omega
        have reaches := ((forestHeight_exact children height positive).mp exactHeight).2
        have childrenValid := (all₂_height_iff (Accepts automaton) edge.children children height).mpr
          ⟨accepted, by omega⟩
        exact List.mem_flatMap.mpr ⟨edge, present, List.mem_map.mpr
          ⟨children, (productsExact edge.children children).mpr ⟨childrenValid, reaches⟩, rfl⟩⟩

/-- Every source iteration preserves the exact meanings of all three tables. -/
theorem next_exact (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms) (unambiguous : Bool)
    (height : Nat) (positive : 0 < height) (before : Tables State Symbol) (exact : Exact automaton height before) :
    Exact automaton (height + 1) (next automaton setList unambiguous before) := by
  refine ⟨?_, ?_, ?_⟩
  · intro state term
    exact (mem_clean setList setExact unambiguous _ term).trans (deeper_exact automaton plain height positive before exact state term)
  · intro state term
    change term ∈ clean setList unambiguous (deeper automaton before state) ++ before.atMost state ↔ _
    rw [List.mem_append, mem_clean setList setExact, deeper_exact automaton plain height positive before exact, exact.2.1, ← and_or_left]
    exact and_congr Iff.rfl (by omega)
  · intro state term
    change term ∈ before.atMost state ↔ _
    rw [exact.2.1]
    exact and_congr Iff.rfl (by omega)

/-- The actual finite recurrence is exact at every leaf-zero depth. -/
theorem tables_exact (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms) (unambiguous : Bool) (depth : Nat) :
    Exact automaton (depth + 1) (tables automaton setList unambiguous depth) := by
  induction depth with
  | zero => exact initial_exact automaton plain setList setExact unambiguous
  | succ depth ih => exact next_exact automaton plain setList setExact unambiguous (depth + 1) (by omega) _ ih

/-- Read the same finite level prefix as genericTake(depth+1), in increasing source depth. -/
def through (automaton : Automaton State Symbol) (setList : List (Term Symbol) → List (Term Symbol))
    (unambiguous : Bool) (depth : Nat) (root : State) : List (Term Symbol) :=
  (List.range (depth + 1)).flatMap fun index => (tables automaton setList unambiguous index).current root

/-- The ordinary finite prefix is exactly the accepted language up to its source depth. -/
theorem prefix_exact (automaton : Automaton State Symbol)
    (plain : ∀ state edge, edge ∈ automaton state → ∀ term, edge.guard term = true)
    (setList : List (Term Symbol) → List (Term Symbol))
    (setExact : ∀ terms term, term ∈ setList terms ↔ term ∈ terms) (unambiguous : Bool)
    (depth : Nat) (root : State) (term : Term Symbol) :
    term ∈ through automaton setList unambiguous depth root ↔ Accepts automaton root term ∧ term.height ≤ depth + 1 := by
  simp only [through, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨index, small, member⟩
    obtain ⟨accepted, height⟩ := (tables_exact automaton plain setList setExact unambiguous index).1 root term |>.mp member
    exact ⟨accepted, by omega⟩
  · rintro ⟨accepted, bounded⟩
    have positive := term.height_pos
    refine ⟨term.height - 1, by omega, ?_⟩
    exact ((tables_exact automaton plain setList setExact unambiguous (term.height - 1)).1 root term).mpr ⟨accepted, by omega⟩

/-- The specialized three-child branch retains the general source worker's exact loop order. -/
theorem ternary_dispatch (current atMost shallower : State → List α) (first second third : State) :
    childLists current atMost shallower [first, second, third] =
      (current first).flatMap (fun a => (atMost second).flatMap (fun b => (atMost third).map (fun c => [a, b, c]))) ++
      (current second).flatMap (fun b => (atMost third).flatMap (fun c => (shallower first).map (fun a => [a, b, c]))) ++
      (current third).flatMap (fun c => (shallower second).flatMap (fun b => (shallower first).map (fun a => [a, b, c]))) := by
  simp [childLists, products, ← List.map_eq_flatMap, List.flatMap_map, List.map_flatMap,
    Function.comp_def, List.flatMap_assoc, List.append_assoc]

end MicroCFTA.SourceDenotationLevels
