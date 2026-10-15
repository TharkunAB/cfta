import MicroCFTA.SourceOrderedBinderImport

/-!
# Finite execution of the ordered binder import schedule

Bounded source child positions and a decreasing condensation height derive
every recursive build. Same-component calls use the proved context rank.
No completed body or total recursive callback is supplied. Actual source
DFS and SCC extraction must still derive these finite graph facts.
-/
namespace MicroCFTA.SourceOrderedBinderComplete
open SourceOrderedBinderImport

/-- The source positions used by all ordered children of one state. -/
def successors (source : Nat → List (Row Symbol Constraint Nat)) (here : Nat) : List Nat :=
  (source here).flatMap Row.children

/-- Component height dominates every possible same-component context rank. -/
def measure (width : Nat) (component height : Nat → Nat) (key : Key) : Nat :=
  height (component key.2) * (2 ^ width + 1) + SourceOrderedBinderRank.rank width key.1 key.2

/-- Every selected recursive source child decreases the combined component/context measure. -/
theorem child_decreases (width : Nat) (source : Nat → List (Row Symbol Constraint Nat))
    (component height : Nat → Nat)
    (closed : ∀ here < width, ∀ next ∈ successors source here, next < width)
    (descending : ∀ here < width, ∀ next ∈ successors source here,
      component next ≠ component here → height (component next) < height (component here))
    (bound : Bound) (here next : Nat) (bounded : here < width)
    (member : next ∈ successors source here)
    (childBound : Bound) (chosen : select component bound here next = .build childBound next) :
    measure width component height (childBound, next) < measure width component height (bound, here) := by
  have nextBound := closed here bounded next member
  unfold select at chosen
  split at chosen
  · rename_i different
    cases chosen
    have down := descending here bounded next member different
    have childRank : SourceOrderedBinderRank.rank width [] next ≤ 2 ^ width := Nat.sub_le _ _
    have step : height (component next) + 1 ≤ height (component here) := by omega
    have scaled := Nat.mul_le_mul_right (2 ^ width + 1) step
    simp only [measure, Nat.add_mul, Nat.one_mul] at *
    omega
  · rename_i same
    have same : component next = component here := Classical.not_not.mp same
    split at chosen
    · cases chosen
    · rename_i absent
      cases chosen
      have smaller := select_rank_decreases width nextBound absent
      simp only [measure, same]
      omega

private theorem children_complete
    (source : Nat → List (Row Symbol Constraint Nat)) (component : Nat → Nat)
    (operations : Operations Symbol Constraint Node) (bound : Bound) (here : Nat)
    (inputs : List Nat)
    (calls : ∀ next ∈ inputs, ∀ childBound, select component bound here next = .build childBound next →
      ∀ before, ∃ value after, Build source component operations (childBound, next) before value after)
    (before : Cache.Table Key Node) :
    ∃ values after, Children source component operations bound here inputs before values after := by
  induction inputs generalizing before with
  | nil => exact ⟨[], before, .nil⟩
  | cons next rest ih =>
      have tailCalls : ∀ next ∈ rest, ∀ childBound, select component bound here next = .build childBound next →
          ∀ before, ∃ value after, Build source component operations (childBound, next) before value after :=
        fun next member => calls next (List.mem_cons_of_mem _ member)
      cases chosen : select component bound here next with
      | reference index =>
          have same : index = next := by
            unfold select at chosen
            split at chosen
            · cases chosen
            · split at chosen
              · exact (Choice.reference.inj chosen).symm
              · cases chosen
          subst index
          obtain ⟨values, after, tail⟩ := ih tailCalls before
          exact ⟨operations.reference next :: values, after, .reference chosen tail⟩
      | build childBound childHere =>
          have same : childHere = next := by
            unfold select at chosen
            split at chosen
            · exact (Choice.build.inj chosen).2.symm
            · split at chosen
              · cases chosen
              · exact (Choice.build.inj chosen).2.symm
          subst childHere
          obtain ⟨value, middle, head⟩ := calls next List.mem_cons_self childBound chosen before
          obtain ⟨values, after, tail⟩ := ih tailCalls middle
          exact ⟨value :: values, after, .build chosen head tail⟩

private theorem rows_complete
    (source : Nat → List (Row Symbol Constraint Nat)) (component : Nat → Nat)
    (operations : Operations Symbol Constraint Node) (bound : Bound) (here : Nat)
    (inputs : List (Row Symbol Constraint Nat))
    (calls : ∀ next ∈ inputs.flatMap Row.children, ∀ childBound,
      select component bound here next = .build childBound next →
      ∀ before, ∃ value after, Build source component operations (childBound, next) before value after)
    (before : Cache.Table Key Node) :
    ∃ copied after, Rows source component operations bound here inputs before copied after := by
  induction inputs generalizing before with
  | nil => exact ⟨[], before, .nil⟩
  | cons first rest ih =>
      obtain ⟨children, middle, head⟩ := children_complete source component operations bound here first.children
        (fun next member => calls next (List.mem_flatMap.mpr ⟨first, List.mem_cons_self, member⟩)) before
      obtain ⟨copied, after, tail⟩ := ih
        (fun next member => calls next (by simpa only [List.flatMap_cons, List.mem_append] using Or.inr member)) middle
      exact ⟨⟨first.symbol, first.constraint, children⟩ :: copied, after, .cons head tail⟩

/-- Finite source positions and condensation order derive a completed actual build from every ordered key. -/
theorem build_complete
    (width : Nat) (source : Nat → List (Row Symbol Constraint Nat))
    (component height : Nat → Nat) (operations : Operations Symbol Constraint Node)
    (closed : ∀ here < width, ∀ next ∈ successors source here, next < width)
    (descending : ∀ here < width, ∀ next ∈ successors source here,
      component next ≠ component here → height (component next) < height (component here))
    (bound : Bound) (here : Nat) (ordered : Ordered bound here) (bounded : here < width)
    (before : Cache.Table Key Node) :
    ∃ value after, Build source component operations (bound, here) before value after := by
  cases found : before (bound, here) with
  | some value => exact ⟨value, before, .hit found⟩
  | none =>
      have calls : ∀ next ∈ successors source here, ∀ childBound,
          select component bound here next = .build childBound next →
          ∀ before, ∃ value after, Build source component operations (childBound, next) before value after := by
        intro next member childBound chosen current
        have nextOrdered := (select_build_ordered ordered chosen).2
        exact build_complete width source component height operations closed descending childBound next nextOrdered
          (closed here bounded next member) current
      obtain ⟨copied, middle, body⟩ := rows_complete source component operations bound here (source here) calls before
      exact ⟨_, _, .miss found body⟩
termination_by measure width component height (bound, here)
decreasing_by
  exact child_decreases width source component height closed descending bound here next bounded member childBound chosen

/-- The current source root starts with no enclosing binders and position zero. -/
theorem root_complete
    (width : Nat) (positive : 0 < width) (source : Nat → List (Row Symbol Constraint Nat))
    (component height : Nat → Nat) (operations : Operations Symbol Constraint Node)
    (closed : ∀ here < width, ∀ next ∈ successors source here, next < width)
    (descending : ∀ here < width, ∀ next ∈ successors source here,
      component next ≠ component here → height (component next) < height (component here)) :
    ∃ value after, Build source component operations ([], 0) (fun _ => none) value after :=
  build_complete width source component height operations closed descending [] 0 (by simp [Ordered]) positive _

end MicroCFTA.SourceOrderedBinderComplete
