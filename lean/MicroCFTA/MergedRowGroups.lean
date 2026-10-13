import Std

/-!
# Distinct rows in a merged symbol group

Grouping uses complete row equality. The supplied symbol order represents
HashMap iteration order. The output membership theorem does not fix that order.
-/
namespace MicroCFTA.MergedRowGroups

/-- Keep the single distinct row, or replace multiple rows with the unconstrained row. -/
def squash (top : Row) : List Row → List Row
  | [] => []
  | [row] => [row]
  | _ :: _ :: _ => [top]

/-- The source group branches in duplicate-free list form. -/
theorem squash_member (top : Row) (rows : List Row) (distinct : rows.Nodup) (row : Row) :
    row ∈ squash top rows ↔
      (row ∈ rows ∧ ∀ other ∈ rows, other = row) ∨
      (row = top ∧ ∃ first ∈ rows, ∃ second ∈ rows, first ≠ second) := by
  cases rows with
  | nil => simp [squash]
  | cons first rest =>
      cases rest with
      | nil => simp [squash, eq_comm]
      | cons second rest =>
          have different : first ≠ second := fun same =>
            (List.nodup_cons.mp distinct).1 (by simp [same])
          constructor
          · intro member
            have same : row = top := by simpa [squash] using member
            exact Or.inr ⟨same, first, by simp, second, by simp, different⟩
          · rintro (⟨_, only⟩ | ⟨rfl, _⟩)
            · exact False.elim (different ((only first (by simp)).trans (only second (by simp)).symm))
            · simp [squash]

/-- Read the distinct complete rows at one source symbol. -/
def rowsAt [DecidableEq Symbol] [BEq Row] (input : List (Symbol × Row)) (symbol : Symbol) : List Row :=
  ((input.filter (fun pair => decide (pair.1 = symbol))).map Prod.snd).eraseDups

/-- Complete row membership survives grouping and duplicate removal exactly. -/
theorem rowsAt_member [DecidableEq Symbol] [BEq Row] [LawfulBEq Row]
    (input : List (Symbol × Row)) (symbol : Symbol) (row : Row) :
    row ∈ rowsAt input symbol ↔ (symbol, row) ∈ input := by
  simp only [rowsAt, List.mem_eraseDups, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨actual, other⟩, ⟨member, rfl⟩, rfl⟩
    exact member
  · intro member
    exact ⟨(symbol, row), ⟨member, rfl⟩, rfl⟩

/-- Execute the group selection in an arbitrary source symbol order. -/
def grouped [DecidableEq Symbol] [BEq Row] (top : Row)
    (order : List Symbol) (input : List (Symbol × Row)) : List (Symbol × Row) :=
  order.flatMap fun symbol => (squash top (rowsAt input symbol)).map (symbol, ·)

private theorem eraseDups_nodup [BEq Row] [LawfulBEq Row] (rows : List Row) : rows.eraseDups.Nodup := by
  cases rows with
  | nil => simp
  | cons first rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp [List.mem_eraseDups]
      · exact eraseDups_nodup _
termination_by rows.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

/-- The physical group output depends on distinct complete rows, not iteration order. -/
theorem grouped_member [DecidableEq Symbol] [BEq Row] [LawfulBEq Row]
    (top : Row) (order : List Symbol) (input : List (Symbol × Row))
    (complete : ∀ symbol row, (symbol, row) ∈ input → symbol ∈ order)
    (symbol : Symbol) (row : Row) :
    (symbol, row) ∈ grouped top order input ↔
      ((symbol, row) ∈ input ∧ ∀ other, (symbol, other) ∈ input → other = row) ∨
      (row = top ∧ ∃ first second, (symbol, first) ∈ input ∧ (symbol, second) ∈ input ∧ first ≠ second) := by
  have selection :=  squash_member top (rowsAt input symbol) (eraseDups_nodup _) row
  simp only [rowsAt_member] at selection
  constructor
  · intro member
    obtain ⟨actual, _, groupMember⟩ := List.mem_flatMap.mp member
    obtain ⟨other, rowMember, same⟩ := List.mem_map.mp groupMember
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    rcases selection.mp rowMember with unique | ⟨same, first, a, second, b, different⟩
    · exact Or.inl unique
    · exact Or.inr ⟨same, first, second, a, b, different⟩
  · intro member
    have ordered : symbol ∈ order := by
      rcases member with ⟨present, _⟩ | ⟨_, first, second, present, _⟩
      · exact complete symbol row present
      · exact complete symbol first present
    apply List.mem_flatMap.mpr
    refine ⟨symbol, ordered, List.mem_map.mpr ⟨row, ?_, rfl⟩⟩
    apply selection.mpr
    rcases member with unique | ⟨same, first, second, a, b, different⟩
    · exact Or.inl unique
    · exact Or.inr ⟨same, first, a, second, b, different⟩

end MicroCFTA.MergedRowGroups
