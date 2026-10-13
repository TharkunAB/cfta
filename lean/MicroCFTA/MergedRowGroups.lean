import Std

/-!
# Distinct rows in a merged symbol group

Grouping uses complete row equality. The supplied symbol order represents
HashMap iteration order. The output membership theorem does not fix that order.
-/
namespace MicroCFTA.MergedRowGroups

/-- Preserve groups of at most four rows. Collapse larger groups to the unconstrained row. -/
def squash (top : Row) (rows : List Row) : List Row :=
  if rows.length ≤ 4 then rows else [top]

/-- The source tests whether the group has more than four edges. -/
theorem squash_member (top : Row) (rows : List Row) (row : Row) :
    row ∈ squash top rows ↔
      (row ∈ rows ∧ rows.length ≤ 4) ∨ (row = top ∧ 4 < rows.length) := by
  by_cases small : rows.length ≤ 4
  · simp [squash, small, Nat.not_lt_of_ge small]
  · have large : 4 < rows.length := by omega
    simp [squash, small, large]

/-- Every output group has at most four edges. -/
theorem squash_bound (top : Row) (rows : List Row) : (squash top rows).length ≤ 4 := by
  unfold squash
  split <;> simp_all

/-- Small groups preserve the exact original row order and spelling. -/
theorem squash_small (top : Row) (rows : List Row) (small : rows.length ≤ 4) :
    squash top rows = rows := by simp [squash, small]

/-- Large groups contain exactly one unconstrained row. -/
theorem squash_large (top : Row) (rows : List Row) (large : 4 < rows.length) :
    squash top rows = [top] := by simp [squash, show ¬ rows.length ≤ 4 by omega]

/-- Changing only the row representation commutes with the threshold branch. -/
theorem squash_map (top : Row) (rows : List Row) (encode : Row → Code) :
    squash (encode top) (rows.map encode) = (squash top rows).map encode := by
  unfold squash
  simp only [List.length_map]
  split <;> rfl

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

/-- Complete-row duplicate removal returns a distinct list. -/
theorem eraseDups_nodup [BEq Row] [LawfulBEq Row] (rows : List Row) : rows.eraseDups.Nodup := by
  cases rows with
  | nil => simp
  | cons first rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp [List.mem_eraseDups]
      · exact eraseDups_nodup _
termination_by rows.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le ..)

/-- Grouping reads a duplicate-free list of complete rows. -/
theorem rowsAt_nodup [DecidableEq Symbol] [BEq Row] [LawfulBEq Row]
    (input : List (Symbol × Row)) (symbol : Symbol) : (rowsAt input symbol).Nodup :=
  eraseDups_nodup _

/-- The physical group output uses the exact four-edge threshold. -/
theorem grouped_member [DecidableEq Symbol] [BEq Row] [LawfulBEq Row]
    (top : Row) (order : List Symbol) (input : List (Symbol × Row))
    (complete : ∀ symbol row, (symbol, row) ∈ input → symbol ∈ order)
    (symbol : Symbol) (row : Row) :
    (symbol, row) ∈ grouped top order input ↔
      ((symbol, row) ∈ input ∧ (rowsAt input symbol).length ≤ 4) ∨
      (row = top ∧ 4 < (rowsAt input symbol).length) := by
  have selection := squash_member top (rowsAt input symbol) row
  simp only [rowsAt_member] at selection
  constructor
  · intro member
    obtain ⟨actual, _, groupMember⟩ := List.mem_flatMap.mp member
    obtain ⟨other, rowMember, same⟩ := List.mem_map.mp groupMember
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact selection.mp rowMember
  · intro member
    have ordered : symbol ∈ order := by
      rcases member with ⟨present, _⟩ | ⟨_, large⟩
      · exact complete symbol row present
      · cases selected : rowsAt input symbol with
        | nil => simp [selected] at large
        | cons first rest =>
            exact complete symbol first ((rowsAt_member input symbol first).mp (by simp [selected]))
    exact List.mem_flatMap.mpr ⟨symbol, ordered,
      List.mem_map.mpr ⟨row, selection.mpr member, rfl⟩⟩

end MicroCFTA.MergedRowGroups
