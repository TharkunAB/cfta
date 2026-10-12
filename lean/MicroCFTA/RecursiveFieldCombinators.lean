import MicroCFTA.RecursiveNaryChoice

/-!
# Reusable field contracts for recursive source operations

The finite field type stores one finite interval at each size. Its set of
sizes can be unbounded. Closed callback expressions combine these fields
without adding a recursive occurrence. Their local laws can be used by a
separate interpreter for n-ary recursive bodies.
-/
namespace MicroCFTA.RecursiveFieldCombinators
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveCallbackDistinct

/-- The unused root of a local callback expression has no members. -/
def emptyField : Finite Symbol := ⟨fun _ => 0, fun _ => none, fun _ _ => []⟩

/-- Each local expression has an empty distinguished root. -/
def emptyBody : Recipe Symbol := .finite emptyField

/-- The local selector uses the independently tabulated member class. -/
def field [DecidableEq Symbol] (recipe : Recipe Symbol) : Finite Symbol :=
  ⟨counts (fun _ => 0) recipe,
    fun position => (classTerms (fun _ => []) recipe position.size)[position.rank]?,
    positions (fun _ => 0) emptyBody recipe⟩

/-- The empty local root satisfies its exact class equation. -/
theorem empty_equation (size : Nat) :
    ([] : List (EngineTerm Symbol)) =
      (classTerms (fun _ => []) emptyBody size).map (fun term => .node .recursion [term]) := by
  simp [emptyBody, emptyField, classTerms, finiteClass]

theorem empty_exact : LeavesExact (emptyBody (Symbol := Symbol)) := by
  intro view wanted position
  simp [emptyField]

theorem empty_indexed : LeavesIndexed (emptyBody (Symbol := Symbol)) := by
  intro position
  simp [emptyField]

theorem empty_bounded : LeavesBounded (emptyBody (Symbol := Symbol)) := by
  intro view wanted row member
  simp [emptyField] at member

theorem empty_ordered : LeavesOrdered (emptyBody (Symbol := Symbol)) := by
  intro view wanted
  exact List.Pairwise.nil

theorem empty_distinct : LeavesDistinct (emptyBody (Symbol := Symbol)) := by
  intro view wanted
  exact List.Pairwise.nil

/-- The local field selector covers exactly its counted class interval. -/
theorem field_indexed [DecidableEq Symbol] (recipe : Recipe Symbol) : FiniteIndex (field recipe) := by
  intro position
  have count := class_length (fun _ => []) (fun _ => 0) (fun _ => rfl) recipe position.size
  constructor
  · rintro ⟨term, selected⟩
    have bound := List.getElem?_eq_some_iff.mp selected
    change position.rank < counts (fun _ => 0) recipe position.size
    rw [← count]
    exact bound.1
  · intro within
    have bound : position.rank < (classTerms (fun _ => []) recipe position.size).length := by
      simpa only [count, field] using within
    refine ⟨(classTerms (fun _ => []) recipe position.size)[position.rank], ?_⟩
    exact List.getElem?_eq_getElem bound

/-- Complete checked callbacks agree with the independent local selector. -/
theorem field_exact [DecidableEq Symbol] (recipe : Recipe Symbol)
    (exactLeaves : LeavesExact recipe) (indexedLeaves : LeavesIndexed recipe) : FiniteExact (field recipe) := by
  intro view wanted position
  constructor
  · intro member
    obtain ⟨term, selected, projected⟩ := checked_sound (fun _ => 0) emptyBody empty_exact recipe exactLeaves view wanted position member
    refine ⟨term, ?_, projected⟩
    exact RecursiveCallbackAlignment.selects_lookup (fun _ => []) (fun _ => 0) (fun _ => rfl)
      emptyBody empty_equation empty_indexed recipe position term selected indexedLeaves
  · rintro ⟨term, selected, projected⟩
    rw [← projected]
    exact RecursiveCallbackCompleteness.table_complete (fun _ => []) (fun _ => 0) (fun _ => rfl)
      emptyBody empty_equation empty_exact empty_indexed recipe exactLeaves indexedLeaves position term selected view

/-- False and true local candidates both stay within the source interval. -/
theorem field_bounded [DecidableEq Symbol] (recipe : Recipe Symbol) (leaves : LeavesBounded recipe) :
    ∀ view wanted row, row ∈ (field recipe).positions view wanted → row.1.rank < (field recipe).counts row.1.size :=
  positions_bound (fun _ => 0) emptyBody (fun _ => rfl) empty_bounded recipe leaves

/-- Local operation callbacks preserve the source candidate order. -/
theorem field_ordered [DecidableEq Symbol] (recipe : Recipe Symbol) (leaves : LeavesOrdered recipe) :
    ∀ view wanted, ((field recipe).positions view wanted).Pairwise (fun first second => before first second) :=
  positions_ordered (fun _ => 0) emptyBody empty_ordered recipe leaves

/-- Local operation callbacks preserve distinct valid candidate positions. -/
theorem field_distinct [DecidableEq Symbol] (recipe : Recipe Symbol)
    (bounded : LeavesBounded recipe) (distinct : LeavesDistinct recipe) :
    ∀ view wanted, Distinct ((field recipe).positions view wanted) :=
  positions_distinct (fun _ => 0) emptyBody (fun _ => rfl) empty_bounded empty_distinct recipe bounded distinct

/-- Pay shifts each complete term position by one size unit. -/
def pay [DecidableEq Symbol] (child : Finite Symbol) : Finite Symbol := field (.pay (.finite child))

/-- Application combines the two source fields in split and function-major order. -/
def ap [DecidableEq Symbol] (functions arguments : Finite Symbol) : Finite Symbol :=
  field (.ap (.finite functions) (.finite arguments))

/-- A user label uses the source labelled view and adds one size unit. -/
def label [DecidableEq Symbol] (symbol : Symbol) (child : Finite Symbol) : Finite Symbol :=
  field (.label symbol (.finite child))

end MicroCFTA.RecursiveFieldCombinators
