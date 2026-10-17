import MicroCFTA.SourceCurrentConjunctionTuples
import MicroCFTA.SourceCurrentConjunctionEquality

/-!
# Initial finite guard and tuple bounds

The guard alphabet and tuple length determine a finite equality-shape bound.
The enumeration retains all guard and edge occurrences in source order.
No constructor heap or future execution appears in the bounds.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleBounds
open InternedConstructorTemplates EqualityNormalize
variable {Formula Symbol : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- Enumerate all words of the requested length over the literal alphabet. -/
def words (alphabet : List Guard) : Nat → List (List Guard)
  | 0 => [[]]
  | count + 1 => alphabet.flatMap fun guard => (words alphabet count).map (guard :: ·)

/-- Enumeration membership records exactly the original length and alphabet. -/
theorem words_mem_iff (alphabet : List Guard) (count : Nat) (word : List Guard) :
    word ∈ words alphabet count ↔ word.length = count ∧ ∀ guard ∈ word, guard ∈ alphabet := by
  induction count generalizing word with
  | zero =>
      cases word <;> simp [words]
  | succ count ih =>
      constructor
      · intro member
        obtain ⟨guard, included, selected⟩ := List.mem_flatMap.mp member
        obtain ⟨tail, present, rfl⟩ := List.mem_map.mp selected
        obtain ⟨length, members⟩ := (ih tail).mp present
        exact ⟨by simp [length], by intro value member; exact (List.mem_cons.mp member).elim (fun same => same ▸ included) (members value)⟩
      · rintro ⟨length, members⟩
        cases word with
        | nil => simp at length
        | cons guard tail =>
            refine List.mem_flatMap.mpr ⟨guard, members guard List.mem_cons_self, ?_⟩
            exact List.mem_map.mpr ⟨tail, (ih tail).mpr ⟨by simpa using length,
              fun value member => members value (List.mem_cons_of_mem _ member)⟩, rfl⟩

/-- Combine literal source equality accessors in their original right-fold order. -/
noncomputable def combined (guards : List Guard) : Option Constraints :=
  guards.foldr (fun guard tail => SourceCompactGuards.combineEqualities (SourceCompactGuards.sourceEqualities guard) tail) (some [])

/-- A path contributes its occurrence and every path component. -/
def pathMass (path : Path) : Nat := 1 + path.length

/-- A class contributes its occurrence and every literal path occurrence. -/
def classMass (paths : Class) : Nat := 1 + (paths.map pathMass).sum

/-- Constraints contribute their occurrence and every literal class occurrence. -/
def constraintsMass (classes : Constraints) : Nat := 1 + (classes.map classMass).sum

private theorem member_sum (f : A → Nat) (values : List A) (value : A) (member : value ∈ values) :
    f value ≤ (values.map f).sum := by
  induction values with
  | nil => cases member
  | cons first rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp member with rfl | member
      · omega
      · have enough := ih member; omega

private theorem length_sum (f : A → Nat) (values : List A) (positive : ∀ value ∈ values, 1 ≤ f value) :
    values.length ≤ (values.map f).sum := by
  induction values with
  | nil => simp
  | cons first rest ih =>
      have head := positive first List.mem_cons_self
      have tail := ih (fun value member => positive value (List.mem_cons_of_mem _ member))
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-- The constraints metric bounds the number of literal classes. -/
theorem classes_length_le (classes : Constraints) : classes.length ≤ constraintsMass classes := by
  have enough := length_sum classMass classes (fun _ _ => by simp [classMass])
  unfold constraintsMass
  omega

/-- The constraints metric bounds each literal class length. -/
theorem class_length_le (classes : Constraints) (paths : Class) (member : paths ∈ classes) :
    paths.length ≤ constraintsMass classes := by
  have enough := length_sum pathMass paths (fun _ _ => by simp [pathMass])
  have included := member_sum classMass classes paths member
  unfold classMass at included
  unfold constraintsMass
  omega

/-- The constraints metric bounds every literal path depth. -/
theorem path_length_le (classes : Constraints) (paths : Class) (path : Path)
    (classMember : paths ∈ classes) (pathMember : path ∈ paths) : path.length ≤ constraintsMass classes := by
  have first := member_sum pathMass paths path pathMember
  have second := member_sum classMass classes paths classMember
  unfold pathMass at first
  unfold classMass at second
  unfold constraintsMass
  omega

/-- All successful combinations of the initial finite words determine one bound. -/
noncomputable def classShapeBound (alphabet : List Guard) (count : Nat) : Nat :=
  1 + ((words alphabet count).map fun word => ((combined word).map constraintsMass).getD 0).sum

/-- The initial bound covers the metric of every successful admitted guard word. -/
theorem combined_mass_le (alphabet : List Guard) (count : Nat) (guards : List Guard)
    (length : guards.length = count) (members : ∀ guard ∈ guards, guard ∈ alphabet)
    (classes : Constraints) (live : combined guards = some classes) :
    constraintsMass classes ≤ classShapeBound alphabet count := by
  have included := (words_mem_iff alphabet count guards).mpr ⟨length, members⟩
  have enough := member_sum (fun word => ((combined word).map constraintsMass).getD 0) _ guards included
  rw [live] at enough
  simp only [Option.map_some, Option.getD_some] at enough
  unfold classShapeBound
  omega

/-- Initial guard membership and length bound every class count and path depth. -/
theorem combined_bounds (alphabet : List Guard) (count : Nat) (guards : List Guard)
    (length : guards.length = count) (members : ∀ guard ∈ guards, guard ∈ alphabet)
    (classes : Constraints) (live : combined guards = some classes) :
    classes.length ≤ classShapeBound alphabet count ∧
      (∀ paths ∈ classes, paths.length ≤ classShapeBound alphabet count) ∧
      ∀ paths ∈ classes, ∀ path ∈ paths, path.length ≤ classShapeBound alphabet count := by
  have bound := combined_mass_le alphabet count guards length members classes live
  exact ⟨Nat.le_trans (classes_length_le classes) bound,
    fun paths member => Nat.le_trans (class_length_le classes paths member) bound,
    fun paths member path present => Nat.le_trans (path_length_le classes paths path member present) bound⟩

/-- The generic physical edge view reads exactly the same guard fold. -/
theorem combined_edgeView (tuple : List (EdgeValue Symbol Guard)) :
    combined (tuple.map (fun edge => edge.entry.key.constraint)) =
      SourceCurrentConjunctionEmptinessRows.combined (tuple.map SourceCurrentConjunctionEquality.edgeView) := by
  induction tuple with
  | nil => rfl
  | cons edge rest ih =>
      simp only [List.map_cons, combined, List.foldr_cons,
        SourceCurrentConjunctionEmptinessRows.combined, SourceCurrentConjunctionEquality.edgeView] at ih ⊢
      rw [ih]

/-- The current completed-read edge view has the same literal guard fold. -/
theorem combined_current_edgeView
    (tuple : List (EdgeValue (SourceObservations.Label FullSyntax.Formula) (SourceSymbolicIndex.Constraint FullSyntax.Formula))) :
    combined (tuple.map (fun edge => edge.entry.key.constraint)) =
      SourceCurrentConjunctionEmptinessRows.combined (tuple.map SourceCurrentConjunctionCompletionReads.edgeView) :=
  combined_edgeView tuple

section Tuples
variable {GuardValue : Type} [DecidableEq Symbol]

/-- Each literal extension has at most one output per prior tuple and input edge. -/
theorem extend_length_le (edges : List (EdgeValue Symbol GuardValue)) (previous : List (List (EdgeValue Symbol GuardValue))) :
    (SourceCurrentConjunctionTuples.extend edges previous).length ≤ previous.length * edges.length := by
  induction previous with
  | nil => simp [SourceCurrentConjunctionTuples.extend]
  | cons tuple rest ih =>
      cases tuple with
      | nil =>
          simpa only [SourceCurrentConjunctionTuples.extend, List.flatMap_cons, List.nil_append, List.length_cons,
            Nat.succ_mul] using Nat.le_trans ih (Nat.le_add_left _ _)
      | cons first tail =>
          have width := List.length_filter_le (fun edge => decide (SourceCurrentConjunctionTuples.shape edge = SourceCurrentConjunctionTuples.shape first)) edges
          simp only [SourceCurrentConjunctionTuples.extend, List.flatMap_cons, List.length_append, List.length_map,
            List.length_cons, Nat.succ_mul] at ih ⊢
          omega

private theorem fold_length_le (rows : List (List (EdgeValue Symbol GuardValue))) (previous : List (List (EdgeValue Symbol GuardValue)))
    (width : Nat) (bounded : ∀ edges ∈ rows, edges.length ≤ width) :
    (rows.foldr SourceCurrentConjunctionTuples.extend previous).length ≤ previous.length * width ^ rows.length := by
  induction rows with
  | nil => simp
  | cons edges rest ih =>
      have first := extend_length_le edges (rest.foldr SourceCurrentConjunctionTuples.extend previous)
      have second := ih (fun row member => bounded row (List.mem_cons_of_mem _ member))
      have head := bounded edges List.mem_cons_self
      calc
        (SourceCurrentConjunctionTuples.extend edges (rest.foldr SourceCurrentConjunctionTuples.extend previous)).length
            ≤ (rest.foldr SourceCurrentConjunctionTuples.extend previous).length * edges.length := first
        _ ≤ (previous.length * width ^ rest.length) * width := Nat.mul_le_mul second head
        _ = previous.length * width ^ (edges :: rest).length := by simp [Nat.pow_succ, Nat.mul_assoc]

/-- Literal tuple occurrences are bounded by the original row width to the original row count. -/
theorem tuples_length_le (rows : List (List (EdgeValue Symbol GuardValue))) (width : Nat)
    (bounded : ∀ edges ∈ rows, edges.length ≤ width) :
    (SourceCurrentConjunctionTuples.tuples rows).length ≤ width ^ rows.length := by
  cases rows with
  | nil => simp [SourceCurrentConjunctionTuples.tuples]
  | cons first rest =>
      have bound := fold_length_le rest (first.map (fun edge => [edge])) width
        (fun edges member => bounded edges (List.mem_cons_of_mem _ member))
      simp only [List.length_map] at bound
      exact Nat.le_trans bound (by simpa [Nat.pow_succ, Nat.mul_comm] using
        Nat.mul_le_mul_right (width ^ rest.length) (bounded first List.mem_cons_self))

/-- Every tuple retains the original row count, including its source rotation. -/
theorem tuple_length (rows : List (List (EdgeValue Symbol GuardValue))) (tuple : List (EdgeValue Symbol GuardValue))
    (member : tuple ∈ SourceCurrentConjunctionTuples.tuples rows) : tuple.length = rows.length := by
  cases rows with
  | nil => cases member
  | cons first rest =>
      have same := (SourceCurrentConjunctionTuples.tuples_selection first rest tuple member).length_eq
      simpa only [List.length_append, List.length_singleton, List.length_cons] using same
end Tuples

/-- An actual selected tuple inherits its guard bounds from the original finite exposed carrier. -/
theorem tuple_combined_bounds [DecidableEq Symbol] (alphabet : List Guard)
    (rows : List (List (EdgeValue Symbol Guard)))
    (carrier : ∀ edges ∈ rows, ∀ edge ∈ edges, edge.entry.key.constraint ∈ alphabet)
    (tuple : List (EdgeValue Symbol Guard)) (member : tuple ∈ SourceCurrentConjunctionTuples.tuples rows)
    (classes : Constraints)
    (live : SourceCurrentConjunctionEmptinessRows.combined (tuple.map SourceCurrentConjunctionEquality.edgeView) = some classes) :
    classes.length ≤ classShapeBound alphabet rows.length ∧
      (∀ paths ∈ classes, paths.length ≤ classShapeBound alphabet rows.length) ∧
      ∀ paths ∈ classes, ∀ path ∈ paths, path.length ≤ classShapeBound alphabet rows.length := by
  apply combined_bounds alphabet rows.length (tuple.map (fun edge => edge.entry.key.constraint))
    (by simpa only [List.length_map] using tuple_length rows tuple member) ?_ classes
    ((combined_edgeView tuple).trans live)
  intro guard present
  obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
  obtain ⟨edges, selected, found⟩ := List.mem_flatten.mp (SourceCurrentConjunctionTuples.tuples_members rows tuple member edge included)
  exact carrier edges selected edge found

end MicroCFTA.SourceCurrentConjunctionTupleBounds
