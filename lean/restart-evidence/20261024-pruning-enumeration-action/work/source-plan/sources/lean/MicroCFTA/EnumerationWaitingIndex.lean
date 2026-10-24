import MicroCFTA.EnumerationSchedule

/-!
# Sparse counts of suspended UVar references

The source decrements the old slot's references before it increments the
new slot's references. Each occurrence counts, including duplicates. Zero
counts remove the map entry. This module proves the exact update equation.
-/
namespace MicroCFTA.EnumerationWaitingIndex
open EnumerationState EnumerationSchedule

/-- The integer-map interface keeps missing entries distinct from stored counts. -/
abbrev Waiting := Nat → Option Int

/-- A missing counter has value zero. -/
def read (waiting : Waiting) (uv : Nat) : Int := (waiting uv).getD 0

/-- The source removes a map entry exactly when its new count is zero. -/
def encode (count : Int) : Option Int := if count = 0 then none else some count

/-- Count every occurrence of one raw suspended UVar. -/
def occurrences (uv : Nat) : List Suspended → Int
  | [] => 0
  | sc :: rest => (if sc.var = uv then 1 else 0) + occurrences uv rest

/-- Reference multiplicities add when assimilation appends suspended constraints. -/
theorem occurrences_append (uv : Nat) (first second : List Suspended) :
    occurrences uv (first ++ second) = occurrences uv first + occurrences uv second := by
  induction first with
  | nil => simp [occurrences]
  | cons sc rest ih => simp [occurrences, ih, Int.add_assoc]

/-- The reference scan counts only unenumerated slots. -/
def total (uv : Nat) : List (UVarValue Symbol) → Int
  | [] => 0
  | value :: rest => occurrences uv (references value) + total uv rest

/-- Apply one source `IntMap.alter` update to one raw UVar. -/
def bump (change : Int) (uv : Nat) (waiting : Waiting) : Waiting :=
  fun other => if other = uv then encode (read waiting uv + change) else waiting other

/-- Apply the source's ordered counter fold to all suspended references. -/
def count (change : Int) (scs : List Suspended) (waiting : Waiting) : Waiting :=
  scs.foldl (fun previous sc => bump change sc.var previous) waiting

/-- Slot replacement removes the old references before it adds the new references. -/
def replace (old new : UVarValue Symbol) (waiting : Waiting) : Waiting :=
  count 1 (references new) (count (-1) (references old) waiting)

/-- Sparse maps store no zero-valued entry. -/
def Canonical (waiting : Waiting) : Prop := ∀ uv, waiting uv = encode (read waiting uv)

/-- The map contains exactly the full raw-slot occurrence count. -/
def Correct (values : List (UVarValue Symbol)) (waiting : Waiting) : Prop :=
  ∀ uv, waiting uv = encode (total uv values)

@[simp] theorem encode_read (value : Int) : (encode value).getD 0 = value := by
  by_cases zero : value = 0 <;> simp [encode, zero]

/-- A single map update adds its change only at the selected key. -/
theorem bump_read (change : Int) (target : Nat) (waiting : Waiting) (uv : Nat) :
    read (bump change target waiting) uv = read waiting uv + if uv = target then change else 0 := by
  by_cases same : uv = target <;> simp [bump, read, same]

/-- Every source counter update retains zero-entry deletion. -/
theorem bump_canonical (change : Int) (target : Nat) (waiting : Waiting) (canonical : Canonical waiting) :
    Canonical (bump change target waiting) := by
  intro uv
  by_cases same : uv = target
  · simp [bump, read, same]
  · simpa [bump, read, same] using canonical uv

/-- The ordered fold adds exactly the multiplicity of each suspended reference. -/
theorem count_read (change : Int) (scs : List Suspended) (waiting : Waiting) (uv : Nat) :
    read (count change scs waiting) uv = read waiting uv + change * occurrences uv scs := by
  induction scs generalizing waiting with
  | nil => simp [count, occurrences]
  | cons first rest ih =>
      simp only [count, List.foldl_cons] at *
      rw [ih, bump_read]
      by_cases same : first.var = uv
      · simp [occurrences, same, Int.mul_add, Int.add_assoc]
      · simp [occurrences, same, Ne.symm same]

/-- Repeated source updates retain zero-entry deletion. -/
theorem count_canonical (change : Int) (scs : List Suspended) (waiting : Waiting) (canonical : Canonical waiting) :
    Canonical (count change scs waiting) := by
  induction scs generalizing waiting with
  | nil => exact canonical
  | cons first rest ih => exact ih (bump change first.var waiting) (bump_canonical change first.var waiting canonical)

/-- Replacement subtracts the old multiplicity and adds the new multiplicity. -/
theorem replace_read (old new : UVarValue Symbol) (waiting : Waiting) (uv : Nat) :
    read (replace old new waiting) uv =
      read waiting uv - occurrences uv (references old) + occurrences uv (references new) := by
  simp [replace, count_read, Int.sub_eq_add_neg]

/-- Replacement preserves the sparse map representation. -/
theorem replace_canonical (old new : UVarValue Symbol) (waiting : Waiting) (canonical : Canonical waiting) :
    Canonical (replace old new waiting) :=
  count_canonical 1 _ _ (count_canonical (-1) _ waiting canonical)

/-- A correct counter table is sparse and has the exact integer scan value. -/
theorem Correct.facts (correct : Correct values waiting) :
    Canonical waiting ∧ ∀ uv, read waiting uv = total uv values := by
  have same : ∀ uv, read waiting uv = total uv values := by intro uv; simp [read, correct uv]
  exact ⟨fun uv => by rw [same uv]; exact correct uv, same⟩

/-- The full reference count follows a valid slot replacement exactly. -/
theorem total_set (uv index : Nat) (values : List (UVarValue Symbol)) (old new : UVarValue Symbol)
    (stored : values[index]? = some old) :
    total uv (values.set index new) = total uv values - occurrences uv (references old) + occurrences uv (references new) := by
  induction values generalizing index with
  | nil => simp at stored
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at stored
          subst first
          simp [total]
          omega
      | succ index =>
          simp only [List.getElem?_cons_succ] at stored
          simp only [List.set_cons_succ, total, ih index stored]
          omega

/-- A valid slot replacement derives the new cached counts from the previous scan invariant. -/
theorem replace_correct (values : List (UVarValue Symbol)) (index : Nat) (old new : UVarValue Symbol)
    (stored : values[index]? = some old) (waiting : Waiting) (correct : Correct values waiting) :
    Correct (values.set index new) (replace old new waiting) := by
  intro uv
  rw [replace_canonical old new waiting correct.facts.1 uv, replace_read, correct.facts.2 uv,
    total_set uv index values old new stored]

/-- The full scan count adds over adjacent slot lists. -/
theorem total_append (uv : Nat) (first second : List (UVarValue Symbol)) :
    total uv (first ++ second) = total uv first + total uv second := by
  induction first with
  | nil => simp [total]
  | cons value rest ih => simp [total, ih, Int.add_assoc]

/-- A newly allocated slot has no suspended references to add. -/
theorem allocate_correct (values : List (UVarValue Symbol)) (node : Option Nat) (waiting : Waiting)
    (correct : Correct values waiting) : Correct (values ++ [.unenumerated node []]) waiting := by
  intro uv
  simpa [total_append, total, references, occurrences] using correct uv

/-- Initialization has no waiting references. -/
theorem initial_correct (node : Nat) : Correct ([.unenumerated (some node) []] : List (UVarValue Symbol)) (fun _ => none) := by
  intro uv
  simp [total, references, occurrences, encode]

/-- Every occurrence count is nonnegative. -/
theorem occurrences_nonnegative (uv : Nat) (scs : List Suspended) : 0 ≤ occurrences uv scs := by
  induction scs with
  | nil => simp [occurrences]
  | cons sc rest ih => simp only [occurrences]; split <;> omega

/-- A positive occurrence count is exactly a named suspended reference. -/
theorem occurrences_positive (uv : Nat) (scs : List Suspended) :
    0 < occurrences uv scs ↔ ∃ sc ∈ scs, sc.var = uv := by
  induction scs with
  | nil => simp [occurrences]
  | cons first rest ih =>
      have nonnegative := occurrences_nonnegative uv rest
      by_cases same : first.var = uv
      · simp [occurrences, same]; omega
      · simpa [occurrences, same] using ih

/-- The whole slot scan is nonnegative. -/
theorem total_nonnegative (uv : Nat) (values : List (UVarValue Symbol)) : 0 ≤ total uv values := by
  induction values with
  | nil => simp [total]
  | cons value rest ih => have := occurrences_nonnegative uv (references value); simp only [total]; omega

/-- A nonzero scan count is exactly a suspended raw reference in a value slot. -/
theorem total_positive (uv : Nat) (values : List (UVarValue Symbol)) :
    0 < total uv values ↔ ∃ value ∈ values, ∃ sc ∈ references value, sc.var = uv := by
  induction values with
  | nil => simp [total]
  | cons value rest ih =>
      have firstNonnegative := occurrences_nonnegative uv (references value)
      have restNonnegative := total_nonnegative uv rest
      simp only [total, List.mem_cons, exists_eq_or_imp]
      rw [← occurrences_positive, ← ih]
      omega

/-- The sparse map contains precisely the raw waiting names, regardless of duplicate references. -/
theorem support_exact (values : List (UVarValue Symbol)) (waiting : Waiting) (correct : Correct values waiting) (uv : Nat) :
    waiting uv ≠ none ↔ ∃ value ∈ values, ∃ sc ∈ references value, sc.var = uv := by
  rw [correct uv, ← total_positive]
  have nonnegative := total_nonnegative uv values
  simp only [encode]
  split <;> simp_all <;> omega

/-- Every stored counter in a correct index is strictly positive. -/
theorem stored_positive (values : List (UVarValue Symbol)) (waiting : Waiting) (correct : Correct values waiting)
    (uv : Nat) (value : Int) (stored : waiting uv = some value) : 0 < value := by
  have nonnegative := total_nonnegative uv values
  rw [correct uv, encode] at stored
  split at stored
  · cases stored
  · have same := Option.some.inj stored
    omega

/-- Removing every old-slot occurrence cannot make any waiting count negative. -/
theorem remove_nonnegative (values : List (UVarValue Symbol)) (index : Nat) (old : UVarValue Symbol)
    (stored : values[index]? = some old) (waiting : Waiting) (correct : Correct values waiting) (uv : Nat) :
    0 ≤ read (count (-1) (references old) waiting) uv := by
  have nonnegative := total_nonnegative uv (values.set index .eliminated)
  rw [total_set uv index values old .eliminated stored] at nonnegative
  simpa [count_read, correct.facts.2 uv, references, occurrences, Int.sub_eq_add_neg] using nonnegative

end MicroCFTA.EnumerationWaitingIndex
