import MicroCFTA.SourceSizedPreprocessing

/-!
# One ordered minimum-size pass

The finite original state sequence supplies the key scan order.
Each key reads the table returned by its suffix before inserting one minimum.
Map key-order and Integer-table representation correspondence remain separate.
-/
namespace MicroCFTA.SourceSizedMinimumPass
open SourceSizedDecided (Row)
variable {Q Symbol Guard : Type}
/-- Each state has either no known size or one signed Integer size. -/
abbrev Table (Q : Type) := Q → Option Int

/-- All children are read in row order from the same current known table. -/
def transitionMinimum (known : Table Q) (row : Row Q Symbol Guard) : Option Int :=
  (row.children.mapM known).map fun sizes => 1 + sizes.sum

/-- Select the first available size and fold min in the original row order. -/
def least : List Int → Option Int
  | [] => none
  | first :: rest => some (rest.foldl min first)

/-- InsertWith min retains every earlier known value as an upper bound. -/
def insertMinimum [DecidableEq Q] (key : Q) (value : Int) (known : Table Q) : Table Q :=
  fun current => if current = key then
    some (match known key with | none => value | some old => min value old)
  else known current

/-- Every row cost uses known before the single key update. -/
def addMinimum [DecidableEq Q] (key : Q) (rows : List (Row Q Symbol Guard)) (known : Table Q) : Table Q :=
  match least (rows.filterMap (transitionMinimum known)) with
  | none => known
  | some value => insertMinimum key value known

/-- A right fold retains the actual within-pass table lookups. -/
def scan [DecidableEq Q] (source : Q → List (Row Q Symbol Guard)) : List Q → Table Q → Table Q
  | [], known => known
  | key :: rest, known => addMinimum key (source key) (scan source rest known)

/-- The original finite carrier grounds the complete pass. -/
def pass [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard) (known : Table Q) : Table Q :=
  scan input.rows input.states known

private theorem lookup_sum_nonnegative (known : Table Q)
    (positive : ∀ current value, known current = some value → 0 < value)
    (children : List Q) (sizes : List Int) (found : children.mapM known = some sizes) : 0 ≤ sizes.sum := by
  induction children generalizing sizes with
  | nil =>
      change some [] = some sizes at found
      have same := Option.some.inj found
      subst sizes
      simp
  | cons first rest ih =>
      cases head : known first with
      | none => simp [List.mapM_cons, head] at found
      | some value =>
          cases tail : rest.mapM known with
          | none => simp [List.mapM_cons, head, tail] at found
          | some values =>
              have firstPositive := positive first value head
              have restNonnegative := ih values tail
              have same : value :: values = sizes := by simpa [List.mapM_cons, head, tail] using found
              subst sizes
              simp only [List.sum_cons]
              omega

private theorem transition_positive (known : Table Q)
    (positive : ∀ current value, known current = some value → 0 < value)
    (row : Row Q Symbol Guard) (value : Int) (found : transitionMinimum known row = some value) : 0 < value := by
  cases children : row.children.mapM known with
  | none => simp [transitionMinimum, children] at found
  | some sizes =>
      have nonnegative := lookup_sum_nonnegative known positive row.children sizes children
      simp only [transitionMinimum, children, Option.map_some, Option.some.injEq] at found
      omega

private theorem fold_positive (sizes : List Int) (first : Int) (positive : 0 < first)
    (others : ∀ value ∈ sizes, 0 < value) : 0 < sizes.foldl min first := by
  induction sizes generalizing first with
  | nil => exact positive
  | cons next rest ih =>
      have nextPositive := others next List.mem_cons_self
      exact ih (min first next) (by omega) (fun value member => others value (List.mem_cons_of_mem _ member))

private theorem least_positive (sizes : List Int) (positive : ∀ value ∈ sizes, 0 < value)
    (value : Int) (found : least sizes = some value) : 0 < value := by
  cases sizes with
  | nil => simp [least] at found
  | cons first rest =>
      simp only [least, Option.some.injEq] at found
      have bound := fold_positive rest first (positive first List.mem_cons_self)
        (fun item member => positive item (List.mem_cons_of_mem _ member))
      exact found ▸ bound

private theorem selected_positive (known : Table Q)
    (positive : ∀ current value, known current = some value → 0 < value)
    (rows : List (Row Q Symbol Guard)) (value : Int)
    (found : least (rows.filterMap (transitionMinimum known)) = some value) : 0 < value := by
  apply least_positive _ _ value found
  intro size member
  obtain ⟨row, _present, actual⟩ := List.mem_filterMap.mp member
  exact transition_positive known positive row size actual

/-- One actual key step changes only its key and never increases an old value. -/
private theorem add_spec [DecidableEq Q] (key : Q) (rows : List (Row Q Symbol Guard))
    (known : Table Q) (current : Q) :
    addMinimum key rows known current = known current ∨
      ∃ value, addMinimum key rows known current = some value ∧ current = key ∧
        ∀ old, known current = some old → value ≤ old := by
  cases selected : least (rows.filterMap (transitionMinimum known)) with
  | none => exact Or.inl (by simp only [addMinimum, selected])
  | some value =>
      by_cases same : current = key
      · subst current
        cases oldLookup : known key with
        | none =>
            refine Or.inr ⟨value, ?_, rfl, ?_⟩
            · simp only [addMinimum, selected, insertMinimum, ite_eq_left, oldLookup]
            · intro old impossible
              simp only [reduceCtorEq] at impossible
        | some old =>
            refine Or.inr ⟨min value old, ?_, rfl, ?_⟩
            · simp only [addMinimum, selected, insertMinimum, ite_eq_left, oldLookup]
            · intro previous found
              simp only [Option.some.injEq] at found
              omega
      · exact Or.inl (by simp only [addMinimum, selected, insertMinimum, ite_eq_right same])

private theorem add_positive [DecidableEq Q] (key : Q) (rows : List (Row Q Symbol Guard))
    (known : Table Q) (positive : ∀ current value, known current = some value → 0 < value)
    (current : Q) (value : Int) (found : addMinimum key rows known current = some value) : 0 < value := by
  cases selected : least (rows.filterMap (transitionMinimum known)) with
  | none => exact positive current value (by simpa only [addMinimum, selected] using found)
  | some candidate =>
      have candidatePositive := selected_positive known positive rows candidate selected
      by_cases same : current = key
      · subst current
        cases oldLookup : known key with
        | none =>
            simp only [addMinimum, selected, insertMinimum, ite_eq_left, oldLookup, Option.some.injEq] at found
            omega
        | some old =>
            have oldPositive := positive key old oldLookup
            simp only [addMinimum, selected, insertMinimum, ite_eq_left, oldLookup, Option.some.injEq] at found
            omega
      · exact positive current value (by simpa only [addMinimum, selected, insertMinimum, ite_eq_right same] using found)

private theorem scan_spec [DecidableEq Q] (source : Q → List (Row Q Symbol Guard))
    (keys : List Q) (known : Table Q) (current : Q) :
    scan source keys known current = known current ∨
      ∃ value, scan source keys known current = some value ∧ current ∈ keys ∧
        ∀ old, known current = some old → value ≤ old := by
  induction keys with
  | nil => exact Or.inl rfl
  | cons key rest ih =>
      cases ih with
      | inl retained =>
          cases add_spec key (source key) (scan source rest known) current with
          | inl same => exact Or.inl (same.trans retained)
          | inr changed =>
              obtain ⟨value, found, atKey, bounded⟩ := changed
              refine Or.inr ⟨value, found, List.mem_cons.mpr (Or.inl atKey), ?_⟩
              intro old before
              apply bounded old
              rw [retained]
              exact before
      | inr changed =>
          obtain ⟨middle, actual, listed, bounded⟩ := changed
          cases add_spec key (source key) (scan source rest known) current with
          | inl same => exact Or.inr ⟨middle, same.trans actual, List.mem_cons_of_mem _ listed, bounded⟩
          | inr updated =>
              obtain ⟨value, found, atKey, nextBound⟩ := updated
              exact Or.inr ⟨value, found, List.mem_cons.mpr (Or.inl atKey),
                fun old before => Int.le_trans (nextBound middle actual) (bounded old before)⟩

private theorem scan_positive [DecidableEq Q] (source : Q → List (Row Q Symbol Guard))
    (keys : List Q) (known : Table Q) (positive : ∀ current value, known current = some value → 0 < value) :
    ∀ current value, scan source keys known current = some value → 0 < value := by
  induction keys with
  | nil => exact positive
  | cons key rest ih => exact add_positive key (source key) (scan source rest known) ih

/-- Original rows and any signed known table derive one-pass support and value effects. -/
theorem pass_spec [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (known : Table Q) (current : Q) :
    pass input known current = known current ∨
      ∃ value, pass input known current = some value ∧ current ∈ input.states ∧
        ∀ old, known current = some old → value ≤ old :=
  scan_spec input.rows input.states known current

/-- A known entry remains known and its actual signed new value cannot increase. -/
theorem pass_known [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (known : Table Q) (current : Q) (old : Int) (before : known current = some old) :
    ∃ value, pass input known current = some value ∧ value ≤ old := by
  rcases pass_spec input known current with retained | ⟨value, found, _listed, bounded⟩
  · exact ⟨old, retained.trans before, Int.le_refl _⟩
  · exact ⟨value, found, bounded old before⟩

/-- The actual pass preserves positivity of every known entry. -/
theorem pass_positive [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (known : Table Q) (positive : ∀ current value, known current = some value → 0 < value) :
    ∀ current value, pass input known current = some value → 0 < value :=
  scan_positive input.rows input.states known positive

/-- Original rows produce the actual positive cold-pass table without a future result input. -/
theorem cold_pass [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard) :
    ∃ next : Table Q, next = pass input (fun _ => none) ∧
      ∀ current value, next current = some value → current ∈ input.states ∧ 0 < value := by
  refine ⟨pass input (fun _ => none), rfl, ?_⟩
  intro current value found
  have positive : ∀ current value, scan input.rows input.states (fun _ => none) current = some value → 0 < value :=
    scan_positive input.rows input.states (fun _ => none) (by intro state size impossible; cases impossible)
  have membership : current ∈ input.states := by
    rcases pass_spec input (fun _ => none) current with retained | ⟨next, actual, listed, _bounded⟩
    · simp only [retained, reduceCtorEq] at found
    · exact listed
  exact ⟨membership, positive current value found⟩

end MicroCFTA.SourceSizedMinimumPass
