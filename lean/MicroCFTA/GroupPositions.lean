import MicroCFTA.DecoderMachineBounds

/-!
# Position tables for finite and recursive group maps

Source regrouping needs keys, not member cardinalities. The key map is finite
even when a group has an unbounded recursive language. The position table
keeps the first occurrence of every identity in ascending source-key order.
-/
namespace MicroCFTA.GroupPositions

/-- Extensional lookup for the source map. -/
abbrev Table (Key : Type) := Key → Option Nat

/-- Map.fromListWith keeps an existing earlier position. -/
def insertFirst [DecidableEq Key] (table : Table Key) (key : Key) (position : Nat) : Table Key :=
  fun queried => if queried = key then (table queried).or (some position) else table queried

/-- Execute source zip positions and left-to-right map insertion. -/
def buildFrom [DecidableEq Key] (start : Nat) : List Key → Table Key → Table Key
  | [], table => table
  | key :: rest, table => buildFrom (start + 1) rest (insertFirst table key start)

/-- The independent first-occurrence specification. -/
def locate [DecidableEq Key] (start : Nat) : List Key → Key → Option Nat
  | [], _ => none
  | key :: rest, queried => if queried = key then some start else locate (start + 1) rest queried

/-- Existing positions survive all subsequent insertions. -/
theorem build_preserves [DecidableEq Key] (keys : List Key) (table : Table Key)
    (key : Key) (position start : Nat) (found : table key = some position) :
    buildFrom start keys table key = some position := by
  induction keys generalizing table start with
  | nil => exact found
  | cons first rest ih =>
      apply ih
      by_cases same : key = first
      · subst first; simp [insertFirst, found]
      · simp [insertFirst, same, found]

/-- The source map fold records exactly the first available occurrence. -/
theorem build_lookup [DecidableEq Key] (keys : List Key) (table : Table Key)
    (key : Key) (start : Nat) :
    buildFrom start keys table key = (table key).or (locate start keys key) := by
  cases found : table key with
  | some position => simpa [found] using build_preserves keys table key position start found
  | none =>
      induction keys generalizing table start with
      | nil => simp [buildFrom, locate, found]
      | cons first rest ih =>
          by_cases same : key = first
          · subst first
            simp only [buildFrom]
            rw [build_preserves rest (insertFirst table key start) key start (start + 1)
              (by simp [insertFirst, found])]
            simp [locate]
          · rw [buildFrom, ih (insertFirst table first start) (start + 1)
              (by simp [insertFirst, same, found])]
            simp [locate, same]

/-- Source positions start at zero. -/
def firstPositions [DecidableEq Key] (keys : List Key) : Table Key :=
  buildFrom 0 keys (fun _ => none)

theorem firstPositions_exact [DecidableEq Key] (keys : List Key) (key : Key) :
    firstPositions keys key = locate 0 keys key := by
  simp [firstPositions, build_lookup]

/-- A position exists exactly when its identity occurs in the source list. -/
theorem locate_exists [DecidableEq Key] (keys : List Key) (key : Key) (start : Nat) :
    (∃ position, locate start keys key = some position) ↔ key ∈ keys := by
  induction keys generalizing start with
  | nil => simp [locate]
  | cons first rest ih =>
      by_cases same : key = first <;> simp [locate, same, ih]

/-- Every stored position is inside the zipped interval. -/
theorem locate_bounds [DecidableEq Key] (keys : List Key) (key : Key) (start position : Nat)
    (found : locate start keys key = some position) :
    start ≤ position ∧ position < start + keys.length := by
  induction keys generalizing start with
  | nil => simp [locate] at found
  | cons first rest ih =>
      by_cases same : key = first
      · simp [locate, same] at found
        subst position
        simp
      · have later := ih (start + 1) (by simpa [locate, same] using found)
        simp only [List.length_cons]
        omega

/-- Keys are available independently of the recursive member count. -/
structure Groups (Key Value Error : Type) where
  cyclic : Bool
  entries : Except Error (List (Key × Value))

/-- Both current source constructors inspect their stored map directly. -/
def groupKeys (groups : Groups Key Value Error) : List Key :=
  match groups.entries with
  | .error _ => []
  | .ok entries => entries.map Prod.fst

/-- The previous cardinality-based key discovery hides successful recursive maps. -/
def oldKeys (groups : Groups Key Value Error) : List Key :=
  if groups.cyclic then [] else groupKeys groups

/-- Both positioning callers derive their complete identity table from groupKeys. -/
def positions [DecidableEq Identity] (identity : Key → Identity) (groups : Groups Key Value Error) :
    Table Identity := firstPositions ((groupKeys groups).map identity)

/-- Every key passed to regroupOn has a safe position lookup. -/
theorem regroup_lookup [DecidableEq Identity] (identity : Key → Identity)
    (groups : Groups Key Value Error) (entries : List (Key × Value))
    (success : groups.entries = .ok entries) (entry : Key × Value) (member : entry ∈ entries) :
    ∃ position, positions identity groups (identity entry.1) = some position ∧
      position < entries.length := by
  have present : identity entry.1 ∈ (groupKeys groups).map identity := by
    simp only [groupKeys, success]
    exact List.mem_map.mpr ⟨entry.1, List.mem_map.mpr ⟨entry, member, rfl⟩, rfl⟩
  obtain ⟨position, found⟩ := (locate_exists _ _ 0).mpr present
  refine ⟨position, ?_, ?_⟩
  · simpa [positions, firstPositions_exact] using found
  · have bounds := locate_bounds _ _ 0 position found
    simpa [groupKeys, success] using bounds.2

/-- A cyclic flag cannot change the key table or any position. -/
theorem recursive_positions [DecidableEq Identity] (identity : Key → Identity)
    (entries : Except Error (List (Key × Value))) :
    positions identity (Groups.mk true entries) = positions identity (Groups.mk false entries) := rfl

/-- Source Int positions agree with the natural positions within the signed range. -/
theorem position_machine [DecidableEq Key] (bits : Nat) (keys : List Key)
    (key : Key) (position : Nat) (found : firstPositions keys key = some position)
    (fits : keys.length ≤ DecoderMachineBounds.maximum bits + 1) :
    DecoderMachineBounds.narrow bits position = (position : Int) := by
  have bounds := locate_bounds keys key 0 position (by simpa [firstPositions_exact] using found)
  exact DecoderMachineBounds.narrow_exact bits position (by omega)

/-- One successful recursive bucket is enough to refute the old lookup guarantee. -/
theorem old_recursive_counterexample :
    firstPositions (oldKeys (Groups.mk true (.ok [(7, ())]) : Groups Nat Unit Unit)) 7 = none ∧
    positions id (Groups.mk true (.ok [(7, ())]) : Groups Nat Unit Unit) 7 = some 0 := by
  decide

end MicroCFTA.GroupPositions
