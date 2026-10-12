import MicroCFTA.KeyedTermBoundary
import MicroCFTA.GroupPositions
import MicroCFTA.SupportGraph

/-!
# Source key positions for recursive member terms

Recur assigns zero-based positions to the distinct ascending map keys.
The overwrite fold models Map.fromList on the zipped entries. Every key
has a position, and two different keys cannot share a private term wrapper.
-/
namespace MicroCFTA.KeyedTermCodes
open Language GeneratorCombinators IntegerTermViews
open RecursiveCallbackTermination KeyedTermBoundary

/-- Insert each zipped key with the source Map.fromList overwrite rule. -/
def buildFrom [DecidableEq Key] (start : Nat) : List Key → GroupPositions.Table Key → GroupPositions.Table Key
  | [], table => table
  | key :: rest, table => buildFrom (start + 1) rest (fun queried => if queried = key then some start else table queried)

/-- Inserting other keys cannot change a stored position. -/
theorem build_absent [DecidableEq Key] (keys : List Key) (start : Nat)
    (table : GroupPositions.Table Key) (key : Key) (absent : key ∉ keys) :
    buildFrom start keys table key = table key := by
  induction keys generalizing start table with
  | nil => rfl
  | cons first rest ih =>
      have different : key ≠ first := fun same => absent (by simp [same])
      have later : key ∉ rest := fun member => absent (by simp [member])
      rw [buildFrom, ih _ _ later]
      simp [different]

/-- Distinct source keys give the same exact position under either insertion policy. -/
theorem build_lookup [DecidableEq Key] (keys : List Key) (unique : keys.Nodup)
    (start : Nat) (table : GroupPositions.Table Key) (key : Key) :
    buildFrom start keys table key = (GroupPositions.locate start keys key).or (table key) := by
  induction keys generalizing start table with
  | nil => simp [buildFrom, GroupPositions.locate]
  | cons first rest ih =>
      obtain ⟨absent, distinct⟩ := List.nodup_cons.mp unique
      by_cases same : key = first
      · subst key
        rw [buildFrom, build_absent rest (start + 1) _ first absent]
        simp [GroupPositions.locate]
      · rw [buildFrom, ih distinct]
        simp [GroupPositions.locate, same]

/-- Source positions use the complete map-key list and start at zero. -/
def table [DecidableEq Key] (keys : List Key) : GroupPositions.Table Key :=
  buildFrom 0 keys (fun _ => none)

/-- Every declared member has one safe finite map lookup. -/
theorem lookup_total [DecidableEq Key] (keys : List Key) (unique : keys.Nodup)
    (key : Key) (member : key ∈ keys) :
    ∃ position, table keys key = some position ∧ position < keys.length := by
  obtain ⟨position, found⟩ := (GroupPositions.locate_exists keys key 0).mpr member
  refine ⟨position, ?_, ?_⟩
  · simp [table, build_lookup keys unique, found]
  · simpa using (GroupPositions.locate_bounds keys key 0 position found).2

/-- One zipped position cannot identify two keys. -/
theorem locate_injective [DecidableEq Key] (keys : List Key) (start : Nat)
    (left right : Key) (position : Nat)
    (first : GroupPositions.locate start keys left = some position)
    (second : GroupPositions.locate start keys right = some position) : left = right := by
  induction keys generalizing start with
  | nil => simp [GroupPositions.locate] at first
  | cons key rest ih =>
      by_cases leftSame : left = key
      · have offset : start = position := by simpa [GroupPositions.locate, leftSame] using first
        by_cases rightSame : right = key
        · exact leftSame.trans rightSame.symm
        · have later : GroupPositions.locate (start + 1) rest right = some position := by
            simpa [GroupPositions.locate, rightSame] using second
          have bound := (GroupPositions.locate_bounds rest right (start + 1) position later).1
          omega
      · by_cases rightSame : right = key
        · have offset : start = position := by simpa [GroupPositions.locate, rightSame] using second
          have later : GroupPositions.locate (start + 1) rest left = some position := by
            simpa [GroupPositions.locate, leftSame] using first
          have bound := (GroupPositions.locate_bounds rest left (start + 1) position later).1
          omega
        · exact ih (start + 1) (by simpa [GroupPositions.locate, leftSame] using first)
            (by simpa [GroupPositions.locate, rightSame] using second)

/-- The source partial lookup is total on a complete declared key family. -/
def code [DecidableEq Key] (keys : List Key) (key : Key) : Nat := (table keys key).getD 0

theorem code_lookup [DecidableEq Key] (keys : List Key) (unique : keys.Nodup)
    (complete : ∀ key, key ∈ keys) (key : Key) : table keys key = some (code keys key) := by
  obtain ⟨position, found, _⟩ := lookup_total keys unique key (complete key)
  simp [code, found]

/-- Every concrete code stays within the finite source key interval. -/
theorem code_bound [DecidableEq Key] (keys : List Key) (unique : keys.Nodup)
    (complete : ∀ key, key ∈ keys) (key : Key) : code keys key < keys.length := by
  obtain ⟨position, found, bound⟩ := lookup_total keys unique key (complete key)
  simpa [code, found] using bound

/-- A representable key-table size makes the source Int label exact. -/
theorem code_machine [DecidableEq Key] (keys : List Key) (unique : keys.Nodup)
    (complete : ∀ key, key ∈ keys) (bits : Nat)
    (fits : keys.length ≤ DecoderMachineBounds.maximum bits) (key : Key) :
    DecoderMachineBounds.narrow bits (code keys key) = (code keys key : Int) :=
  DecoderMachineBounds.narrow_exact bits _ (by have := code_bound keys unique complete key; omega)

/-- The concrete key-position producer discharges the wrapper identity contract. -/
theorem code_injective [DecidableEq Key] (keys : List Key) (unique : keys.Nodup)
    (complete : ∀ key, key ∈ keys) : Function.Injective (code keys) := by
  intro left right same
  have first := code_lookup keys unique complete left
  have second := code_lookup keys unique complete right
  simp only [table, build_lookup keys unique, Option.or_none] at first second
  rw [← same] at second
  exact locate_injective keys 0 left right _ first second

/-- Complete member wrappers from different declared keys are disjoint. -/
theorem member_identity [DecidableEq Key] (keys : List Key) (unique : keys.Nodup)
    (complete : ∀ key, key ∈ keys) (left right : Key) (first second : EngineTerm Symbol) :
    atKeyTerm (code keys left) first = atKeyTerm (code keys right) second ↔
      left = right ∧ first = second := by
  rw [wrapper_injective]
  constructor
  · rintro ⟨same, bodies⟩
    exact ⟨code_injective keys unique complete same, bodies⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- The actual family restriction accepts exactly the selected key's wrapped body. -/
theorem support_exact [DecidableEq Key] (keys : List Key) (unique : keys.Nodup)
    (complete : ∀ key, key ∈ keys) (environment : BinderLanguage.Env (Label Symbol))
    (bodies : Key → SupportGraph.Support Symbol) (key : Key) (term : EngineTerm Symbol) :
    BinderLanguage.meaning environment
      (SupportGraph.restrictKey (code keys key)
        (SupportGraph.family (keys.map fun child => (code keys child, bodies child)))) term ↔
      ∃ child, BinderLanguage.meaning environment (bodies key) child ∧
        term = atKeyTerm (code keys key) child := by
  rw [SupportGraph.restrict_family_exact]
  constructor
  · rintro ⟨body, member, child, accepted, same⟩
    obtain ⟨found, _, pair⟩ := List.mem_map.mp member
    have keyEq := code_injective keys unique complete (congrArg Prod.fst pair)
    subst found
    have bodyEq : bodies key = body := congrArg Prod.snd pair
    exact ⟨child, bodyEq ▸ accepted, same⟩
  · rintro ⟨child, accepted, same⟩
    exact ⟨bodies key, List.mem_map.mpr ⟨key, complete key, rfl⟩, child, accepted, same⟩

end MicroCFTA.KeyedTermCodes
