import MicroCFTA.SourceEqualityConstraintAllocation
import MicroCFTA.SourceEqualityPhysicalPayloadCanonical

/-!
# Completed equality-operation memo allocation

Completed entries retain their original full arguments and results. The
source fast paths and completed hits make no interner call. A computation
miss interns its actual physical output. This model does not represent
pending runtime thunks or a global evaluation schedule.
-/
namespace MicroCFTA.SourceEqualityConstraintMemoAllocation
open SourceEqualityConstraintAllocation
local notation "PhysicalKey" => SourceEqualityPartialConstraintKey.Key

/-- Combination keeps the source argument identities in order. -/
abbrev CombineKey := Option Nat × Option Nat

/-- Descent keeps the source identity and selected child index. -/
abbrev DescendKey := Option Nat × Nat

/-- A completed combination retains both original arguments and its result. -/
structure CombineCell where
  first : Value
  second : Value
  result : Value

/-- A completed descent retains its original argument, index, and result. -/
structure DescendCell where
  input : Value
  index : Nat
  result : Value

/-- The operation tables share the physical equality interner. -/
structure State where
  constraints : Cache.State PhysicalKey
  combinations : Cache.Table CombineKey CombineCell
  descents : Cache.Table DescendKey DescendCell

/-- A completed combination has stored original arguments and exact output. -/
structure CombineGood (cache : Cache.State PhysicalKey) (key : CombineKey) (cell : CombineCell) : Prop where
  first_ready : Ready cache cell.first
  second_ready : Ready cache cell.second
  result_ready : Ready cache cell.result
  key_eq : (cell.first.identity, cell.second.identity) = key
  exact : SourceEqualityInheritedPayload.combine cell.first.payload cell.second.payload = .ok cell.result.payload

/-- A completed descent has a stored original argument and exact output. -/
structure DescendGood (cache : Cache.State PhysicalKey) (key : DescendKey) (cell : DescendCell) : Prop where
  input_ready : Ready cache cell.input
  result_ready : Ready cache cell.result
  key_eq : (cell.input.identity, cell.index) = key
  exact : cell.result.payload = SourceEqualityDescend.descend cell.input.payload cell.index

/-- Every completed entry is linked to valid current canonical storage. -/
structure Valid (state : State) : Prop where
  constraints : Cache.Valid state.constraints
  combinations : ∀ key cell, state.combinations key = some cell → CombineGood state.constraints key cell
  descents : ∀ key cell, state.descents key = some cell → DescendGood state.constraints key cell

/-- Empty completed tables can start from an existing physical interner. -/
def initial (cache : Cache.State PhysicalKey) : State := ⟨cache, fun _ => none, fun _ => none⟩

/-- A cold operation state has no allocated identities or completed entries. -/
def empty : State := initial Cache.emptyState

/-- Empty completed tables preserve the supplied interner invariant. -/
theorem initial_valid (cache : Cache.State PhysicalKey) (valid : Cache.Valid cache) : Valid (initial cache) := by
  refine ⟨valid, ?_, ?_⟩ <;> intro key cell impossible <;> cases impossible

/-- The cold operation state is valid. -/
theorem empty_valid : Valid empty := initial_valid _ Cache.empty_valid

/-- Allocation receipts and completed-table growth retain all old entries. -/
structure Grows (before after : State) : Prop where
  constraints : Cache.Steps before.constraints after.constraints
  combinations : Cache.Extends before.combinations after.combinations
  descents : Cache.Extends before.descents after.descents

/-- An unchanged operation state needs no allocation event. -/
theorem grows_refl (state : State) : Grows state state :=
  ⟨.refl _, Cache.extends_refl _, Cache.extends_refl _⟩

/-- Allocation receipts retain every earlier canonical constraint value. -/
theorem Grows.constraint_growth (growth : Grows before after) :
    Cache.Extends before.constraints.table after.constraints.table := Cache.steps_table_extends growth.constraints

/-- Canonical storage growth retains every completed combination receipt. -/
theorem CombineGood.grows (good : CombineGood before key cell)
    (growth : Cache.Extends before.table after.table) : CombineGood after key cell :=
  ⟨good.first_ready.grows growth, good.second_ready.grows growth, good.result_ready.grows growth,
    good.key_eq, good.exact⟩

/-- Canonical storage growth retains every completed descent receipt. -/
theorem DescendGood.grows (good : DescendGood before key cell)
    (growth : Cache.Extends before.table after.table) : DescendGood after key cell :=
  ⟨good.input_ready.grows growth, good.result_ready.grows growth, good.key_eq, good.exact⟩

/-- Independent physical allocations preserve unchanged completed tables. -/
theorem Valid.grows (valid : Valid before) (cache : Cache.State PhysicalKey)
    (cacheValid : Cache.Valid cache) (growth : Cache.Extends before.constraints.table cache.table) :
    Valid { before with constraints := cache } :=
  ⟨cacheValid, fun key cell present => (valid.combinations key cell present).grows growth,
    fun key cell present => (valid.descents key cell present).grows growth⟩

/-- Independent permitted allocation steps preserve both completed memo tables. -/
theorem Valid.steps (valid : Valid before) (cache : Cache.State PhysicalKey)
    (steps : Cache.Steps before.constraints cache) : Valid { before with constraints := cache } :=
  valid.grows cache (Cache.steps_valid valid.constraints steps) (Cache.steps_table_extends steps)

/-- Equal canonical identities determine complete ready physical values. -/
theorem ready_eq_of_identity (cache : Cache.State PhysicalKey) (valid : Cache.Valid cache)
    (first second : Value) (firstReady : Ready cache first) (secondReady : Ready cache second)
    (same : first.identity = second.identity) : first = second := by
  have keys := SourceEqualityPartialKeyTransport.recorded_key_eq cache valid first.payload second.payload
    first.identity firstReady.1 (same.symm ▸ secondReady.1)
  have payloads := SourceEqualityPhysicalPayloadCanonical.eq_of_key first.payload second.payload
    firstReady.2 secondReady.2 keys
  cases first <;> cases second <;> simp_all [Value.identity, Value.payload]

private theorem keepFirst_good [DecidableEq Key] (property : Key → Cell → Prop)
    (table : Cache.Table Key Cell) (old : ∀ key cell, table key = some cell → property key cell)
    (key : Key) (cell : Cell) (good : property key cell) :
    ∀ other stored, Cache.keepFirst table key cell other = some stored → property other stored := by
  intro other stored present
  cases found : table key with
  | some existing => exact old other stored (by simpa only [Cache.keepFirst, found] using present)
  | none =>
      by_cases same : other = key
      · subst other
        have identical : cell = stored := by simpa [Cache.keepFirst, found, Cache.put] using present
        exact identical ▸ good
      · exact old other stored (by simpa [Cache.keepFirst, found, Cache.put, same] using present)

private theorem Valid.insert_combine (valid : Valid state) (key : CombineKey) (cell : CombineCell)
    (good : CombineGood state.constraints key cell) :
    Valid { state with combinations := Cache.keepFirst state.combinations key cell } :=
  ⟨valid.constraints, keepFirst_good _ _ valid.combinations key cell good, valid.descents⟩

private theorem Valid.insert_descend (valid : Valid state) (key : DescendKey) (cell : DescendCell)
    (good : DescendGood state.constraints key cell) :
    Valid { state with descents := Cache.keepFirst state.descents key cell } :=
  ⟨valid.constraints, valid.combinations, keepFirst_good _ _ valid.descents key cell good⟩

/-- Read a completed combination or compute and intern its physical output. -/
noncomputable def combineCached (first second : Value) (before : State) : Except String Value × State :=
  let key := (first.identity, second.identity)
  match before.combinations key with
  | some cell => (.ok cell.result, before)
  | none => match SourceEqualityInheritedPayload.combine first.payload second.payload with
    | .error message => (.error message, before)
    | .ok payload =>
        let built := intern payload before.constraints
        (.ok built.1, { before with
          constraints := built.2
          combinations := Cache.keepFirst before.combinations key ⟨first, second, built.1⟩ })

/-- Source combination bypasses its memo only for contradiction or two live empty operands. -/
noncomputable def combine (first second : Value) (before : State) : Except String Value × State :=
  match first, second with
  | .contradiction, _ | _, .contradiction => (.ok .contradiction, before)
  | .live _ [], .live _ [] => (.ok first, before)
  | _, _ => combineCached first second before

/-- Read a completed descent or compute and intern its physical output. -/
def descendCached (input : Value) (index : Nat) (before : State) : Value × State :=
  let key := (input.identity, index)
  match before.descents key with
  | some cell => (cell.result, before)
  | none =>
      let built := intern (SourceEqualityDescend.descend input.payload index) before.constraints
      (built.1, { before with
        constraints := built.2
        descents := Cache.keepFirst before.descents key ⟨input, index, built.1⟩ })

/-- Source descent bypasses its memo for contradiction and live empty payloads. -/
def descend (input : Value) (index : Nat) (before : State) : Value × State :=
  match input with
  | .contradiction | .live _ [] => (input, before)
  | _ => descendCached input index before

/-- A completed combination hit retains the whole operation state. -/
theorem combineCached_hit (first second : Value) (before : State) (cell : CombineCell)
    (present : before.combinations (first.identity, second.identity) = some cell) :
    combineCached first second before = (.ok cell.result, before) := by
  simp only [combineCached, present]

/-- A completed descent hit retains the whole operation state. -/
theorem descendCached_hit (input : Value) (index : Nat) (before : State) (cell : DescendCell)
    (present : before.descents (input.identity, index) = some cell) :
    descendCached input index before = (cell.result, before) := by
  simp only [descendCached, present]

/-- A top-level combination with an existing key makes no state change. -/
theorem combine_state_of_hit (first second : Value) (before : State) (cell : CombineCell)
    (present : before.combinations (first.identity, second.identity) = some cell) :
    (combine first second before).2 = before := by
  cases first with
  | contradiction => rfl
  | live firstIdentity firstRecords =>
      cases second with
      | contradiction => rfl
      | live secondIdentity secondRecords =>
          cases firstRecords <;> cases secondRecords
          all_goals first | rfl | exact congrArg Prod.snd (combineCached_hit _ _ before cell present)

/-- A top-level descent with an existing key makes no state change. -/
theorem descend_state_of_hit (input : Value) (index : Nat) (before : State) (cell : DescendCell)
    (present : before.descents (input.identity, index) = some cell) :
    (descend input index before).2 = before := by
  cases input with
  | contradiction => rfl
  | live identity records =>
      cases records with
      | nil => rfl
      | cons head tail => exact congrArg Prod.snd (descendCached_hit _ index before cell present)

/-- A combination computation or completed hit preserves exact ready output and allocation receipts. -/
theorem combineCached_correct (first second : Value) (before : State) (valid : Valid before)
    (firstReady : Ready before.constraints first) (secondReady : Ready before.constraints second) :
    ∃ result, (combineCached first second before).1 = .ok result ∧
      Valid (combineCached first second before).2 ∧
      Ready (combineCached first second before).2.constraints result ∧
      SourceEqualityInheritedPayload.combine first.payload second.payload = .ok result.payload ∧
      Grows before (combineCached first second before).2 := by
  cases found : before.combinations (first.identity, second.identity) with
  | some cell =>
      have good := valid.combinations _ cell found
      have firstSame := ready_eq_of_identity before.constraints valid.constraints cell.first first
        good.first_ready firstReady (congrArg Prod.fst good.key_eq)
      have secondSame := ready_eq_of_identity before.constraints valid.constraints cell.second second
        good.second_ready secondReady (congrArg Prod.snd good.key_eq)
      rw [combineCached_hit first second before cell found]
      refine ⟨cell.result, rfl, valid, good.result_ready, ?_, grows_refl before⟩
      simpa only [firstSame, secondSame] using good.exact
  | none =>
      obtain ⟨payload, built, wellFormed, _⟩ :=
        SourceEqualityInheritedPayload.combine_complete (Symbol := Unit) first.payload second.payload
      have cacheValid := (intern_valid payload before.constraints valid.constraints).1
      have growth := intern_growth payload before.constraints
      have outputReady := intern_ready payload before.constraints valid.constraints wellFormed
      have good : CombineGood (intern payload before.constraints).2 (first.identity, second.identity)
          ⟨first, second, (intern payload before.constraints).1⟩ := by
        refine ⟨firstReady.grows growth, secondReady.grows growth, outputReady, rfl, ?_⟩
        rw [intern_payload]
        exact built
      have updated := (valid.grows _ cacheValid growth).insert_combine _ _ good
      simp only [combineCached, found, built]
      exact ⟨(intern payload before.constraints).1, rfl, updated, outputReady,
        by simp only [intern_payload],
        ⟨intern_steps payload before.constraints, Cache.keepFirst_extends _ _ _, Cache.extends_refl _⟩⟩

/-- A descent computation or completed hit preserves exact ready output and allocation receipts. -/
theorem descendCached_correct (input : Value) (index : Nat) (before : State) (valid : Valid before)
    (inputReady : Ready before.constraints input) :
    Valid (descendCached input index before).2 ∧
      Ready (descendCached input index before).2.constraints (descendCached input index before).1 ∧
      (descendCached input index before).1.payload = SourceEqualityDescend.descend input.payload index ∧
      Grows before (descendCached input index before).2 := by
  cases found : before.descents (input.identity, index) with
  | some cell =>
      have good := valid.descents _ cell found
      have inputSame := ready_eq_of_identity before.constraints valid.constraints cell.input input
        good.input_ready inputReady (congrArg Prod.fst good.key_eq)
      have indexSame : cell.index = index := congrArg Prod.snd good.key_eq
      rw [descendCached_hit input index before cell found]
      refine ⟨valid, good.result_ready, ?_, grows_refl before⟩
      simpa only [inputSame, indexSame] using good.exact
  | none =>
      let payload := SourceEqualityDescend.descend input.payload index
      have wellFormed := SourceEqualityDescend.descend_wellFormed input.payload inputReady.2 index
      have cacheValid := (intern_valid payload before.constraints valid.constraints).1
      have growth := intern_growth payload before.constraints
      have outputReady := intern_ready payload before.constraints valid.constraints wellFormed
      have good : DescendGood (intern payload before.constraints).2 (input.identity, index)
          ⟨input, index, (intern payload before.constraints).1⟩ :=
        ⟨inputReady.grows growth, outputReady, rfl, intern_payload payload before.constraints⟩
      have updated := (valid.grows _ cacheValid growth).insert_descend _ _ good
      simp only [descendCached, found]
      exact ⟨updated, outputReady, intern_payload payload before.constraints,
        ⟨intern_steps payload before.constraints, Cache.extends_refl _, Cache.keepFirst_extends _ _ _⟩⟩

private theorem contradiction_ready (cache : Cache.State PhysicalKey) : Ready cache .contradiction :=
  ⟨trivial, by intro originals impossible; cases impossible⟩

/-- Actual source combination completes and preserves valid storage, exact payload, and cache growth. -/
theorem combine_correct (first second : Value) (before : State) (valid : Valid before)
    (firstReady : Ready before.constraints first) (secondReady : Ready before.constraints second) :
    ∃ result, (combine first second before).1 = .ok result ∧
      Valid (combine first second before).2 ∧
      Ready (combine first second before).2.constraints result ∧
      SourceEqualityInheritedPayload.combine first.payload second.payload = .ok result.payload ∧
      Grows before (combine first second before).2 := by
  cases first with
  | contradiction =>
      refine ⟨.contradiction, rfl, valid, contradiction_ready _, ?_, grows_refl before⟩
      cases second <;> rfl
  | live firstIdentity firstRecords =>
      cases second with
      | contradiction =>
          refine ⟨.contradiction, rfl, valid, contradiction_ready _, ?_, grows_refl before⟩
          rfl
      | live secondIdentity secondRecords =>
          cases firstRecords with
          | nil =>
              cases secondRecords with
              | nil => exact ⟨.live firstIdentity [], rfl, valid, firstReady, rfl, grows_refl before⟩
              | cons head tail => exact combineCached_correct _ _ before valid firstReady secondReady
          | cons head tail =>
              cases secondRecords <;> exact combineCached_correct _ _ before valid firstReady secondReady

/-- Actual source descent preserves valid storage, exact payload, and cache growth. -/
theorem descend_correct (input : Value) (index : Nat) (before : State) (valid : Valid before)
    (inputReady : Ready before.constraints input) :
    Valid (descend input index before).2 ∧
      Ready (descend input index before).2.constraints (descend input index before).1 ∧
      (descend input index before).1.payload = SourceEqualityDescend.descend input.payload index ∧
      Grows before (descend input index before).2 := by
  cases input with
  | contradiction => exact ⟨valid, inputReady, rfl, grows_refl before⟩
  | live identity records =>
      cases records with
      | nil => exact ⟨valid, inputReady, rfl, grows_refl before⟩
      | cons head tail => exact descendCached_correct _ index before valid inputReady

end MicroCFTA.SourceEqualityConstraintMemoAllocation
