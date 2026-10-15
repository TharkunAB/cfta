import MicroCFTA.SourceEqualityPartialConstraintRenaming
import MicroCFTA.SourceEqualityInheritedPayload

/-!
# Allocation receipts for complete physical equality payloads

Live values retain the identity and full physical class records. Contradiction
has no live identity. Interning records actual abstract reserve and install
steps. The result remains linked to the original physical trie key.
Runtime cache adequacy and signed machine capacity remain separate.
-/
namespace MicroCFTA.SourceEqualityConstraintAllocation
open Cache SourceEqualityPartialConstraintKey SourceEqualityPartialKeyTransport

/-- Consecutive actual interner traces retain their complete atomic receipt. -/
theorem steps_trans {before middle after : Cache.State Key}
    (first : Cache.Steps before middle) (second : Cache.Steps middle after) : Cache.Steps before after := by
  induction second with
  | refl => exact first
  | next earlier step ih => exact .next ih step

/-- A complete source equality value has either a live identity or the contradiction tag. -/
inductive Value where
  | contradiction
  | live (identity : Nat) (records : List SourceEqualityClassOrder.Record)

/-- Read the complete physical payload without its allocation identity. -/
def Value.payload : Value → SourceEqualityPrecheck.Constraint
  | .contradiction => none
  | .live _ records => some records

/-- Read the source equality identity while retaining contradiction separately. -/
def Value.identity : Value → Option Nat
  | .contradiction => none
  | .live identity _ => some identity

/-- A complete value has its physical key in the current canonical interner. -/
def Stored (cache : Cache.State Key) (value : Value) : Prop := Recorded cache value.payload value.identity

/-- A complete recorded value also retains coherent nontrivial ascending records. -/
def Ready (cache : Cache.State Key) (value : Value) : Prop := Stored cache value ∧ SourceEqualityDescend.WellFormed value.payload

/-- Canonical table growth retains the original complete physical value. -/
theorem Ready.grows (ready : Ready before value) (growth : Cache.Extends before.table after.table) : Ready after value :=
  ⟨ready.1.grows growth, ready.2⟩

/-- Intern the live payload or retain the contradiction tag without allocation. -/
def intern (payload : SourceEqualityPrecheck.Constraint) (before : Cache.State Key) : Value × Cache.State Key :=
  match payload with
  | none => (.contradiction, before)
  | some records =>
      let built := Cache.intern before (key records)
      (.live built.1.identity records, built.2)

/-- Interning retains the literal complete payload, including ordered metadata. -/
theorem intern_payload (payload : SourceEqualityPrecheck.Constraint) (before : Cache.State Key) :
    (intern payload before).1.payload = payload := by cases payload <;> rfl

/-- A sequential interner call is a permitted reserve/install trace or a read-only hit. -/
theorem cache_intern_steps (before : Cache.State Key) (key : Key) : Cache.Steps before (Cache.intern before key).2 := by
  cases found : before.table key with
  | some entry => simpa only [Cache.intern, found] using Cache.Steps.refl before
  | none =>
      have reserved : Cache.Steps before (Cache.reserve before key).2 :=
        .next (.refl before) (.reserve before key)
      have installed := Cache.Steps.next reserved
        (Cache.Step.install (Cache.reserve before key).2 (Cache.reserve before key).1 (Cache.reserve_issued before key))
      simpa only [Cache.intern, found] using installed

/-- Actual payload interning retains its complete abstract atomic allocation receipt. -/
theorem intern_steps (payload : SourceEqualityPrecheck.Constraint) (before : Cache.State Key) :
    Cache.Steps before (intern payload before).2 := by
  cases payload with
  | none => exact .refl before
  | some records => exact cache_intern_steps before (key records)

/-- Actual allocation preserves valid storage and records the exact returned value. -/
theorem intern_valid (payload : SourceEqualityPrecheck.Constraint) (before : Cache.State Key) (valid : Cache.Valid before) :
    Cache.Valid (intern payload before).2 ∧ Stored (intern payload before).2 (intern payload before).1 := by
  cases payload with
  | none => exact ⟨valid, trivial⟩
  | some records =>
      have checked := Cache.intern_correct before (key records) valid
      exact ⟨checked.1, (Cache.intern before (key records)).1, checked.2.1, rfl⟩

/-- Interning a well-formed complete payload derives the full ready-value invariant. -/
theorem intern_ready (payload : SourceEqualityPrecheck.Constraint) (before : Cache.State Key) (valid : Cache.Valid before)
    (wellFormed : SourceEqualityDescend.WellFormed payload) : Ready (intern payload before).2 (intern payload before).1 := by
  refine ⟨(intern_valid payload before valid).2, ?_⟩
  rw [intern_payload]
  exact wellFormed

/-- Actual allocation retains every earlier canonical value through its atomic trace. -/
theorem intern_growth (payload : SourceEqualityPrecheck.Constraint) (before : Cache.State Key) :
    Cache.Extends before.table (intern payload before).2.table := Cache.steps_table_extends (intern_steps payload before)

/-- Successful physical readback retains the literal normalized class lists. -/
theorem read_classes (equalities : Option EqualityNormalize.Constraints)
    (cached : SourceEqualityGuardReadback.Cached equalities) (payload : SourceEqualityPrecheck.Constraint)
    (read : SourceEqualityPhysicalPayload.read equalities = .ok payload) :
    SourceEqualityInheritedPayload.classes payload = equalities := by
  cases equalities with
  | none =>
      have same : payload = none := by simpa only [SourceEqualityPhysicalPayload.read, Except.ok.injEq] using read.symm
      rw [same]
      rfl
  | some classes =>
      obtain ⟨records, built, _, paths⟩ := SourceEqualityPhysicalPayload.normal_records classes (cached classes rfl)
      have same : payload = some records := by simpa only [SourceEqualityPhysicalPayload.read, built, Except.ok.injEq] using read.symm
      rw [same]
      exact congrArg some paths

/-- Construct a cached source equality field and intern its complete physical output. -/
def construct (equalities : Option EqualityNormalize.Constraints) (before : Cache.State Key) : Except String Value × Cache.State Key :=
  match SourceEqualityPhysicalPayload.read equalities with
  | .error message => (.error message, before)
  | .ok payload =>
      let built := intern payload before
      (.ok built.1, built.2)

/-- An original normalized field derives its ready value and literal source constructor receipt. -/
theorem construct_complete (equalities : Option EqualityNormalize.Constraints)
    (cached : SourceEqualityGuardReadback.Cached equalities) (before : Cache.State Key) (valid : Cache.Valid before) :
    ∃ value after, construct equalities before = (.ok value, after) ∧ Cache.Valid after ∧ Ready after value ∧
      Cache.Steps before after ∧ SourceEqualityPhysicalPayload.read equalities = .ok value.payload ∧
      SourceEqualityInheritedPayload.classes value.payload = equalities := by
  obtain ⟨payload, read, wellFormed, _⟩ := SourceEqualityInheritedPayload.read_complete (Symbol := Unit) equalities cached
  refine ⟨(intern payload before).1, (intern payload before).2, ?_,
    (intern_valid payload before valid).1, intern_ready payload before valid wellFormed, intern_steps payload before, ?_, ?_⟩
  · simp only [construct, read]
  · rw [intern_payload]
    exact read
  · rw [intern_payload]
    exact read_classes equalities cached payload read

/-- Demand one source normalization constructor and intern its completed live output. -/
noncomputable def normalize (paths : EqualityNormalize.Constraints) (before : Cache.State Key) : Except String Value × Cache.State Key :=
  construct (SourceCompactGuards.normalize paths) before

/-- Actual source normalization derives completion, literal class readback, and atomic allocation receipts. -/
theorem normalize_complete (paths : EqualityNormalize.Constraints) (before : Cache.State Key) (valid : Cache.Valid before) :
    ∃ value after, normalize paths before = (.ok value, after) ∧ Cache.Valid after ∧ Ready after value ∧
      Cache.Steps before after ∧ SourceEqualityInheritedPayload.classes value.payload = SourceCompactGuards.normalize paths := by
  obtain ⟨payload, read, wellFormed, _⟩ := SourceEqualityInheritedPayload.read_complete (Symbol := Unit)
    (SourceCompactGuards.normalize paths) (SourceEqualityGuardReadback.normalize_cached paths)
  refine ⟨(intern payload before).1, (intern payload before).2, ?_,
    (intern_valid payload before valid).1, intern_ready payload before valid wellFormed, intern_steps payload before, ?_⟩
  · simp only [normalize, construct, read]
  · rw [intern_payload]
    exact read_classes _ (SourceEqualityGuardReadback.normalize_cached paths) payload read

end MicroCFTA.SourceEqualityConstraintAllocation
