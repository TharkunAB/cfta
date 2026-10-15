import MicroCFTA.SourceEqualityPartialConstraintRenaming
import MicroCFTA.SourceEqualityPartialMemoSound

/-!
# Result-memo publication under physical constraint identity renaming

Corresponding published keys retain the same logical result handle. Cells
retain the same complete requests, phases, and values. Constraint allocation
histories can grow independently. Lookup and demand observe the same thunk
without requiring equal numeric constraint identities.
-/
namespace MicroCFTA.SourceEqualityPartialMemoRenaming
open Cache SourceEqualityPartialMemoWorker SourceEqualityPartialMemoFrame
open SourceEqualityPartialConstraintRenaming
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {first second : Tables}

/-- Both physical publication tables identify the same complete logical cells. -/
structure Related (first second : Tables) : Prop where
  cells : first.memo.cells = second.memo.cells
  next : first.memo.next = second.memo.next
  forward : ∀ key handle, first.memo.table key = some handle →
    ∃ other, KeyLinked first.constraints second.constraints key other ∧ second.memo.table other = some handle
  backward : ∀ key handle, second.memo.table key = some handle →
    ∃ other, KeyLinked first.constraints second.constraints other key ∧ first.memo.table other = some handle

/-- Empty result tables correspond for any two constraint allocation histories. -/
theorem related_empty (first second : Cache.State SourceEqualityPartialConstraintKey.Key) :
    Related ⟨first, FlatMemoThunk.empty⟩ ⟨second, FlatMemoThunk.empty⟩ := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro key handle impossible <;> cases impossible

/-- Independent constraint allocation retains every existing publication correspondence. -/
theorem Related.grows (related : Related first second)
    (firstGrowth : Extends first.constraints.table firstCache.table)
    (secondGrowth : Extends second.constraints.table secondCache.table) :
    Related ⟨firstCache, first.memo⟩ ⟨secondCache, second.memo⟩ := by
  refine ⟨related.cells, related.next, ?_, ?_⟩
  · intro key handle stored
    obtain ⟨other, linked, present⟩ := related.forward key handle stored
    exact ⟨other, ⟨linked.1.grows firstGrowth secondGrowth, linked.2⟩, present⟩
  · intro key handle stored
    obtain ⟨other, linked, present⟩ := related.backward key handle stored
    exact ⟨other, ⟨linked.1.grows firstGrowth secondGrowth, linked.2⟩, present⟩

/-- Corresponding physical publications derive the second table's complete original-request validity. -/
theorem Related.valid (related : Related first second) (firstValid : Valid first)
    (secondValid : Cache.Valid second.constraints) : Valid second := by
  refine ⟨secondValid, ?_, ?_, ?_⟩
  · intro handle cell stored
    have earlier : first.memo.cells handle = some cell := related.cells ▸ stored
    have bound := firstValid.2.bounded handle cell earlier
    simpa only [related.next] using bound
  · intro key handle stored
    obtain ⟨other, linked, present⟩ := related.backward key handle stored
    obtain ⟨cell, original, recorded⟩ := firstValid.2.linked other handle present
    exact ⟨cell, related.cells ▸ original,
      recorded_transport firstValid.1 cell.request.inherited other.1 key.1 recorded.1 linked.1,
      recorded.2.trans linked.2⟩
  · intros
    trivial

/-- Physical identity renaming and actual native heap preservation transport every completed-cell proof. -/
theorem Related.sound (firstState secondState : SourceEqualityPartialMemoWorker.State width)
    (related : Related (stateTables firstState) (stateTables secondState))
    (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient firstState)
    (secondValid : Cache.Valid secondState.constraints)
    (keeps : SourceEqualityRequiredCache.Keeps firstState.native.machine.heap secondState.native.machine.heap) :
    SourceEqualityPartialMemoSound.Sound holds ambient secondState := by
  refine ⟨related.valid sound.valid secondValid, ?_⟩
  intro handle cell stored
  have earlier : firstState.memo.cells handle = some cell := related.cells ▸ stored
  exact (sound.cells handle cell earlier).keeps holds ambient keeps

/-- Corresponding actual candidate keys observe exactly the same published handle or miss. -/
theorem Related.lookup_eq (related : Related first second)
    (firstValid : Cache.Valid first.constraints) (secondValid : Cache.Valid second.constraints)
    (linked : KeyLinked first.constraints second.constraints left right) : first.memo.table left = second.memo.table right := by
  cases found : first.memo.table left with
  | some handle =>
      obtain ⟨other, pair, stored⟩ := related.forward left handle found
      have same : right = other := (key_eq_iff firstValid secondValid linked pair).mp rfl
      exact same ▸ stored.symm
  | none =>
      cases stored : second.memo.table right with
      | none => rfl
      | some handle =>
          obtain ⟨other, pair, present⟩ := related.backward right handle stored
          have same : left = other := (key_eq_iff firstValid secondValid linked pair).mpr rfl
          rw [← same, found] at present
          cases present

/-- Actual miss publication preserves both directions of the physical publication relation. -/
private theorem publish (related : Related first second)
    (firstValid : Cache.Valid first.constraints) (secondValid : Cache.Valid second.constraints)
    (linked : KeyLinked first.constraints second.constraints left right) (request : Request)
    (firstMissing : first.memo.table left = none) (secondMissing : second.memo.table right = none) :
    Related ⟨first.constraints, (FlatMemoThunk.lookupOrInsert left request first.memo).2⟩
      ⟨second.constraints, (FlatMemoThunk.lookupOrInsert right request second.memo).2⟩ := by
  simp only [FlatMemoThunk.lookupOrInsert, firstMissing, secondMissing]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [related.cells, related.next]
  · dsimp only
    rw [related.next]
  · intro key handle stored
    by_cases same : key = left
    · subst key
      have value : first.memo.next = handle := by simpa [put] using stored
      exact ⟨right, linked, by simp [put, ← related.next, value]⟩
    · have old : first.memo.table key = some handle := by simpa [put, same] using stored
      obtain ⟨other, pair, present⟩ := related.forward key handle old
      have different : other ≠ right := by
        intro equal
        exact same ((key_eq_iff firstValid secondValid pair linked).mpr equal)
      exact ⟨other, pair, by simpa [put, different] using present⟩
  · intro key handle stored
    by_cases same : key = right
    · subst key
      have value : second.memo.next = handle := by simpa [put] using stored
      exact ⟨left, linked, by simp [put, related.next, value]⟩
    · have old : second.memo.table key = some handle := by simpa [put, same] using stored
      obtain ⟨other, pair, present⟩ := related.backward key handle old
      have different : other ≠ left := by
        intro equal
        exact same ((key_eq_iff firstValid secondValid pair linked).mp equal)
      exact ⟨other, pair, by simpa [put, different] using present⟩

/-- Actual hit or miss lookup returns the same handle and preserves corresponding result tables. -/
theorem Related.lookup (related : Related first second)
    (firstValid : Cache.Valid first.constraints) (secondValid : Cache.Valid second.constraints)
    (linked : KeyLinked first.constraints second.constraints left right) (request : Request) :
    (FlatMemoThunk.lookupOrInsert left request first.memo).1 = (FlatMemoThunk.lookupOrInsert right request second.memo).1 ∧
    Related ⟨first.constraints, (FlatMemoThunk.lookupOrInsert left request first.memo).2⟩
      ⟨second.constraints, (FlatMemoThunk.lookupOrInsert right request second.memo).2⟩ := by
  have equal := related.lookup_eq firstValid secondValid linked
  cases found : first.memo.table left with
  | some handle =>
      have stored : second.memo.table right = some handle := equal ▸ found
      simpa only [FlatMemoThunk.lookupOrInsert, found, stored] using
        (show handle = handle ∧ Related first second from ⟨rfl, related⟩)
  | none =>
      have missing : second.memo.table right = none := equal ▸ found
      exact ⟨by simpa only [FlatMemoThunk.lookupOrInsert, found, missing] using related.next,
        publish related firstValid secondValid linked request found missing⟩

/-- Actual preparation and publication preserve handles across independent constraint tables. -/
theorem prepare_publish (request : Request) (firstState secondState : SourceEqualityPartialMemoWorker.State width)
    (related : Related (stateTables firstState) (stateTables secondState))
    (firstValid : Valid (stateTables firstState)) (secondValid : Valid (stateTables secondState)) :
    let firstPrepared := prepare request firstState
    let secondPrepared := prepare request secondState
    let firstLookup := FlatMemoThunk.lookupOrInsert firstPrepared.1 request firstPrepared.2.memo
    let secondLookup := FlatMemoThunk.lookupOrInsert secondPrepared.1 request secondPrepared.2.memo
    firstLookup.1 = secondLookup.1 ∧
      Related ⟨firstPrepared.2.constraints, firstLookup.2⟩ ⟨secondPrepared.2.constraints, secondLookup.2⟩ := by
  have firstFrame := prepare_frame request firstState firstValid
  have secondFrame := prepare_frame request secondState secondValid
  have prepared := related.grows firstFrame.constraints secondFrame.constraints
  exact prepared.lookup firstFrame.valid.1 secondFrame.valid.1
    (SourceEqualityPartialConstraintRenaming.prepare_linked request firstState secondState firstValid.1 secondValid.1) request

/-- Equal logical cells retain their correspondence after the same actual phase update. -/
theorem Related.setStatus (related : Related first second) (handle : Nat) (status : FlatMemoThunk.Status (InternedConstructorTemplates.Value Symbol Guard)) :
    Related ⟨first.constraints, FlatMemoThunk.setStatus handle status first.memo⟩
      ⟨second.constraints, FlatMemoThunk.setStatus handle status second.memo⟩ := by
  cases found : first.memo.cells handle with
  | none => simpa only [FlatMemoThunk.setStatus, found, ← related.cells] using related
  | some cell =>
      simp only [FlatMemoThunk.setStatus, found, ← related.cells]
      exact ⟨rfl, related.next, related.forward, related.backward⟩

/-- Actual demand observes the same absent, original evaluate, busy, or complete value branch. -/
theorem Related.demand (related : Related first second) (handle : Nat) :
    (FlatMemoThunk.demand handle first.memo).1 = (FlatMemoThunk.demand handle second.memo).1 ∧
    Related ⟨first.constraints, (FlatMemoThunk.demand handle first.memo).2⟩
      ⟨second.constraints, (FlatMemoThunk.demand handle second.memo).2⟩ := by
  cases found : first.memo.cells handle with
  | none =>
      simpa only [FlatMemoThunk.demand, found, ← related.cells] using
        (show (FlatMemoThunk.Observation.absent : FlatMemoThunk.Observation Request (InternedConstructorTemplates.Value Symbol Guard)) = .absent ∧ Related first second from ⟨rfl, related⟩)
  | some cell =>
      cases cell with
      | mk request status =>
          cases status <;> simp only [FlatMemoThunk.demand, found, ← related.cells]
          · exact ⟨trivial, related.setStatus handle .evaluating⟩
          · exact ⟨trivial, related⟩
          · exact ⟨trivial, related⟩

/-- Actual completion retains the same original request and full returned value in both tables. -/
theorem Related.finish (related : Related first second) (handle : Nat) (value : InternedConstructorTemplates.Value Symbol Guard) :
    Related ⟨first.constraints, FlatMemoThunk.finish handle value first.memo⟩
      ⟨second.constraints, FlatMemoThunk.finish handle value second.memo⟩ := by
  cases found : first.memo.cells handle with
  | none => simpa only [FlatMemoThunk.finish, found, ← related.cells] using related
  | some cell =>
      cases cell with
      | mk request status =>
          cases status <;> simp only [FlatMemoThunk.finish, found, ← related.cells]
          · exact related
          · exact related.setStatus handle (.returned value)
          · exact related

end MicroCFTA.SourceEqualityPartialMemoRenaming
