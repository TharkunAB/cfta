import MicroCFTA.SourceEqualityPartialMemoFrame

/-!
# Semantic provenance of partial-reduction result cells

Every phase retains an available closed original request and a well-formed
inherited payload. A returned phase also retains its actual result and the
immutable language law. Table validity supplies the exact physical key link.
These preservation laws do not assume a native Scope or an outer caller law.
-/
namespace MicroCFTA.SourceEqualityPartialMemoSound
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialMemoWorker
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

/-- One completed request narrows unconditionally and is exact under inherited satisfaction. -/
def MeaningLaw (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (request : Request) (result : Value Symbol Guard) : Prop :=
  ∀ term,
    (InternedGuardedLanguage.meaning holds ambient result term →
      InternedGuardedLanguage.meaning holds ambient request.value term) ∧
    (SourceEqualityPrecheck.Sat term request.inherited →
      (InternedGuardedLanguage.meaning holds ambient result term ↔
        InternedGuardedLanguage.meaning holds ambient request.value term))

/-- All cells retain their original request; returned cells also retain the proved result. -/
def CellGood (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (heap : InternedConstructorTemplates.State Symbol Guard)
    (cell : FlatMemoThunk.Cell Request (Value Symbol Guard)) : Prop :=
  Available heap cell.request.value ∧ cell.request.value.free = [] ∧
    SourceEqualityDescend.WellFormed cell.request.inherited ∧
    match cell.status with
    | .returned result => Available heap result ∧ result.free = [] ∧ MeaningLaw holds ambient cell.request result
    | .suspended | .evaluating => True

/-- Actual table validity and every stored cell retain their separate provenance facts. -/
structure Sound (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (state : SourceEqualityPartialMemoWorker.State width) : Prop where
  valid : SourceEqualityPartialMemoFrame.Valid (SourceEqualityPartialMemoFrame.stateTables state)
  cells : ∀ handle cell, state.memo.cells handle = some cell → CellGood holds ambient state.native.machine.heap cell

variable (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)

/-- The empty initial memo needs no supplied request or result fact. -/
theorem initial_sound (native : NativeState width Symbol Guard) : Sound holds ambient (initial native) := by
  refine ⟨SourceEqualityPartialMemoFrame.initial_valid native, ?_⟩
  intro handle cell impossible
  cases impossible

/-- Actual heap preservation retains every immutable request and returned-result fact. -/
theorem CellGood.keeps {before after : InternedConstructorTemplates.State Symbol Guard}
    {cell : FlatMemoThunk.Cell Request (Value Symbol Guard)}
    (good : CellGood holds ambient before cell) (keeps : SourceEqualityRequiredCache.Keeps before after) :
    CellGood holds ambient after cell := by
  refine ⟨keeps.available _ good.1, good.2.1, good.2.2.1, ?_⟩
  cases phase : cell.status with
  | suspended | evaluating => trivial
  | returned result =>
      have returned := good.2.2.2
      rw [phase] at returned
      exact ⟨keeps.available _ returned.1, returned.2⟩

/-- Unchanged memo tables and actual native heap preservation retain soundness. -/
theorem Sound.keeps {before after : SourceEqualityPartialMemoWorker.State width}
    (sound : Sound holds ambient before)
    (tables : SourceEqualityPartialMemoFrame.stateTables after = SourceEqualityPartialMemoFrame.stateTables before)
    (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap) :
    Sound holds ambient after := by
  refine ⟨?_, ?_⟩
  · rw [tables]
    exact sound.valid
  · intro handle cell stored
    have memoSame : after.memo = before.memo := congrArg SourceEqualityPartialMemoFrame.Tables.memo tables
    rw [memoSame] at stored
    exact (sound.cells handle cell stored).keeps holds ambient keeps

/-- Sound cells strengthen the existing exact key-linked memo validity predicate. -/
theorem Sound.memo_valid {state : SourceEqualityPartialMemoWorker.State width} (sound : Sound holds ambient state) :
    FlatMemoThunk.Valid (SourceEqualityPartialMemoFrame.KeyOf state.constraints)
      (CellGood holds ambient state.native.machine.heap) state.memo :=
  ⟨sound.valid.2.bounded, sound.valid.2.linked, sound.cells⟩

/-- Actual physical-key preparation preserves every request and result fact. -/
theorem prepare_sound (candidate : Request) (before : SourceEqualityPartialMemoWorker.State width)
    (sound : Sound holds ambient before) : Sound holds ambient (prepare candidate before).2 :=
  ⟨(SourceEqualityPartialMemoFrame.prepare_frame candidate before sound.valid).valid, sound.cells⟩

/-- Actual publication retains old cells and checks the newly suspended original request. -/
theorem lookup_sound (key : SourceEqualityPartialMemoWorker.Key) (candidate : Request)
    (before : SourceEqualityPartialMemoWorker.State width) (sound : Sound holds ambient before)
    (available : Available before.native.machine.heap candidate.value) (closed : candidate.value.free = [])
    (wellFormed : SourceEqualityDescend.WellFormed candidate.inherited)
    (recorded : SourceEqualityPartialMemoFrame.KeyOf before.constraints candidate key) :
    Sound holds ambient { before with memo := (FlatMemoThunk.lookupOrInsert key candidate before.memo).2 } := by
  have suspended : CellGood holds ambient before.native.machine.heap ⟨candidate, .suspended⟩ :=
    ⟨available, closed, wellFormed, trivial⟩
  have checked := FlatMemoThunk.lookup_valid key candidate before.memo _ _
    (sound.memo_valid holds ambient) recorded suspended
  exact ⟨(SourceEqualityPartialMemoFrame.lookup_frame key candidate
    (SourceEqualityPartialMemoFrame.stateTables before) sound.valid recorded).valid, checked.checked⟩

/-- Demand preserves original requests and does not require a result law before completion. -/
theorem demand_sound (handle : Nat) (before : SourceEqualityPartialMemoWorker.State width)
    (sound : Sound holds ambient before) :
    Sound holds ambient { before with memo := (FlatMemoThunk.demand handle before.memo).2 } := by
  refine ⟨(SourceEqualityPartialMemoFrame.demand_frame handle
    (SourceEqualityPartialMemoFrame.stateTables before) sound.valid).valid, ?_⟩
  cases stored : before.memo.cells handle with
  | none => simpa only [FlatMemoThunk.demand, stored] using sound.cells
  | some cell =>
      cases cell with
      | mk request status =>
          cases status with
          | evaluating | returned result => simpa only [FlatMemoThunk.demand, stored] using sound.cells
          | suspended =>
              have original := sound.cells handle ⟨request, .suspended⟩ stored
              have changed : CellGood holds ambient before.native.machine.heap ⟨request, .evaluating⟩ :=
                ⟨original.1, original.2.1, original.2.2.1, trivial⟩
              have checked := FlatMemoThunk.setStatus_valid handle .evaluating before.memo _ _
                (sound.memo_valid holds ambient) ⟨request, .suspended⟩ stored changed
              simpa only [FlatMemoThunk.demand, stored] using checked.checked

/-- Completing the actually stored evaluating request installs its proved actual result. -/
theorem finish_sound (handle : Nat) (original : Request) (result : Value Symbol Guard)
    (before : SourceEqualityPartialMemoWorker.State width) (sound : Sound holds ambient before)
    (running : before.memo.cells handle = some ⟨original, .evaluating⟩)
    (available : Available before.native.machine.heap result) (closed : result.free = [])
    (meaning : MeaningLaw holds ambient original result) :
    Sound holds ambient { before with memo := FlatMemoThunk.finish handle result before.memo } := by
  have requestGood := sound.cells handle ⟨original, .evaluating⟩ running
  have changed : CellGood holds ambient before.native.machine.heap ⟨original, .returned result⟩ :=
    ⟨requestGood.1, requestGood.2.1, requestGood.2.2.1, available, closed, meaning⟩
  have checked := FlatMemoThunk.setStatus_valid handle (.returned result) before.memo _ _
    (sound.memo_valid holds ambient) ⟨original, .evaluating⟩ running changed
  refine ⟨⟨sound.valid.1, FlatMemoThunk.finish_valid handle result before.memo _ sound.valid.2⟩, ?_⟩
  simpa only [FlatMemoThunk.finish, running] using checked.checked

end MicroCFTA.SourceEqualityPartialMemoSound
