import MicroCFTA.SourceEqualityConstraintAllocation
import MicroCFTA.SourceEqualityPartialMemoRenaming
import MicroCFTA.SourceEqualityPartialMemoReuse

/-!
# Actual constraint allocation effects in recursive result-memo state

Constraint constructors can allocate keys that never become outer requests.
Their atomic interner receipts preserve all original result cells and their
current semantic proofs. Source allocations can precede a corresponding
request without changing publication handles. Already stored inherited
values require no additional allocation at request preparation.
-/
namespace MicroCFTA.SourceEqualityPartialAllocationFrame
open Cache SourceEqualityPartialMemoWorker SourceEqualityPartialMemoFrame
open SourceEqualityConstraintAllocation
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Actual interner steps retain all original result requests and returned values. -/
theorem steps_frame (before : SourceEqualityPartialMemoWorker.State width)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (valid : Valid (stateTables before)) (steps : Cache.Steps before.constraints cache) :
    Frame (stateTables before) (stateTables {before with constraints := cache}) := by
  have growth := Cache.steps_table_extends steps
  refine ⟨⟨Cache.steps_valid valid.1 steps, ?_⟩, growth, Cache.extends_refl _, .refl _, .refl _⟩
  exact valid.2.keyMap _ _ _ _ (key_grows growth)

/-- Actual interner effects preserve completed-cell soundness without a future semantic premise. -/
theorem steps_sound (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (before : SourceEqualityPartialMemoWorker.State width) (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient before) (steps : Cache.Steps before.constraints cache) :
    SourceEqualityPartialMemoSound.Sound holds ambient {before with constraints := cache} :=
  ⟨(steps_frame before cache sound.valid steps).valid, sound.cells⟩

/-- A complete physical payload constructor supplies its actual full-state frame receipt. -/
theorem intern_frame (payload : SourceEqualityPrecheck.Constraint) (before : SourceEqualityPartialMemoWorker.State width)
    (valid : Valid (stateTables before)) :
    Frame (stateTables before) (stateTables {before with constraints := (intern payload before.constraints).2}) :=
  steps_frame before _ valid (intern_steps payload before.constraints)

/-- Original cell proofs survive actual payload construction and its output is ready for a source request. -/
theorem intern_sound (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (payload : SourceEqualityPrecheck.Constraint) (before : SourceEqualityPartialMemoWorker.State width)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient before)
    (wellFormed : SourceEqualityDescend.WellFormed payload) :
    SourceEqualityPartialMemoSound.Sound holds ambient {before with constraints := (intern payload before.constraints).2} ∧
      Ready (intern payload before.constraints).2 (intern payload before.constraints).1 :=
  ⟨steps_sound holds ambient before _ sound (intern_steps payload before.constraints),
    intern_ready payload before.constraints sound.valid.1 wellFormed⟩

/-- A source inherited value already has its physical identity before result-memo lookup. -/
theorem prepare_stored (inherited : SourceEqualityConstraintAllocation.Value)
    (value : InternedConstructorTemplates.Value Symbol Guard) (before : SourceEqualityPartialMemoWorker.State width)
    (stored : Stored before.constraints inherited) :
    prepare ⟨inherited.payload, value⟩ before = ((inherited.identity, value.referenceOf), before) :=
  SourceEqualityPartialMemoReuse.prepare_linked ⟨inherited.payload, value⟩ before _ ⟨stored, rfl⟩

/-- Extra actual source allocations before a request preserve corresponding publication handles and cells. -/
theorem prepare_after_source_allocations (request : Request) (model source : SourceEqualityPartialMemoWorker.State width)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (related : SourceEqualityPartialMemoRenaming.Related (stateTables model) (stateTables source))
    (modelValid : Valid (stateTables model)) (sourceValid : Valid (stateTables source))
    (steps : Cache.Steps source.constraints cache) :
    let firstPrepared := prepare request model
    let secondPrepared := prepare request {source with constraints := cache}
    let firstLookup := FlatMemoThunk.lookupOrInsert firstPrepared.1 request firstPrepared.2.memo
    let secondLookup := FlatMemoThunk.lookupOrInsert secondPrepared.1 request secondPrepared.2.memo
    firstLookup.1 = secondLookup.1 ∧
      SourceEqualityPartialMemoRenaming.Related ⟨firstPrepared.2.constraints, firstLookup.2⟩
        ⟨secondPrepared.2.constraints, secondLookup.2⟩ := by
  have frame := steps_frame source cache sourceValid steps
  have retained := related.grows (Cache.extends_refl _) frame.constraints
  exact SourceEqualityPartialMemoRenaming.prepare_publish request model {source with constraints := cache}
    retained modelValid frame.valid

end MicroCFTA.SourceEqualityPartialAllocationFrame
