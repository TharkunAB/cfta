import MicroCFTA.SourceEqualityConjoinAllocation

/-!
# Read-only lookup of original physical constraint fields

The native request reads an already constructed stored field. It does not
intern that field again. A missing live key records unavailable model
representation. Malformed physical readback retains its original error.
-/
namespace MicroCFTA.SourceEqualityConstraintFieldLookup
open SourceEqualityConstraintAllocation
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint
local notation "SourceConstraint" => SourceSymbolicIndex.Constraint

/-- Read an original raw field from existing canonical storage without any allocation. -/
def load (original : SourceConstraint Formula) (cache : Cache.State Key) : Except String (Option (Allocated Formula)) :=
  match SourceEqualityPhysicalPayload.read original.equalities with
  | .error message => .error message
  | .ok none => .ok (some ⟨.contradiction, original.guard⟩)
  | .ok (some records) => match cache.table (SourceEqualityPartialConstraintKey.key records) with
    | none => .ok none
    | some entry => .ok (some ⟨.live entry.identity records, original.guard⟩)

/-- Malformed physical readback retains its checked source error. -/
theorem load_error (original : SourceConstraint Formula) (cache : Cache.State Key) (message : String)
    (failed : SourceEqualityPhysicalPayload.read original.equalities = .error message) :
    load original cache = .error message := by simp only [load, failed]

/-- A missing live canonical key is unavailable representation, not a source error. -/
theorem load_missing (original : SourceConstraint Formula) (cache : Cache.State Key)
    (records : List SourceEqualityClassOrder.Record)
    (built : SourceEqualityPhysicalPayload.read original.equalities = .ok (some records))
    (absent : cache.table (SourceEqualityPartialConstraintKey.key records) = none) :
    load original cache = .ok none := by simp only [load, built, absent]

/-- An actual read receipt and existing canonical value determine the exact loaded physical value. -/
theorem load_of_stored (original : SourceConstraint Formula) (cache : Cache.State Key) (value : Value)
    (built : SourceEqualityPhysicalPayload.read original.equalities = .ok value.payload)
    (stored : Stored cache value) : load original cache = .ok (some ⟨value, original.guard⟩) := by
  cases value with
  | contradiction => simp only [load, built, Value.payload]
  | live identity records =>
      obtain ⟨entry, present, same⟩ := stored
      simp only [load, built, Value.payload, present, same]

private theorem original_readback (original : SourceConstraint Formula) (value : Value)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (built : SourceEqualityPhysicalPayload.read original.equalities = .ok value.payload) :
    SourceEqualityConjoinAllocation.readback (⟨value, original.guard⟩ : Allocated Formula) = original := by
  change (⟨SourceEqualityInheritedPayload.classes value.payload, original.guard⟩ : SourceConstraint Formula) = original
  rw [read_classes original.equalities cached value.payload built]

/-- Existing constructor and ready-value receipts give exact original readback with no cache change. -/
theorem load_of_receipt (original : SourceConstraint Formula) (cache : Cache.State Key)
    (cached : SourceEqualityGuardReadback.Cached original.equalities) (value : Value)
    (built : SourceEqualityPhysicalPayload.read original.equalities = .ok value.payload)
    (ready : Ready cache value) :
    load original cache = .ok (some ⟨value, original.guard⟩) ∧
      SourceEqualityConjoinAllocation.readback (⟨value, original.guard⟩ : Allocated Formula) = original ∧
      Ready cache value :=
  ⟨load_of_stored original cache value built ready.1, original_readback original value cached built, ready⟩

private theorem load_properties (original : SourceConstraint Formula) (cache : Cache.State Key)
    (cached : SourceEqualityGuardReadback.Cached original.equalities) (value : Allocated Formula)
    (done : load original cache = .ok (some value)) :
    Ready cache value.stored ∧ SourceEqualityConjoinAllocation.readback value = original ∧
      SourceEqualityPhysicalPayload.read original.equalities = .ok value.stored.payload := by
  cases built : SourceEqualityPhysicalPayload.read original.equalities with
  | error message => simp only [load, built] at done; cases done
  | ok payload =>
      cases payload with
      | none =>
          have same : value = ⟨.contradiction, original.guard⟩ := by
            simpa only [load, built, Except.ok.injEq, Option.some.injEq] using done.symm
          subst value
          have ready : Ready cache .contradiction :=
            ⟨trivial, SourceEqualityInheritedPayload.read_wellFormed original.equalities cached none built⟩
          exact ⟨ready, original_readback original .contradiction cached built, rfl⟩
      | some records =>
          cases present : cache.table (SourceEqualityPartialConstraintKey.key records) with
          | none => simp only [load, built, present, Except.ok.injEq] at done; cases done
          | some entry =>
              have same : value = ⟨.live entry.identity records, original.guard⟩ := by
                simpa only [load, built, present, Except.ok.injEq, Option.some.injEq] using done.symm
              subst value
              have ready : Ready cache (.live entry.identity records) :=
                ⟨⟨entry, present, rfl⟩,
                  SourceEqualityInheritedPayload.read_wellFormed original.equalities cached (some records) built⟩
              exact ⟨ready, original_readback original _ cached built, rfl⟩

/-- A successful current field lookup derives readiness and exact original readback. -/
theorem load_ready (original : SourceConstraint Formula) (cache : Cache.State Key)
    (_valid : Cache.Valid cache) (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (value : Allocated Formula) (done : load original cache = .ok (some value)) :
    Ready cache value.stored ∧ SourceEqualityConjoinAllocation.readback value = original :=
  ⟨(load_properties original cache cached value done).1, (load_properties original cache cached value done).2.1⟩

/-- A successful current lookup retains the actual physical constructor receipt. -/
theorem load_constructor_receipt (original : SourceConstraint Formula) (cache : Cache.State Key)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (value : Allocated Formula) (done : load original cache = .ok (some value)) :
    SourceEqualityPhysicalPayload.read original.equalities = .ok value.stored.payload :=
  (load_properties original cache cached value done).2.2

/-- A successful original allocation supplies every lookup receipt without an assumed cached answer. -/
theorem load_of_construct (original : SourceConstraint Formula)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (before : Cache.State Key) (valid : Cache.Valid before) (value : Value) (after : Cache.State Key)
    (done : SourceEqualityConstraintAllocation.construct original.equalities before = (.ok value, after)) :
    load original after = .ok (some ⟨value, original.guard⟩) ∧
      SourceEqualityConjoinAllocation.readback (⟨value, original.guard⟩ : Allocated Formula) = original ∧
      Ready after value ∧ SourceEqualityPhysicalPayload.read original.equalities = .ok value.payload ∧ Cache.Valid after := by
  obtain ⟨actual, cache, completed, afterValid, ready, _, built, _⟩ :=
    SourceEqualityConstraintAllocation.construct_complete original.equalities cached before valid
  have pair := Prod.mk.inj (completed.symm.trans done)
  have same : actual = value := Except.ok.inj pair.1
  have sameCache : cache = after := pair.2
  subst actual
  subst cache
  obtain ⟨loaded, readback, _⟩ := load_of_receipt original after cached value built ready
  exact ⟨loaded, readback, ready, built, afterValid⟩

/-- Later canonical cache growth retains lookup of the actual original constructor value. -/
theorem load_of_construct_grows (original : SourceConstraint Formula)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (before : Cache.State Key) (valid : Cache.Valid before) (value : Value) (after current : Cache.State Key)
    (done : SourceEqualityConstraintAllocation.construct original.equalities before = (.ok value, after))
    (growth : Cache.Extends after.table current.table) :
    load original current = .ok (some ⟨value, original.guard⟩) ∧
      SourceEqualityConjoinAllocation.readback (⟨value, original.guard⟩ : Allocated Formula) = original ∧ Ready current value := by
  obtain ⟨_, _, ready, built, _⟩ := load_of_construct original cached before valid value after done
  exact load_of_receipt original current cached value built (ready.grows growth)

end MicroCFTA.SourceEqualityConstraintFieldLookup
