import MicroCFTA.SourceEqualityConstraintFieldLookup
import MicroCFTA.SourceEqualityConstraintOrigins

/-!
# Original field allocation retained through source construction

Each literal field carries an earlier successful constructor receipt.
The current interner retains that constructor's entries. Actual graph
construction preserves the receipt at every resident edge. Read-only
lookup then returns the original value without allocating at the request.
GHC execution must still supply the original allocation inventory.
-/
namespace MicroCFTA.SourceEqualityOriginalFieldOrigins
open InternedConstructorTemplates InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open SourceEqualityConstraintAllocation
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "SourceConstraint" => SourceSymbolicIndex.Constraint
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint

/-- An earlier actual constructor returned a value whose entries remain in the current interner. -/
def Origin (current : Cache.State Key) (original : SourceConstraint Formula) : Prop :=
  ∃ before value after, Cache.Valid before ∧
    construct original.equalities before = (.ok value, after) ∧
    Cache.Extends after.table current.table

/-- A successful original constructor establishes its own allocation origin. -/
theorem of_construct (original : SourceConstraint Formula)
    (before : Cache.State Key) (valid : Cache.Valid before) (value : Value) (after : Cache.State Key)
    (done : construct original.equalities before = (.ok value, after)) : Origin after original :=
  ⟨before, value, after, valid, done, Cache.extends_refl _⟩

/-- Later canonical cache growth retains the same earlier constructor receipt. -/
theorem Origin.grows (origin : Origin before original) (growth : Cache.Extends before.table after.table) :
    Origin after original := by
  obtain ⟨initial, value, final, valid, done, retained⟩ := origin
  exact ⟨initial, value, final, valid, done, Cache.extends_trans retained growth⟩

/-- Original allocation provenance derives exact read-only lookup and physical readback. -/
theorem Origin.load (original : SourceConstraint Formula) (cache : Cache.State Key)
    (cached : SourceEqualityGuardReadback.Cached original.equalities) (origin : Origin cache original) :
    ∃ value : Allocated Formula, SourceEqualityConstraintFieldLookup.load original cache = .ok (some value) ∧
      SourceEqualityConjoinAllocation.readback value = original ∧ Ready cache value.stored ∧
      SourceEqualityPhysicalPayload.read original.equalities = .ok value.stored.payload := by
  obtain ⟨before, stored, after, valid, done, growth⟩ := origin
  obtain ⟨loaded, readback, ready⟩ :=
    SourceEqualityConstraintFieldLookup.load_of_construct_grows original cached before valid stored after cache done growth
  exact ⟨⟨stored, original.guard⟩, loaded, readback, ready,
    SourceEqualityConstraintFieldLookup.load_constructor_receipt original cache cached _ loaded⟩

/-- Actual original construction retains every literal allocation origin at its resident edge key. -/
theorem constructed [DecidableEq (EdgeKey Symbol (SourceConstraint Formula))]
    (cache : Cache.State Key) (expression : Syntax Symbol (SourceConstraint Formula))
    (origins : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, Origin cache original)
    (value : InternedConstructorTemplates.Value Symbol (SourceConstraint Formula))
    (heap : State Symbol (SourceConstraint Formula))
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    SourceEqualityAnnotationHeap.Heap (Origin cache) heap := by
  have allowed := SourceEqualityConstraintOrigins.allowed (Origin cache) expression origins
  simpa only [built, Outcome.state] using SourceEqualityAnnotationConstruction.build
    (Origin cache) expression allowed [] empty (SourceEqualityAnnotationHeap.empty_heap _)

/-- Every actual resident original edge has its earlier allocated field in current canonical storage. -/
theorem resident_lookup [DecidableEq (EdgeKey Symbol (SourceConstraint Formula))]
    (cache : Cache.State Key) (expression : Syntax Symbol (SourceConstraint Formula))
    (origins : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, Origin cache original)
    (value : InternedConstructorTemplates.Value Symbol (SourceConstraint Formula))
    (heap : State Symbol (SourceConstraint Formula))
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (edge : EdgeValue Symbol (SourceConstraint Formula)) (resident : EdgeResident heap edge)
    (cached : SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities) :
    ∃ loaded : Allocated Formula,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint cache = .ok (some loaded) ∧
      SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧ Ready cache loaded.stored ∧
      SourceEqualityPhysicalPayload.read edge.entry.key.constraint.equalities = .ok loaded.stored.payload :=
  Origin.load edge.entry.key.constraint cache cached
    (constructed cache expression origins value heap built edge.entry.key edge resident)

end MicroCFTA.SourceEqualityOriginalFieldOrigins
