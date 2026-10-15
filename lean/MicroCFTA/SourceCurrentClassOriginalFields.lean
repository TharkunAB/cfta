import MicroCFTA.SourceEqualityOriginalFieldOrigins
import MicroCFTA.SourceCurrentClassConstructionEntry

/-!
# Original allocated fields at current cold class entry

Original graph construction derives native readiness and normalized fields.
Earlier literal allocation receipts derive successful read-only lookup for
every resident original edge. The equality interner is not reset. Original
allocation scheduling and later inherited storage remain separate.
-/
namespace MicroCFTA.SourceCurrentClassOriginalFields
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped SourceEqualityNativeInitial
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula

/-- Actual original construction and earlier allocation receipts derive all initial fields and lookup results. -/
theorem constructed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression)
    (cache : Cache.State Key)
    (origins : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityOriginalFieldOrigins.Origin cache original)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    IdleReady top conjoin (cold width heap) ∧ CostHeap heap ∧ FieldHeap heap ∧
      Available heap value ∧ value.free = [] ∧
      ∀ edge, EdgeResident heap edge → Values heap edge.children ∧
        ∃ loaded : Allocated,
          SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint cache = .ok (some loaded) ∧
          SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
          SourceEqualityConstraintAllocation.Ready cache loaded.stored ∧
          SourceEqualityPhysicalPayload.read edge.entry.key.constraint.equalities = .ok loaded.stored.payload := by
  obtain ⟨ready, costs, fields, available, closed, edges⟩ :=
    SourceCurrentClassInitial.constructed width expression allowed value heap built
  refine ⟨ready, costs, fields, available, closed, ?_⟩
  intro edge resident
  have input := edges edge resident
  exact ⟨input.1, SourceEqualityOriginalFieldOrigins.resident_lookup cache expression origins value heap built
    edge resident input.2⟩

/-- A finite closed source build derives current cold entry with every original allocated field available. -/
theorem closed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression)
    (cache : Cache.State Key)
    (origins : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityOriginalFieldOrigins.Origin cache original) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      IdleReady top conjoin (cold width heap) ∧ CostHeap heap ∧ FieldHeap heap ∧
        Available heap value ∧ value.free = [] ∧
        ∀ edge, EdgeResident heap edge → Values heap edge.children ∧
          ∃ loaded : Allocated,
            SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint cache = .ok (some loaded) ∧
            SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
            SourceEqualityConstraintAllocation.Ready cache loaded.stored ∧
            SourceEqualityPhysicalPayload.read edge.entry.key.constraint.equalities = .ok loaded.stored.payload := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  exact ⟨value, heap, built, constructed width expression allowed cache origins value heap built⟩

/-- Original allocation history supplies the loaded value before any actual live prefix and completed scan. -/
theorem cold_scan_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (origins : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityOriginalFieldOrigins.Origin operations.constraints original)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Language.Term Symbol)
    (accepted : InternedGuardedLanguage.edgeMeaning (SourceSymbolicIndex.acceptsConstraint formulas solver) ambient edge term) :
    ∃ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint operations.constraints = .ok (some loaded) ∧
      SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
      SourceEqualityConstraintAllocation.Ready operations.constraints loaded.stored ∧
      ∀ (inherited : SourceEqualityConstraintAllocation.Value),
        SourceEqualityConstraintAllocation.Ready operations.constraints inherited →
        ∀ (output : List SourceEqualityClassOrder.Record),
          (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited operations).1 = .ok (.classes output) →
          ∀ {selected : EqualityNormalize.Constraints} {outcome : Option EqualityNormalize.Class}
            {after : SourceRecursiveIntersectionThunks.State width Symbol Guard} {saved : SourceCurrentEmptinessMemo.Memo},
            SourceCurrentEqualityClassScan.Scan SourceMemoGate.unconstrained
              (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) edge.children
              (output.map SourceEqualityClassOrder.Record.paths) (cold width heap)
              SourceCurrentEmptinessMemo.empty outcome selected after saved → outcome = none := by
  have initial := constructed width expression allowed operations.constraints origins value heap built
  obtain ⟨loaded, found, readback, ready, _⟩ := (initial.2.2.2.2.2 edge resident).2
  refine ⟨loaded, found, readback, ready, ?_⟩
  intro inherited inheritedReady output done selected outcome after saved trace
  exact SourceCurrentClassConstructionEntry.cold_scan_sound width expression allowed value heap built edge resident
    operations valid loaded found inherited inheritedReady output done trace formulas solver ambient term accepted

end MicroCFTA.SourceCurrentClassOriginalFields
