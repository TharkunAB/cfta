import MicroCFTA.SourceEqualityNativeInitial
import MicroCFTA.SourceEqualityNativeDemandFieldHeap
import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.InternedFreshOrdinaryConstraintHeap

/-!
# Initial current class state from original source construction

The actual closed constructor run supplies native readiness, costs, stored
normalized fields, and available original children. Cold initialization
starts only the domain and native request tables. The separate equality
interner and warm global memo tables are not initialized by this theorem.
-/
namespace MicroCFTA.SourceCurrentClassInitial
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped SourceEqualityNativeInitial
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap
local notation "ValidGuard" => fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities

/-- Actual normalized source construction derives the initial native state and every resident edge input. -/
theorem constructed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : InternedFreshOrdinaryConstraintHeap.SyntaxValid ValidGuard expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    IdleReady top conjoin (cold width heap) ∧ CostHeap heap ∧ FieldHeap heap ∧
      Available heap value ∧ value.free = [] ∧
      ∀ edge, EdgeResident heap edge → Values heap edge.children ∧ ValidGuard edge.entry.key.constraint := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value heap built
  have checked := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using checked.facts
  have costs : CostHeap heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  have fields : FieldHeap heap := by
    simpa only [SourceEqualityNativeDemandFieldHeap.Heap, built, InternedNestedConstruction.Outcome.state] using
      InternedFreshOrdinaryConstraintHeap.build_heap ValidGuard expression [] empty
        (InternedFreshOrdinaryConstraintHeap.empty_heap _) allowed
  refine ⟨ready width top conjoin heap semantic, costs, fields, checked.result value heap built,
    InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value heap built, ?_⟩
  intro edge resident
  exact ⟨facts.cached.edges edge.entry.key edge resident,
    SourceEqualityNativeDemandFieldHeap.resident_cached heap fields edge resident⟩

/-- Original normalized syntax has a finite closed run with the derived cold class-entry invariants. -/
theorem closed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : InternedFreshOrdinaryConstraintHeap.SyntaxValid ValidGuard expression) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      IdleReady top conjoin (cold width heap) ∧ CostHeap heap ∧ FieldHeap heap ∧
        Available heap value ∧ value.free = [] ∧
        ∀ edge, EdgeResident heap edge → Values heap edge.children ∧ ValidGuard edge.entry.key.constraint := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  exact ⟨value, heap, built, constructed width expression allowed value heap built⟩

end MicroCFTA.SourceCurrentClassInitial
