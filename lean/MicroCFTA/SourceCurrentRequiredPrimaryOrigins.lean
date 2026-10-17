import MicroCFTA.SourceCurrentRequiredPrimaryExposure
import MicroCFTA.SourceCurrentRequiredLanguage
import MicroCFTA.SourceCurrentConstrainedCapGuardExecution
import MicroCFTA.InternedFreshOrdinaryCosts

/-!
# Complete Required execution with primary structural origins

The original false primary class supplies structural exposure safety.
The existing completion theorem constructs the actual result. The same
result retains ordered origins and its full guarded-language receipt.
No future result, graph, or output-origin condition is an input premise.
-/
namespace MicroCFTA.SourceCurrentRequiredPrimaryOrigins
open Language InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open InternedNestedProvenance (Values)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentRequiredRowOrigins (Origin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
noncomputable local instance : DecidableEq (EdgeKey Symbol Guard) := by classical exact inferInstance

/-- Initial caller facts construct a complete Required return with ordered structural origins and exact language. -/
theorem complete
    {paths : Class} {values : List (Value Symbol Guard)} {initial anchor : Heap}
    (gate : EndpointStatefulGateTrace.ClassTrace source reaches values paths initial false anchor)
    (initialSemantic : SemanticReady initial) (initialCosts : InternedFreshOrdinaryCostHeap.Heap initial)
    (initialAvailable : Values initial values)
    (caller : Heap) (semantic : SemanticReady caller)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal caller)
    (costs : InternedFreshOrdinaryCostHeap.Heap caller)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain caller)
    (available : Values caller values) (growth : Grows anchor caller) :
    ∃ results after, Keeps caller after ∧ SemanticReady after ∧ Values after results ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
          (paths.map (List.map Int.ofNat)) values caller) results after ∧
      All₂ Origin values results ∧
      ∀ holds ambient terms,
        All₂ (InternedGuardedLanguage.meaning holds ambient) results terms ↔
          All₂ (InternedGuardedLanguage.meaning holds ambient) values terms ∧
            SourceEqualityRequiredAPI.ForestRequired (paths.map (List.map Int.ofNat)) terms := by
  obtain ⟨results, after, kept, finalSemantic, resident, stable, language⟩ :=
    SourceCurrentRequiredLanguage.primary_complete gate initialSemantic initialCosts initialAvailable
      caller semantic available growth
  refine ⟨results, after, kept, finalSemantic, resident, stable, ?_, language⟩
  obtain ⟨fuel, readFuel, enough⟩ := stable
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff
    (paths.map (List.map Int.ofNat)) values caller results after).mpr
      ⟨fuel, readFuel, enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)⟩
  cases compiled : build (paths.map (List.map Int.ofNat)) with
  | node entries =>
      simp only [compiled] at graph
      exact SourceCurrentRequiredRowOrigins.children graph semantic costs available guards
        (SourceCurrentRequiredPrimaryExposure.primary_domain gate initialSemantic initialAvailable
          caller semantic normal available growth entries compiled)

/-- Actual closed construction derives every heap premise for complete primary-selected structural origins. -/
theorem constructed (expression : InternedNestedConstruction.Syntax Symbol Guard) :
    ∃ value state, InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      ∀ values : List (Value Symbol Guard), Values state values → ∀ paths : Class,
        EndpointStatefulGateTrace.ClassTrace source reaches values paths state false state →
        ∃ results after,
          SourceEqualityRequiredWorkerComplete.StableRun
            (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
              (paths.map (List.map Int.ofNat)) values state) results after ∧
          All₂ Origin values results ∧
          ∀ holds ambient terms,
            All₂ (InternedGuardedLanguage.meaning holds ambient) results terms ↔
              All₂ (InternedGuardedLanguage.meaning holds ambient) values terms ∧
                SourceEqualityRequiredAPI.ForestRequired (paths.map (List.map Int.ofNat)) terms := by
  obtain ⟨value, state, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value state built
  have costs : InternedFreshOrdinaryCostHeap.Heap state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  have normal : SourceCurrentRequiredUnionNormal.UnionNormal state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using SourceCurrentRequiredUnionNormal.source expression
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain state := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      SourceCurrentConstrainedCapGuardExecution.closed_heap Plain expression
  refine ⟨value, state, built, ?_⟩
  intro values available paths gate
  obtain ⟨results, after, _, _, _, stable, origins, language⟩ :=
    complete gate semantic costs available state semantic normal costs guards available (grows_refl state)
  exact ⟨results, after, stable, origins, language⟩

end MicroCFTA.SourceCurrentRequiredPrimaryOrigins
