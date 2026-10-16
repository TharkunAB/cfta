import MicroCFTA.SourceCurrentClassGateCompletion
import MicroCFTA.SourceCurrentSeededQueryCompletion
import MicroCFTA.SourceCurrentEqualityClassScanSoundness

/-!
# Finite current class prefixes before the changed emptiness body

Initial physical invariants derive both class gates and any reached seeded
query. The range plan checks only native requests at actual reached prefixes.
The result stops before provablyEmpty. It does not use the historical
TaskTrace-based Decision as the current conjunction-analysis body.
-/
namespace MicroCFTA.SourceCurrentClassPrefixCompletion
open EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped
open SourceCurrentEqualityClassScanSoundness
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- Only an actual true primary and false secondary prefix needs a seeded native range plan. -/
def Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (paths : Class) (before : Native width Symbol Guard) : Prop :=
  ∀ heap, EndpointStatefulGateTrace.ClassTrace source reaches values paths before.machine.heap true heap →
    ∀ anchor, SourceCurrentSecondaryTrace.ClassTrace source values paths heap false anchor →
      SourceCurrentSeededQueryCompletion.SeededRanges top conjoin values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor)

/-- The actual gate outcomes determine whether a class is selected, skipped, or queried. -/
inductive Prefix [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (paths : Class) :
    Native width Symbol Guard → Bool → Option (Value Symbol Guard) → Native width Symbol Guard → Prop where
  | selected (primary : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.machine.heap false heap) :
      Prefix values paths before true none (advanceHeap before heap)
  | skipped (primary : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.machine.heap true heap)
      (secondary : SourceCurrentSecondaryTrace.ClassTrace source values paths heap true anchor) :
      Prefix values paths before false none (advanceHeap (advanceHeap before heap) anchor)
  | queried (primary : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.machine.heap true heap)
      (secondary : SourceCurrentSecondaryTrace.ClassTrace source values paths heap false anchor)
      (seeded : SourceEmptinessClassFold.Seeded top conjoin values (paths.map (List.map Int.ofNat))
        (advanceHeap (advanceHeap before heap) anchor) query after) :
      Prefix values paths before false (some query) after

/-- Physical readiness constructs the complete reached prefix without supplied gate or query completion. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (paths : Class) (before : Native width Symbol Guard)
    (ready : IdleReady top conjoin before) (costs : CostHeap before.machine.heap)
    (fields : FieldHeap before.machine.heap) (available : Values before.machine.heap values)
    (proper : ∀ path ∈ paths, path ≠ []) (ranges : Ranges values paths before) :
    ∃ selected query after, Prefix values paths before selected query after ∧
      IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
      Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap values ∧
      ∀ value, query = some value → Available after.machine.heap value ∧ value.free = [] := by
  obtain ⟨_, answer, heap, primary, _, _, _, _, _⟩ :=
    SourceCurrentClassGateCompletion.primary_class_complete source reaches values paths before.machine.heap
      ready.semantic costs available
  obtain ⟨primaryReady, primaryCosts, primaryFields, first, primaryValues⟩ :=
    primary_advance source reaches primary ready available costs fields
  cases answer with
  | false =>
      exact ⟨true, none, _, .selected primary, primaryReady, primaryCosts, primaryFields, first, primaryValues,
        by intro value impossible; cases impossible⟩
  | true =>
      obtain ⟨_, answer, anchor, secondary, _, _, _, _, _⟩ :=
        SourceCurrentClassGateCompletion.secondary_class_complete source reaches values paths heap
          primaryReady.semantic primaryCosts primaryValues
      cases answer with
      | true =>
          obtain ⟨finalReady, finalCosts, finalFields, second, finalValues⟩ :=
            secondary_advance source secondary primaryReady primaryValues primaryCosts primaryFields
          exact ⟨false, none, _, .skipped primary secondary, finalReady, finalCosts, finalFields,
            first.trans second, finalValues, by intro value impossible; cases impossible⟩
      | false =>
          obtain ⟨query, after, seeded, finalReady, finalCosts, finalFields, second, _, resident, closed, finalValues, _⟩ :=
            SourceCurrentSeededQueryCompletion.false_class_complete source paths values secondary
              primaryReady primaryCosts primaryFields primaryValues proper (ranges heap primary anchor secondary)
          exact ⟨false, some query, after, .queried primary secondary seeded, finalReady, finalCosts, finalFields,
            first.trans second, finalValues, by intro value same; cases same; exact ⟨resident, closed⟩⟩

end MicroCFTA.SourceCurrentClassPrefixCompletion
