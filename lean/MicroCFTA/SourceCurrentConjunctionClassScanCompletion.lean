import MicroCFTA.SourceCurrentConjunctionClassScan

/-!
# Finite scans with current conjunction memo effects

The range plan supplies machine bounds only at reached checked native
queries. It supplies no completed query, final invariant, or result law.
Actual gate, projection, native, and current memo completion derive the
complete reached scan. A true answer requires no range plan for the suffix.
Semantic correctness of the seeded query remains a separate obligation.
-/
namespace MicroCFTA.SourceCurrentConjunctionClassScanCompletion
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}

/-- Only actual reached gate and false memo outcomes demand the following range plan. -/
def Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (budget : Nat) (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) : Constraints → Checked width → Memo → Prop
  | [], _, _ => True
  | paths :: classes, before, memo =>
      (∀ heap, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
        before.native.machine.heap false heap →
        Ranges budget unconstrained reaches values classes (advanceHeap before heap) memo) ∧
      (∀ heap, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
        before.native.machine.heap true heap →
        ∀ anchor, SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap true anchor →
        Ranges budget unconstrained reaches values classes (advanceHeap (advanceHeap before heap) anchor) memo) ∧
      (∀ heap, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
        before.native.machine.heap true heap →
        ∀ anchor, SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor →
        SourceCurrentAllocatedSeededQuery.SeededRanges values (paths.map (List.map Int.ofNat))
          (advanceHeap (advanceHeap before heap) anchor) ∧
        ∀ query middle, SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
          (advanceHeap (advanceHeap before heap) anchor) query middle →
          ∀ later saved, SourceCurrentConjunctionMemo.Call budget memo query (physical middle) false later saved →
            Ranges budget unconstrained reaches values classes (advancePhysical middle later) saved)

/-- Initial invariants and reached word bounds derive a finite current scan and its returned states. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (classes : Constraints) (before : Checked width) (memo : Memo)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : Ranges budget unconstrained reaches values classes before memo) :
    ∃ outcome selected after saved,
      Scan budget unconstrained reaches values classes before memo outcome selected after saved ∧
      Ready after ∧ Effects (physical before) (physical after) ∧
      Values after.native.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  induction classes generalizing before memo with
  | nil =>
      exact ⟨none, [], before, memo, .nil, ready,
        .refl _ (SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs),
        available, correct, fun _ _ found => found⟩
  | cons paths classes ih =>
      have tailProper : ∀ other ∈ classes, ∀ path ∈ other, path ≠ [] :=
        fun other member => proper other (List.mem_cons_of_mem _ member)
      obtain ⟨answer, heap, primary, _, _⟩ := SourceCurrentAllocatedGateFields.primary_complete
        unconstrained reaches values paths (physical before)
        (SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs) available
      have first := primary_effects unconstrained reaches primary ready available
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct
      cases answer with
      | false =>
          obtain ⟨outcome, selected, after, saved, actual, finalReady, later, finalValues, finalCorrect, retained⟩ :=
            ih (advanceHeap before heap) memo first.1 first.2.2 tailProper firstCorrect
              (ranges.1 heap primary)
          exact ⟨outcome, paths :: selected, after, saved, .selected primary actual,
            finalReady, first.2.1.trans later, finalValues, finalCorrect, retained⟩
      | true =>
          obtain ⟨answer, anchor, secondary, _, _⟩ := SourceCurrentAllocatedGateFields.secondary_complete
            unconstrained reaches values paths (physical (advanceHeap before heap))
            first.2.1.ready first.2.2
          cases answer with
          | true =>
              have second := secondary_effects unconstrained secondary first.1 first.2.2
              have secondCorrect := SourceCurrentEmptinessMemo.grows formulas solver second.2.1.keeps memo firstCorrect
              obtain ⟨outcome, selected, after, saved, actual, finalReady, later, finalValues, finalCorrect, retained⟩ :=
                ih (advanceHeap (advanceHeap before heap) anchor) memo second.1 second.2.2 tailProper secondCorrect
                  (ranges.2.1 heap primary anchor secondary)
              exact ⟨outcome, selected, after, saved, .skipped primary secondary actual,
                finalReady, first.2.1.trans (second.2.1.trans later), finalValues, finalCorrect, retained⟩
          | false =>
              have reached := ranges.2.2 heap primary anchor secondary
              obtain ⟨query, middle, seeded, queryGood, queryEffects, _, queryScopes, queryIdle, queryAvailable, _⟩ :=
                SourceCurrentAllocatedSeededQuery.false_class_complete unconstrained paths values secondary
                  first.1.good first.2.1.ready first.1.scopedCache first.1.idle first.2.2
                  (proper paths List.mem_cons_self) reached.1
              have queryReady : Ready middle :=
                ⟨queryGood, queryEffects.ready.semantic, queryEffects.ready.costs, queryScopes, queryIdle⟩
              have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver queryEffects.keeps memo firstCorrect
              obtain ⟨answer, later, savedMemo, decision, _⟩ := SourceCurrentConjunctionMemo.complete
                budget memo query (physical middle) queryEffects.ready queryAvailable
              obtain ⟨memoReady, memoEffects, memoCorrect, _, memoRetained⟩ :=
                memo_effects formulas solver decision queryReady queryAvailable queryCorrect
              have memoValues : Values (advancePhysical middle later).native.machine.heap values :=
                fun value member => memoEffects.keeps.available value
                  (queryEffects.keeps.available value (first.2.2 value member))
              cases answer with
              | false =>
                  obtain ⟨outcome, selected, after, saved, actual, finalReady, remaining, finalValues, finalCorrect, retained⟩ :=
                    ih (advancePhysical middle later) savedMemo memoReady memoValues tailProper memoCorrect
                      (reached.2 query middle seeded later savedMemo decision)
                  exact ⟨outcome, selected, after, saved, .continued primary secondary seeded decision actual,
                    finalReady, first.2.1.trans (queryEffects.trans (memoEffects.trans remaining)),
                    finalValues, finalCorrect,
                    fun key entry found => retained key entry (memoRetained key entry found)⟩
              | true =>
                  exact ⟨some paths, [], advancePhysical middle later, savedMemo,
                    .stopped primary secondary seeded decision, memoReady,
                    first.2.1.trans (queryEffects.trans memoEffects), memoValues, memoCorrect, memoRetained⟩

end MicroCFTA.SourceCurrentConjunctionClassScanCompletion
