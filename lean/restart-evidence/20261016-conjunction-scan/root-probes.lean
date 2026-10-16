import MicroCFTA.SourceCurrentConjunctionClassScanCompletion

open MicroCFTA
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

#check SourceCurrentConjunctionClassScan.stopped_member
#check SourceCurrentConjunctionClassScan.selected_sublist
#check SourceCurrentConjunctionClassScan.advance_ready
#check SourceCurrentConjunctionClassScan.primary_effects
#check SourceCurrentConjunctionClassScan.secondary_effects
#check SourceCurrentConjunctionClassScan.memo_effects
#check SourceCurrentConjunctionClassScanCompletion.finite
#print axioms SourceCurrentConjunctionClassScan.stopped_member
#print axioms SourceCurrentConjunctionClassScan.selected_sublist
#print axioms SourceCurrentConjunctionClassScan.advance_ready
#print axioms SourceCurrentConjunctionClassScan.primary_effects
#print axioms SourceCurrentConjunctionClassScan.secondary_effects
#print axioms SourceCurrentConjunctionClassScan.memo_effects
#print axioms SourceCurrentConjunctionClassScanCompletion.finite

namespace MicroCFTA.CurrentConjunctionScanKernelProbe
variable {width budget : Nat}

theorem finite_current_scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (classes : Constraints) (before : Checked width) (memo : Memo)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before memo) :
    ∃ outcome selected after saved,
      Scan budget unconstrained reaches values classes before memo outcome selected after saved ∧
      selected.Sublist classes ∧ (∀ paths, outcome = some paths → paths ∈ classes) ∧
      SourceCurrentAllocatedNativePhysicalCompletion.Good after ∧
      SourceEqualityRequiredSemanticCache.SemanticReady after.native.machine.heap ∧
      InternedFreshOrdinaryCostHeap.Heap after.native.machine.heap ∧
      SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧
      SourceCurrentConjunctionEquality.Fields after.operations after.native.machine.heap ∧
      SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after) ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  obtain ⟨outcome, selected, after, saved, actual, finalReady, effects, _, finalCorrect, retained⟩ :=
    SourceCurrentConjunctionClassScanCompletion.finite formulas solver budget unconstrained reaches
      values classes before memo ready available proper correct ranges
  refine ⟨outcome, selected, after, saved, actual, selected_sublist actual, ?_,
    finalReady.good, finalReady.semantic, finalReady.costs, finalReady.scopedCache, finalReady.idle,
    finalReady.good.fields, effects, finalCorrect, retained⟩
  intro paths equal
  subst outcome
  exact stopped_member actual

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) :
    Scan budget unconstrained reaches values [] before memo none [] before memo := .nil

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (paths : Class) (before : Checked width) (memo : Memo) (firstHeap secondHeap : State Symbol Guard)
    (first : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap false firstHeap)
    (second : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths firstHeap false secondHeap) :
    Scan budget unconstrained reaches values [paths, paths] before memo none [paths, paths]
      (advanceHeap (advanceHeap before firstHeap) secondHeap) memo := .selected first (.selected second .nil)

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (paths : Class) (untouched : Constraints) (before middle : Checked width) (memo saved : Memo)
    (heap anchor : State Symbol Guard) (query : Value Symbol Guard) (later : Physical)
    (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap true heap)
    (secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor)
    (seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap (advanceHeap before heap) anchor) query middle)
    (decision : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) true later saved) :
    Scan budget unconstrained reaches values (paths :: untouched) before memo (some paths) []
      (advancePhysical middle later) saved := .stopped primary secondary seeded decision

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {memo saved : Memo} {query : Value Symbol Guard} {before : Checked width} {answer : Bool} {after : Physical}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query (physical before) answer after saved)
    (ready : Ready before) (available : Available before.native.machine.heap query)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo) :
    Ready (advancePhysical before after) ∧
      (advancePhysical before after).native.nodes = before.native.nodes ∧
      (advancePhysical before after).native.edges = before.native.edges ∧
      (advancePhysical before after).native.machine.domains = before.native.machine.domains ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer := by
  obtain ⟨finalReady, _, _, sound, _⟩ := memo_effects formulas solver actual ready available correct
  exact ⟨finalReady, rfl, rfl, rfl, sound⟩

example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (unconstrained reaches : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo) :
    ∃ outcome selected after saved, Scan budget unconstrained reaches values [] before memo outcome selected after saved ∧
      Ready after ∧ SourceCurrentEmptinessMemo.Extends memo saved := by
  obtain ⟨outcome, selected, after, saved, actual, finalReady, _, _, _, retained⟩ :=
    SourceCurrentConjunctionClassScanCompletion.finite formulas solver budget unconstrained reaches values [] before memo
      ready available (by simp) correct trivial
  exact ⟨outcome, selected, after, saved, actual, finalReady, retained⟩

end MicroCFTA.CurrentConjunctionScanKernelProbe
#print axioms MicroCFTA.CurrentConjunctionScanKernelProbe.finite_current_scan
