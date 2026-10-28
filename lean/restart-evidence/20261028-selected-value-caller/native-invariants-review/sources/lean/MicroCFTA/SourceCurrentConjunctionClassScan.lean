import MicroCFTA.SourceCurrentAllocatedConjunctionMemo
import MicroCFTA.SourceCurrentAllocatedGateFields
import MicroCFTA.SourceCurrentAllocatedSeededQuery

/-!
# Class scans with the current conjunction decision

The graph records only reached original classes. Gates retain the actual
native tables and equality-operation state. A refused query uses the checked
seeded fold, then the current conjunction memo. A true answer stops before
the class suffix. Selected classes retain their order and multiplicity.

This graph does not use the historical intersection-based emptiness Call.
Exact query-language transport, the three global gate memo receipts, and
the general constrained caller remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentConjunctionClassScan
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {width : Nat}

/-- Gate effects update the constructor heap in the same checked state. -/
def advanceHeap (before : Checked width) (heap : State Symbol Guard) : Checked width :=
  advancePhysical before ⟨heap, before.operations⟩

/-- Reached classes thread actual gate, checked-query, and current memo results. -/
inductive Scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (budget : Nat) (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) :
    Constraints → Checked width → Memo → Option Class → Constraints → Checked width → Memo → Prop where
  | nil : Scan budget unconstrained reaches values [] state memo none [] state memo
  | selected
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
        before.native.machine.heap false heap)
      (rest : Scan budget unconstrained reaches values classes (advanceHeap before heap)
        memo outcome selected after saved) :
      Scan budget unconstrained reaches values (paths :: classes) before memo outcome (paths :: selected) after saved
  | skipped
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
        before.native.machine.heap true heap)
      (secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap true anchor)
      (rest : Scan budget unconstrained reaches values classes
        (advanceHeap (advanceHeap before heap) anchor) memo outcome selected after saved) :
      Scan budget unconstrained reaches values (paths :: classes) before memo outcome selected after saved
  | continued
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
        before.native.machine.heap true heap)
      (secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor)
      (seeded : SourceCurrentAllocatedSeededQuery.Seeded values
        (paths.map (List.map Int.ofNat)) (advanceHeap (advanceHeap before heap) anchor) query middle)
      (decision : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) false later savedMemo)
      (rest : Scan budget unconstrained reaches values classes (advancePhysical middle later)
        savedMemo outcome selected after saved) :
      Scan budget unconstrained reaches values (paths :: classes) before memo outcome selected after saved
  | stopped
      (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
        before.native.machine.heap true heap)
      (secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor)
      (seeded : SourceCurrentAllocatedSeededQuery.Seeded values
        (paths.map (List.map Int.ofNat)) (advanceHeap (advanceHeap before heap) anchor) query middle)
      (decision : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) true later saved) :
      Scan budget unconstrained reaches values (paths :: classes) before memo (some paths) []
        (advancePhysical middle later) saved

/-- Every rejection names an original class in the reached prefix. -/
theorem stopped_member [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {paths : Class} {before after : Checked width} {memo saved : Memo}
    (trace : Scan budget unconstrained reaches values classes before memo (some paths) selected after saved) :
    paths ∈ classes := by
  generalize result : some paths = outcome at trace
  induction trace with
  | nil => cases result
  | selected primary rest ih => exact List.mem_cons_of_mem _ (ih result)
  | skipped primary secondary rest ih => exact List.mem_cons_of_mem _ (ih result)
  | continued primary secondary seeded decision rest ih => exact List.mem_cons_of_mem _ (ih result)
  | stopped primary secondary seeded decision =>
      have same := Option.some.inj result
      subst paths
      exact List.mem_cons_self

/-- The selected reached records retain source order and repeated occurrences. -/
theorem selected_sublist [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {outcome : Option Class} {before after : Checked width} {memo saved : Memo}
    (trace : Scan budget unconstrained reaches values classes before memo outcome selected after saved) :
    selected.Sublist classes := by
  induction trace with
  | nil => exact .refl _
  | selected primary rest ih => exact .cons_cons _ ih
  | skipped primary secondary rest ih => exact .cons _ ih
  | continued primary secondary seeded decision rest ih => exact .cons _ ih
  | stopped => exact List.nil_sublist _

/-- Physical readiness includes the scope needed by subsequent generated native operands. -/
structure Ready (state : Checked width) : Prop where
  good : Good state
  semantic : SemanticReady state.native.machine.heap
  costs : CostHeap state.native.machine.heap
  scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native
  idle : SourceRecursiveIntersectionNative.Idle state.native

/-- Constructor-only effects retain every checked invariant at the same native tables. -/
theorem advance_ready (before : Checked width) (after : Physical) (ready : Ready before)
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) after) :
    Ready (advancePhysical before after) :=
  ⟨SourceCurrentAllocatedConjunctionMemo.advance_good before after ready.good effects,
    effects.ready.semantic, effects.ready.costs,
    SourceCurrentAllocatedConjunctionMemo.advance_scoped before after ready.scopedCache,
    SourceCurrentAllocatedConjunctionMemo.advance_idle before after ready.idle⟩

/-- Each actual primary gate derives readiness and retains the original forest. -/
theorem primary_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : Class} {before : Checked width}
    {answer : Bool} {heap : State Symbol Guard}
    (actual : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap answer heap)
    (ready : Ready before) (available : Values before.native.machine.heap values) :
    Ready (advanceHeap before heap) ∧
      SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical (advanceHeap before heap)) ∧
      Values (advanceHeap before heap).native.machine.heap values := by
  have first := SourceCurrentAllocatedGateFields.primary_class unconstrained reaches actual
    (SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs) available
  exact ⟨advance_ready before ⟨heap, before.operations⟩ ready first.1, first.1, first.2⟩

/-- Each actual secondary gate derives readiness in its actual returned heap. -/
theorem secondary_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : Class} {before : Checked width}
    {answer : Bool} {heap : State Symbol Guard}
    (actual : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths
      before.native.machine.heap answer heap)
    (ready : Ready before) (available : Values before.native.machine.heap values) :
    Ready (advanceHeap before heap) ∧
      SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical (advanceHeap before heap)) ∧
      Values (advanceHeap before heap).native.machine.heap values := by
  have first := SourceCurrentAllocatedGateFields.secondary_class unconstrained actual
    (SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs) available
  exact ⟨advance_ready before ⟨heap, before.operations⟩ ready first.1, first.1, first.2⟩

/-- Each reached current memo call derives readiness and its final fourth-memo invariant. -/
theorem memo_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {memo saved : Memo} {query : Value Symbol Guard}
    {before : Checked width} {answer : Bool} {after : Physical}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query (physical before) answer after saved)
    (ready : Ready before) (available : Available before.native.machine.heap query)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo) :
    Ready (advancePhysical before after) ∧
      SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical (advancePhysical before after)) ∧
      SourceCurrentEmptinessMemo.Correct formulas solver (advancePhysical before after).native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      SourceCurrentEmptinessMemo.Extends memo saved := by
  obtain ⟨receipt, finalCorrect, sound, retained⟩ := SourceCurrentAllocatedConjunctionMemo.call_effects
    formulas solver actual ready.good ready.semantic ready.costs ready.idle available correct
  exact ⟨advance_ready before after ready receipt.effects, receipt.effects, finalCorrect, sound, retained⟩

end MicroCFTA.SourceCurrentConjunctionClassScan
