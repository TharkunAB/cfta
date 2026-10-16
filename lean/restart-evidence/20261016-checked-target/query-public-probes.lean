import MicroCFTA.SourceCurrentAllocatedTargetQuery

#print axioms MicroCFTA.SourceCurrentAllocatedTargetQuery.Step.done
#print axioms MicroCFTA.SourceCurrentAllocatedTargetQuery.Step.unique
#print axioms MicroCFTA.SourceCurrentAllocatedTargetQuery.finite
#print axioms MicroCFTA.SourceCurrentAllocatedTargetQuery.Step.verified
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetQuery.Step.done
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetQuery.Step.unique
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetQuery.finite
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetQuery.Step.verified

namespace MicroCFTA.AllocatedTargetQueryProbes
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedTargetQuery
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "S" => SourceObservations.Label FullSyntax.Formula
local notation "G" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ranges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
variable {width : Nat} [DecidableEq S] [DecidableEq (EdgeKey S G)]

-- A literal physical trace constructs a raw step without semantic premises.
example {fuel : Nat} {left right value : Value S G} {before after : Checked width}
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before (.code (.pure value)) after) :
    Step left right before value after := .run trace

-- The trace has the exact count-plus-one completion convention.
example {fuel : Nat} {left right value : Value S G} {before after : Checked width}
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before (.code (.pure value)) after) :
    execute (fuel + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after :=
  trace_done fuel _ before after value trace.steps

-- Uniqueness covers every checked state field, including both operation tables.
example {left right first second : Value S G} {before one two : Checked width}
    (firstStep : Step left right before first one) (secondStep : Step left right before second two) :
    one.operations = two.operations ∧ one.native = two.native := by
  have same := (firstStep.unique secondStep).2
  exact ⟨congrArg State.operations same, congrArg State.native same⟩

-- Empty operands are admitted as literal duplicate roots; no completion is an input.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width) (ready : Ready before)
    (admitted : At formulas solver inventory before)
    (ranges : Ranges (.code (requestNode IntersectionEmptyDomain.emptyDomain (.empty : Value S G) .empty)) before)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ next : Inventory, ∃ value after,
      next.source = before.native.machine.heap ∧ next.roots = inventory.roots ++ [.empty, .empty] ∧
      Receipt formulas solver next .empty .empty before value after memos :=
  finite formulas solver inventory .empty .empty before ready admitted
    (InternedProbeProvenance.empty_available _) (InternedProbeProvenance.empty_available _)
    rfl rfl ranges memos valid

-- Arbitrary actual steps gain final readiness from initial admission, not a final invariant premise.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {left right value : Value S G} {before after : Checked width}
    (actual : Step left right before value after) (ready : Ready before)
    (admitted : At formulas solver inventory before)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : Ranges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) : Ready after := by
  obtain ⟨next, _, _, receipt⟩ := actual.verified formulas solver inventory ready admitted
    leftAvailable rightAvailable leftClosed rightClosed ranges memos valid
  exact receipt.ready

-- Repeated operands have their original language under every ambient environment.
example {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {left value : Value S G} {before after : Checked width} {memos : Memos}
    (receipt : Receipt formulas solver inventory left left before value after memos)
    (ambient : InternedGuardedLanguage.Env S) (term : Term S) :
    InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ↔
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term := by
  simpa only [and_self] using receipt.meaning ambient term

-- Global coherence and operational silence refer to the same original memo bundle.
example {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {left right value : Value S G} {before after : Checked width} {memos : Memos}
    (receipt : Receipt formulas solver inventory left right before value after memos) :
    Valid after.native.machine.heap memos ∧
    ∃ events, SourceGlobalUnfold.Runs ⟨before.native.machine.heap, memos.unfolding⟩
      ⟨after.native.machine.heap, memos.unfolding⟩ events ∧ SourceGlobalUnfold.NoGlobal events :=
  ⟨receipt.globals, receipt.events⟩

-- Actual equality operations retain all earlier completed combination and descent entries.
example {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {left right value : Value S G} {before after : Checked width} {memos : Memos}
    (receipt : Receipt formulas solver inventory left right before value after memos) :
    SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations := receipt.effects.grows
end MicroCFTA.AllocatedTargetQueryProbes
