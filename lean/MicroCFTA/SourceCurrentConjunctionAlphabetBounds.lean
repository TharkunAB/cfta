import MicroCFTA.SourceCurrentConjunctionCallerNumeric

/-!
# Conjunction resources from one initial guard alphabet

The initial heap uses one finite guard alphabet. Actual decisions and memo
calls retain that alphabet. The same alphabet supplies both worker ceilings
and the full caller forecast. Causal guard observations remain separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionAlphabetBounds
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorklist (closed)
open SourceCurrentConjunctionWorklistResources (forecast workerFuel readerFuel)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula

/-- The same actual decision retains every initial guard in the fixed alphabet. -/
theorem decision_carrier [DecidableEq Symbol]
    [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
    [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    (alphabet : List Guard)
    {budget : Nat} {start : Value Symbol Guard} {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionDecision.Decision budget start before answer after)
    (ready : Ready before) (available : Available before.heap start)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) after.heap := by
  cases actual with
  | open_input _ => exact known
  | closed _ explored _ =>
      exact (SourceCurrentConjunctionGuardUniverse.run_heap (fun guard => guard ∈ alphabet)
        explored ready (by
          intro nodes member value included
          cases List.mem_singleton.mp member
          cases List.mem_singleton.mp included
          exact available) known).2

/-- The initial alphabet bounds the same decision and both independent worker ceilings. -/
theorem decision_bound [DecidableEq Symbol]
    [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
    [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    (alphabet : List Guard)
    {budget : Nat} {start : Value Symbol Guard} {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionDecision.Decision budget start before answer after)
    (resource : Nat) (ready : Ready before) (available : Available before.heap start)
    (fits : Fits resource before.heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (forecast alphabet budget resource) after.heap ∧
      (∀ work reader, workerFuel alphabet budget resource ≤ work →
        readerFuel alphabet budget resource ≤ reader →
        SourceCurrentConjunctionWorker.decision work reader budget start before = .done answer after) := by
  cases actual with
  | open_input openInput =>
      exact ⟨fits.mono (SourceCurrentConjunctionWorklistResources.forecast_ge _ _ _),
        by intros; simp only [SourceCurrentConjunctionWorker.decision, openInput, Bool.false_eq_true, ite_false]⟩
  | closed admitted explored grown =>
      have inputs : SourceCurrentConjunctionWorklist.PendingReady before [[start]] := by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available
      have widths : ∀ nodes ∈ [[start]], nodes.length ≤ resource := by
        intro nodes member
        cases List.mem_singleton.mp member
        exact fits.stored.positive
      have numeric := SourceCurrentConjunctionWorklistResources.bound explored alphabet resource
        ready inputs fits widths known
      refine ⟨numeric.1, ?_⟩
      intro work reader enoughWork enoughRead
      simp only [SourceCurrentConjunctionWorker.decision, admitted, ite_true,
        numeric.2 work reader enoughWork enoughRead, SourceCurrentConjunctionWorker.Outcome.bind, grown]

/-- Initial physical facts construct a decision and retain the supplied alphabet. -/
theorem decision_complete [DecidableEq Symbol]
    [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
    [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    (alphabet : List Guard) (budget : Nat) (start : Value Symbol Guard)
    (before : Physical) (resource : Nat) (ready : Ready before)
    (available : Available before.heap start) (fits : Fits resource before.heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    ∃ answer after, SourceCurrentConjunctionDecision.Decision budget start before answer after ∧
      Effects before after ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) after.heap ∧
      Fits (forecast alphabet budget resource) after.heap ∧
      (∀ work reader, workerFuel alphabet budget resource ≤ work →
        readerFuel alphabet budget resource ≤ reader →
        SourceCurrentConjunctionWorker.decision work reader budget start before = .done answer after) := by
  obtain ⟨answer, after, actual, effects⟩ := SourceCurrentConjunctionDecision.complete budget start before ready available
  exact ⟨answer, after, actual, effects, decision_carrier alphabet actual ready available known,
    decision_bound alphabet actual resource ready available fits known⟩

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteValue" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsAllocation.State ConcreteSymbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

section Concrete
variable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
  [DecidableEq ConcreteValue]

/-- Hits preserve the exact heap and misses retain the same initial guard alphabet. -/
theorem call_carrier (alphabet : List ConcreteGuard)
    {budget : Nat} {memo saved : Memo} {query : ConcreteValue}
    {before after : ConcretePhysical} {answer : Bool}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query before answer after saved)
    (ready : Ready before) (available : Available before.heap query)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) after.heap := by
  cases actual with
  | hit _ => exact known
  | miss _ actual => exact decision_carrier alphabet actual ready available known

/-- The same actual memo return fits the initial alphabet forecast and common replay ceilings. -/
theorem call_bound (alphabet : List ConcreteGuard)
    {budget : Nat} {memo saved : Memo} {query : ConcreteValue}
    {before after : ConcretePhysical} {answer : Bool}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query before answer after saved)
    (resource : Nat) (ready : Ready before) (available : Available before.heap query)
    (fits : Fits resource before.heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (forecast alphabet budget resource) after.heap ∧
      (∀ work reader, workerFuel alphabet budget resource ≤ work →
        readerFuel alphabet budget resource ≤ reader →
        SourceCurrentConjunctionWorker.call work reader budget memo query before = .done (answer, saved) after) := by
  cases actual with
  | hit found =>
      exact ⟨fits.mono (SourceCurrentConjunctionWorklistResources.forecast_ge _ _ _),
        by intros; simp only [SourceCurrentConjunctionWorker.call, found]⟩
  | miss absent actual =>
      have numeric := decision_bound alphabet actual resource ready available fits known
      exact ⟨numeric.1, by
        intro work reader enoughWork enoughRead
        simp only [SourceCurrentConjunctionWorker.call, absent, numeric.2 work reader enoughWork enoughRead,
          SourceCurrentConjunctionWorker.Outcome.bind]⟩

/-- Initial physical and memo facts construct the complete call with the original alphabet. -/
theorem memo_complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (alphabet : List ConcreteGuard)
    (budget : Nat) (memo : Memo) (query : ConcreteValue) (before : ConcretePhysical)
    (resource : Nat) (ready : Ready before) (available : Available before.heap query)
    (fits : Fits resource before.heap)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.heap memo)
    (annotation : ConcreteGuard → Prop) (guards : SourceCurrentConstrainedCapGuardHeap.Heap annotation before.heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    ∃ answer after saved, SourceCurrentConjunctionMemo.Call budget memo query before answer after saved ∧
      Effects before after ∧ SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧ SourceCurrentEmptinessMemo.Extends memo saved ∧
      SourceCurrentConstrainedCapGuardHeap.Heap annotation after.heap ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) after.heap ∧
      Fits (forecast alphabet budget resource) after.heap ∧
      (∀ work reader, workerFuel alphabet budget resource ≤ work →
        readerFuel alphabet budget resource ≤ reader →
        SourceCurrentConjunctionWorker.call work reader budget memo query before = .done (answer, saved) after) := by
  obtain ⟨answer, after, saved, actual, effects, finalCorrect, sound, retained⟩ :=
    SourceCurrentConjunctionMemo.finite formulas solver budget memo query before ready available correct
  exact ⟨answer, after, saved, actual, effects, finalCorrect, sound, retained,
    SourceCurrentConjunctionGuard.call annotation actual ready available guards,
    call_carrier alphabet actual ready available known,
    call_bound alphabet actual resource ready available fits known⟩

end Concrete

open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame)
open SourceCurrentConstrainedCapTargetForecast (scalar)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "advance" => SourceCurrentAllocatedPartialState.advance

/-- One fixed initial alphabet supplies the full caller forecast. -/
noncomputable def callerForecast (alphabet : List ConcreteGuard) (budget : Nat) (profile : Profile) : Profile :=
  let resource := forecast alphabet budget (scalar profile)
  ⟨resource, resource, profile.domains, resource⟩

/-- The caller forecast retains all initial numeric components. -/
theorem callerForecast_ge (alphabet : List ConcreteGuard) (budget : Nat) (profile : Profile) :
    Le profile (callerForecast alphabet budget profile) := by
  have retained := SourceCurrentConjunctionWorklistResources.forecast_ge alphabet budget (scalar profile)
  exact ⟨Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_nodes profile) retained,
    Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_edges profile) retained,
    Nat.le_refl _, Nat.le_trans (SourceCurrentConstrainedCapTargetForecast.scalar_mass profile) retained⟩

/-- Larger initial numeric components retain the same supplied-alphabet schedule. -/
theorem callerForecast_mono (alphabet : List ConcreteGuard) (budget : Nat) {first last : Profile}
    (increase : Le first last) : Le (callerForecast alphabet budget first) (callerForecast alphabet budget last) := by
  have retained := SourceCurrentConjunctionWorklistResources.forecast_mono alphabet budget
    (SourceCurrentConstrainedCapTargetForecast.scalar_mono increase)
  exact ⟨retained, retained, increase.2.2.1, retained⟩

/-- Initial caller facts construct their own call and full Post with the same supplied alphabet. -/
theorem caller_complete [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteValue]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (alphabet : List ConcreteGuard) (inventory : Inventory) (budget : Nat) (query : ConcreteValue)
    (before : Caller width) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile)
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile before.checked)
    (available : Available before.checked.native.machine.heap query)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ answer after saved,
      SourceCurrentConjunctionMemo.Call budget before.fourth query (physical before.checked) answer after saved ∧
      Frame formulas solver inventory (advancePhysical before.checked after) ∧
      Post formulas solver inventory before (advance before (advancePhysical before.checked after) saved before.merge) memos ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Fits (callerForecast alphabet budget profile)
        (advancePhysical before.checked after) ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) after.heap ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      (advance before (advancePhysical before.checked after) saved before.merge).nodeResults = before.nodeResults ∧
      (advance before (advancePhysical before.checked after) saved before.merge).edgeResults = before.edgeResults ∧
      (advance before (advancePhysical before.checked after) saved before.merge).merge = before.merge ∧
      (advance before (advancePhysical before.checked after) saved before.merge).fourth = saved ∧
      (∀ work reader, workerFuel alphabet budget (scalar profile) ≤ work →
        readerFuel alphabet budget (scalar profile) ≤ reader →
        SourceCurrentConjunctionWorker.call work reader budget before.fourth query (physical before.checked) = .done (answer, saved) after) := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good initial.ready.semantic initial.ready.costs
  have scalarFits := (SourceCurrentConstrainedCapRequiredResources.of_checked fits).scalar_fits
  obtain ⟨answer, after, saved, actual, effects, correct, sound, retained, _guards, carrier, bounded, done⟩ :=
    memo_complete formulas solver alphabet budget before.fourth query (physical before.checked)
      (scalar profile) ready available scalarFits initial.correct Plain frame.context.guards known
  have returned := SourceCurrentConjunctionCallerNumeric.of_call formulas solver actual frame available initial.correct
  have probes := SourceCurrentAllocatedProbeConjunction.call_heap actual ready available initial.probes
  have post : Post formulas solver inventory before (advance before (advancePhysical before.checked after) saved before.merge) memos := by
    exact ⟨⟨returned.ready, returned.admitted,
      initial.sound.advance formulas solver _ saved before.merge effects,
      initial.stored.grows effects.keeps, initial.covered, correct,
      SourceQueryUnfoldMemo.valid_grows _ _ initial.ready.semantic effects.keeps memos initial.globals, probes⟩,
      effects, Cache.extends_refl _, retained⟩
  exact ⟨answer, after, saved, actual, returned, post,
    ⟨bounded.nodes, bounded.edges, fits.domains, bounded.stored⟩, carrier, sound, rfl, rfl, rfl, rfl, done⟩

end MicroCFTA.SourceCurrentConjunctionAlphabetBounds
