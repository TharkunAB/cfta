import MicroCFTA.SourceCurrentAllocatedTupleConjunctionWorkerActual
import MicroCFTA.SourceCurrentConjunctionDemandWorklistNumeric
import MicroCFTA.SourceCurrentConstrainedCapRequiredResources

/-!
# Current-entry resources for the checked tuple worker

The initial caller and numeric profile supply the same tuple call, returned
state, read receipt, and complete caller invariant. The heap guard carrier
and one initial pending entry determine both lower-stage ceilings. Constructor
bounds may increase. The original domain bound is retained. These bounds do
not identify eager reads with native lazy demand or count native runtime work.
-/
namespace MicroCFTA.SourceCurrentAllocatedTupleConjunctionWorkerActual
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapTargetForecast (scalar)
open SourceCurrentAllocatedTupleConjunctionWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Call" => SourceCurrentConjunctionDemandWorklistExecution.Call
local notation "CallReads" => SourceCurrentConjunctionDemandWorklistMemos.CallReads
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
local notation "workerFuel" => SourceCurrentConjunctionDemandWorklistNumeric.workerFuel
local notation "readerFuel" => SourceCurrentConjunctionDemandWorklistNumeric.readerFuel

/-- The entry heap and profile supply constructor bounds while retaining the original domain bound. -/
noncomputable def forecast (heap : Heap) (budget : Nat) (profile : Profile) : Profile :=
  let resource := SourceCurrentConjunctionDemandWorklistNumeric.forecast (guards heap) budget 1 (scalar profile)
  ⟨resource, resource, profile.domains, resource⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Initial Context and Fits derive the same complete checked call, read receipt, and numeric replay. -/
theorem finite_resources {inventory : Inventory} {before : Caller width}
    {query : Value Symbol Guard} {memos : Memos}
    (budget : Nat) (profile : Profile) (initial : Context formulas solver inventory before memos)
    (fits : Fits profile before.checked) (available : Available before.checked.native.machine.heap query) :
    ∃ (answer : Bool) (reached : Physical) (saved : Memo) (final : Memos),
      ∃ actual : Call budget before.fourth query (physical before.checked) answer reached saved,
        CallReads actual memos final ∧
        Post formulas solver inventory before
          (SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked reached) saved before.merge) final ∧
        SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
        Available reached.heap query ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
        Fits (forecast before.checked.native.machine.heap budget profile) (advancePhysical before.checked reached) ∧
        (∀ work reader,
          workerFuel (guards before.checked.native.machine.heap) budget 1 (scalar profile) ≤ work →
          readerFuel (guards before.checked.native.machine.heap) budget 1 (scalar profile) ≤ reader →
          call work reader budget query before.checked before.fourth =
            .done answer (advancePhysical before.checked reached) saved) := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  have scalarFits := (SourceCurrentConstrainedCapRequiredResources.of_checked fits).scalar_fits
  obtain ⟨answer, reached, saved, actual, _effects, numeric, replay⟩ :=
    SourceCurrentConjunctionDemandWorklistNumeric.call_complete budget before.fourth query (physical before.checked)
      (scalar profile) ready available scalarFits
  obtain ⟨final, reads, post, sound, returnedAvailable, unfolding, querySame⟩ :=
    SourceCurrentAllocatedTupleConjunctionCaller.actual formulas solver actual initial available
  refine ⟨answer, reached, saved, final, actual, reads, post, sound, returnedAvailable, unfolding, querySame, ?_, ?_⟩
  · exact ⟨numeric.nodes, numeric.edges, fits.domains, numeric.stored⟩
  · intro work reader enoughWork enoughRead
    exact call_lift (replay work reader enoughWork enoughRead)

/-- A supplied checked success retains its exact endpoint, full receipt, and entry-derived resource bounds. -/
theorem raw_done_resources {inventory : Inventory} {p h budget : Nat}
    {before : Caller width} {after : Checked width} {query : Value Symbol Guard}
    {answer : Bool} {saved : Memo} {memos : Memos}
    (profile : Profile) (initial : Context formulas solver inventory before memos)
    (fits : Fits profile before.checked) (available : Available before.checked.native.machine.heap query)
    (done : call p h budget query before.checked before.fourth = .done answer after saved) :
    ∃ reached final, after = advancePhysical before.checked reached ∧
      ∃ actual : Call budget before.fourth query (physical before.checked) answer reached saved,
        CallReads actual memos final ∧
        Post formulas solver inventory before
          (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
        SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
        Available after.native.machine.heap query ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
        Fits (forecast before.checked.native.machine.heap budget profile) after ∧
        (∀ work reader,
          workerFuel (guards before.checked.native.machine.heap) budget 1 (scalar profile) ≤ work →
          readerFuel (guards before.checked.native.machine.heap) budget 1 (scalar profile) ≤ reader →
          call work reader budget query before.checked before.fourth = .done answer after saved) := by
  obtain ⟨reached, final, same, actual, reads, post, sound, returnedAvailable, unfolding, querySame⟩ :=
    verified formulas solver initial available done
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  have scalarFits := (SourceCurrentConstrainedCapRequiredResources.of_checked fits).scalar_fits
  have numeric := SourceCurrentConjunctionDemandWorklistNumeric.call_bound actual
    (guards before.checked.native.machine.heap) (scalar profile) ready available scalarFits
    (SourceCurrentConjunctionGuardUniverse.initial before.checked.native.machine.heap
      ready.semantic.ready.semantic.1.normal.facts)
  have returned : Fits (forecast before.checked.native.machine.heap budget profile)
      (advancePhysical before.checked reached) :=
    ⟨numeric.1.nodes, numeric.1.edges, fits.domains, numeric.1.stored⟩
  refine ⟨reached, final, same, actual, reads, post, sound, returnedAvailable, unfolding, querySame, ?_, ?_⟩
  · simpa only [same] using returned
  · intro work reader enoughWork enoughRead
    simpa only [same] using call_lift (numeric.2 work reader enoughWork enoughRead)

end MicroCFTA.SourceCurrentAllocatedTupleConjunctionWorkerActual
