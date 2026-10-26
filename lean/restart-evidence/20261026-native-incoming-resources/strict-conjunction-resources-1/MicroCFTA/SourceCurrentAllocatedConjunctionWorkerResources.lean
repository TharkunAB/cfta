import MicroCFTA.SourceCurrentAllocatedConjunctionWorkerActual
import MicroCFTA.SourceCurrentConjunctionCallerNumeric

/-!
# Numeric resources for the actual conjunction worker

The current entry heap supplies the finite guard carrier.
The same actual call retains its full caller and computed resource bounds.
The constructor heap can grow. The native tables and domain cache stay exact.
The forecast does not bound guard data from an earlier query entry.
-/
namespace MicroCFTA.SourceCurrentAllocatedConjunctionWorkerActual
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapTargetForecast (scalar)
open SourceCurrentAllocatedConjunctionWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Call" => SourceCurrentConjunctionMemo.Call
local notation "CallReads" => SourceCurrentConjunctionGlobalMemos.CallReads
local notation "forecast" => SourceCurrentConjunctionCallerNumeric.forecast
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
local notation "workerFuel" => SourceCurrentConjunctionWorklistResources.workerFuel
local notation "readerFuel" => SourceCurrentConjunctionWorklistResources.readerFuel
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Current caller facts produce one call, its full receipts, and computed stable bounds. -/
theorem finite_resources {inventory : Inventory} {before : Caller width}
    {query : Value Symbol Guard} {memos : Memos}
    (budget : Nat) (profile : Profile) (initial : Context formulas solver inventory before memos)
    (fits : Fits profile before.checked) (available : Available before.checked.native.machine.heap query) :
    ∃ answer (reached : Physical) saved final,
      ∃ actual : Call budget before.fourth query (physical before.checked) answer reached saved,
        CallReads actual memos final ∧
        Post formulas solver inventory before
          (SourceCurrentAllocatedPartialState.advance before (advancePhysical before.checked reached) saved before.merge) final ∧
        SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
        Available reached.heap query ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
        Fits (forecast before.checked.native.machine.heap budget profile) (advancePhysical before.checked reached) ∧
        (∀ work reader,
          workerFuel (guards before.checked.native.machine.heap) budget (scalar profile) ≤ work →
          readerFuel (guards before.checked.native.machine.heap) budget (scalar profile) ≤ reader →
          call work reader budget query before.checked before.fourth =
            .done answer (advancePhysical before.checked reached) saved) := by
  obtain ⟨answer, reached, saved, final, actual, reads, post, sound, returnedAvailable, unfolding, querySame⟩ :=
    SourceCurrentAllocatedConjunctionCaller.finite formulas solver budget initial available
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  have scalarFits := (SourceCurrentConstrainedCapRequiredResources.of_checked fits).scalar_fits
  have numeric := SourceCurrentConjunctionNumeric.call_bound actual (scalar profile) ready available scalarFits
  refine ⟨answer, reached, saved, final, actual, reads, post, sound, returnedAvailable, unfolding, querySame, ?_, ?_⟩
  · exact ⟨numeric.1.nodes, numeric.1.edges, fits.domains, numeric.1.stored⟩
  · intro work reader enoughWork enoughRead
    exact call_lift (numeric.2 work reader enoughWork enoughRead)

/-- A supplied success retains its literal endpoint and the same current-entry forecast. -/
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
          workerFuel (guards before.checked.native.machine.heap) budget (scalar profile) ≤ work →
          readerFuel (guards before.checked.native.machine.heap) budget (scalar profile) ≤ reader →
          call work reader budget query before.checked before.fourth = .done answer after saved) := by
  obtain ⟨reached, final, same, actual, reads, post, sound, returnedAvailable, unfolding, querySame⟩ :=
    verified formulas solver initial available done
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  have scalarFits := (SourceCurrentConstrainedCapRequiredResources.of_checked fits).scalar_fits
  have numeric := SourceCurrentConjunctionNumeric.call_bound actual (scalar profile) ready available scalarFits
  have returned : Fits (forecast before.checked.native.machine.heap budget profile)
      (advancePhysical before.checked reached) :=
    ⟨numeric.1.nodes, numeric.1.edges, fits.domains, numeric.1.stored⟩
  refine ⟨reached, final, same, actual, reads, post, sound, returnedAvailable, unfolding, querySame, ?_, ?_⟩
  · simpa only [same] using returned
  · intro work reader enoughWork enoughRead
    simpa only [same] using call_lift (numeric.2 work reader enoughWork enoughRead)

end MicroCFTA.SourceCurrentAllocatedConjunctionWorkerActual
