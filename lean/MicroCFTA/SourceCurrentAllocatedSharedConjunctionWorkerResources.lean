import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorkerActual
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionOutcome
import MicroCFTA.SourceCurrentConjunctionSharedFixedAlphabetNumeric
import MicroCFTA.SourceCurrentConstrainedCapRequiredResources

/-!
# Computed resources for the checked shared conjunction worker

Current caller facts derive one successful call at explicit observation
ceilings. Its ordered reads and full Post use that same call. Larger
ceilings retain the answer, checked state, fourth memo and private snapshot.
A supplied success retains its own ordered receipt at its original bounds.
The native domain supply stays exact. Native capacity and runtime are separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorkerActual
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapTargetForecast (scalar)
open SourceCurrentAllocatedSharedConjunctionWorker
open SourceCurrentConjunctionSharedWorkerOutcomeMemos (CallReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Snapshot" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
local notation "Numeric" => SourceCurrentConjunctionSharedFixedAlphabetNumeric.forecast

/-- A fixed current guard inventory bounds the heap and retains the domain profile. -/
noncomputable def forecast_with_alphabet (alphabet : List Guard) (budget : Nat) (profile : Profile) : Profile :=
  let bound := Numeric alphabet budget (scalar profile)
  ⟨bound, bound, profile.domains, bound⟩

/-- The entry heap derives its own guard inventory for the complete shared forecast. -/
noncomputable def forecast (heap : State Symbol Guard) (budget : Nat) (profile : Profile) : Profile :=
  forecast_with_alphabet (guards heap) budget profile

/-- The original profile and tuple budget determine the shared projection ceiling. -/
noncomputable def projectionFuel (alphabet : List Guard) (budget : Nat) (profile : Profile) : Nat :=
  SourceCurrentConjunctionSharedFixedAlphabetNumeric.projectionFuel alphabet budget (scalar profile)

/-- The original profile and tuple budget determine the shared reader ceiling. -/
noncomputable def readerFuel (alphabet : List Guard) (budget : Nat) (profile : Profile) : Nat :=
  SourceCurrentConjunctionSharedFixedAlphabetNumeric.readerFuel alphabet budget (scalar profile)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- A current fixed alphabet supplies one computed call, its literal receipt and exact stable bounds. -/
theorem finite_resources_with_alphabet {inventory : Inventory} {before : Caller width}
    {query : Node} {memos : Memos} (alphabet : List Guard) (budget : Nat) (profile : Profile)
    (initial : Context formulas solver inventory before memos) (fits : Fits profile before.checked)
    (available : Available before.checked.native.machine.heap query)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ (answer : Bool) (after : Checked width) (saved : Memo) (snapshot : Snapshot) (final : Memos),
      call (projectionFuel alphabet budget profile) (readerFuel alphabet budget profile)
        budget query before.checked before.fourth = .done answer after saved snapshot ∧
      CallReads (projectionFuel alphabet budget profile) (readerFuel alphabet budget profile)
        budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      Available after.native.machine.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      Fits (forecast_with_alphabet alphabet budget profile) after ∧
      (∀ P H, projectionFuel alphabet budget profile ≤ P → readerFuel alphabet budget profile ≤ H →
        call P H budget query before.checked before.fourth = .done answer after saved snapshot) := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  have scalarFits := (SourceCurrentConstrainedCapRequiredResources.of_checked fits).scalar_fits
  obtain ⟨answer, saved, snapshot, stable, numeric⟩ :=
    SourceCurrentConjunctionSharedFixedAlphabetNumeric.call_bound alphabet budget before.fourth query
      (physical before.checked) (scalar profile) ready available scalarFits known
  let p := projectionFuel alphabet budget profile
  let h := readerFuel alphabet budget profile
  have raw := stable p h (Nat.le_refl _) (Nat.le_refl _)
  have checked := call_lift (before := before.checked) raw
  have received := SourceCurrentAllocatedSharedConjunctionOutcome.verified formulas solver
    p h budget before query memos initial available
  dsimp only at received
  rw [raw] at received
  dsimp only [SourceCurrentConjunctionSharedWorker.Outcome.state,
    SourceCurrentConjunctionSharedWorkerOutcomeMemos.returnedMemo] at received
  obtain ⟨final, reads, post, resident, retained, same, sound⟩ := received
  refine ⟨answer, advancePhysical before.checked snapshot.storage.requirements.physical, saved,
    snapshot, final, checked, reads, post, sound, resident, retained, same, ?_, ?_⟩
  · exact ⟨numeric.fits.nodes, numeric.fits.edges, fits.domains, numeric.fits.stored⟩
  · intro P H enoughP enoughH
    exact call_lift (stable P H enoughP enoughH)

/-- A supplied success retains its own receipt and all four literal components under the fixed forecast. -/
theorem raw_done_resources_with_alphabet {inventory : Inventory} {p h budget : Nat}
    {before : Caller width} {after : Checked width} {query : Node} {answer : Bool}
    {saved : Memo} {snapshot : Snapshot} {memos : Memos} (alphabet : List Guard) (profile : Profile)
    (initial : Context formulas solver inventory before memos) (fits : Fits profile before.checked)
    (available : Available before.checked.native.machine.heap query)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (done : call p h budget query before.checked before.fourth = .done answer after saved snapshot) :
    ∃ final, after = advancePhysical before.checked snapshot.storage.requirements.physical ∧
      CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      Available after.native.machine.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      Fits (forecast_with_alphabet alphabet budget profile) after ∧
      (∀ P H, projectionFuel alphabet budget profile ≤ P → readerFuel alphabet budget profile ≤ H →
        call P H budget query before.checked before.fourth = .done answer after saved snapshot) := by
  obtain ⟨baseAnswer, baseAfter, baseSaved, baseSnapshot, _baseFinal, canonical, _baseReads,
      _basePost, _baseSound, _baseAvailable, _baseExtends, _baseQuery, numeric, replay⟩ :=
    finite_resources_with_alphabet formulas solver alphabet budget profile initial fits available known
  have same := call_done_unique done canonical
  have returned : Fits (forecast_with_alphabet alphabet budget profile) after := same.2.1.symm ▸ numeric
  have stable : ∀ P H, projectionFuel alphabet budget profile ≤ P → readerFuel alphabet budget profile ≤ H →
      call P H budget query before.checked before.fourth = .done answer after saved snapshot := by
    intro P H enoughP enoughH
    simpa only [same.1, same.2.1, same.2.2.1, same.2.2.2] using replay P H enoughP enoughH
  obtain ⟨raw, advanced⟩ := call_done done
  have received := SourceCurrentAllocatedSharedConjunctionOutcome.verified formulas solver
    p h budget before query memos initial available
  dsimp only at received
  rw [raw] at received
  dsimp only [SourceCurrentConjunctionSharedWorker.Outcome.state,
    SourceCurrentConjunctionSharedWorkerOutcomeMemos.returnedMemo] at received
  obtain ⟨final, reads, post, resident, retained, querySame, sound⟩ := received
  refine ⟨final, advanced, reads, ?_, sound, ?_, retained, querySame, returned, stable⟩
  · simpa only [advanced] using post
  · rw [advanced]
    change Available (physical (advancePhysical before.checked snapshot.storage.requirements.physical)).heap query
    rw [SourceCurrentAllocatedQueryMemo.physical_advance]
    exact resident

/-- Context and the current heap profile derive the alphabet, computed call and full literal receipt. -/
theorem finite_resources {inventory : Inventory} {before : Caller width} {query : Node} {memos : Memos}
    (budget : Nat) (profile : Profile) (initial : Context formulas solver inventory before memos)
    (fits : Fits profile before.checked) (available : Available before.checked.native.machine.heap query) :
    ∃ (answer : Bool) (after : Checked width) (saved : Memo) (snapshot : Snapshot) (final : Memos),
      call (projectionFuel (guards before.checked.native.machine.heap) budget profile)
        (readerFuel (guards before.checked.native.machine.heap) budget profile)
        budget query before.checked before.fourth = .done answer after saved snapshot ∧
      CallReads (projectionFuel (guards before.checked.native.machine.heap) budget profile)
        (readerFuel (guards before.checked.native.machine.heap) budget profile)
        budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      Available after.native.machine.heap query ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      Fits (forecast before.checked.native.machine.heap budget profile) after ∧
      (∀ P H, projectionFuel (guards before.checked.native.machine.heap) budget profile ≤ P →
        readerFuel (guards before.checked.native.machine.heap) budget profile ≤ H →
        call P H budget query before.checked before.fourth = .done answer after saved snapshot) := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  exact finite_resources_with_alphabet formulas solver (guards before.checked.native.machine.heap)
    budget profile initial fits available
    (SourceCurrentConjunctionGuardUniverse.initial before.checked.native.machine.heap
      ready.semantic.ready.semantic.1.normal.facts)

/-- A supplied success derives its own receipt and current-entry forecast without extra heap invariants. -/
theorem raw_done_resources {inventory : Inventory} {p h budget : Nat}
    {before : Caller width} {after : Checked width} {query : Node} {answer : Bool}
    {saved : Memo} {snapshot : Snapshot} {memos : Memos} (profile : Profile)
    (initial : Context formulas solver inventory before memos) (fits : Fits profile before.checked)
    (available : Available before.checked.native.machine.heap query)
    (done : call p h budget query before.checked before.fourth = .done answer after saved snapshot) :
    ∃ final, after = advancePhysical before.checked snapshot.storage.requirements.physical ∧
      CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      Available after.native.machine.heap query ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      Fits (forecast before.checked.native.machine.heap budget profile) after ∧
      (∀ P H, projectionFuel (guards before.checked.native.machine.heap) budget profile ≤ P →
        readerFuel (guards before.checked.native.machine.heap) budget profile ≤ H →
        call P H budget query before.checked before.fourth = .done answer after saved snapshot) := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  exact raw_done_resources_with_alphabet formulas solver (guards before.checked.native.machine.heap)
    profile initial fits available
    (SourceCurrentConjunctionGuardUniverse.initial before.checked.native.machine.heap
      ready.semantic.ready.semantic.1.normal.facts) done

end MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorkerActual
