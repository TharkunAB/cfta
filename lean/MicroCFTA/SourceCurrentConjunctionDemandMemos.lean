import MicroCFTA.SourceCurrentConjunctionDemandCompletion
import MicroCFTA.SourceCurrentConjunctionDemandSoundness
import MicroCFTA.SourceCurrentConjunctionGlobalMemos
import MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity

/-!
# Global memo receipts for actual demand admission

Sampling receipts retain the complete actual demand list. Repeated reads
remain separate occurrences. Positive admission passes the sampled memo
bundle to its actual tuple allocation. The proofs retain the exact returned
bundle and do not replace demand with a compressed exposure schedule.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandMemos
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionRowsAllocation (Ready Effects Tuples)
open SourceCurrentConjunctionDemandExecution (Admission)
open SourceCurrentConjunctionCompletionReads (Exposures)
open SourceCurrentConjunctionGlobalMemos (ExposuresReads TuplesReads)
open SourceCurrentConjunctionTuplePull (start)
open SourceCurrentConjunctionTuplePullReadTrace (demands)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A finite successful observation fixes every logical sampling read occurrence. -/
inductive SampleReads : {h budget : Nat} → {nodes : List Node} → {before after : Physical} →
    {result : SourceCurrentConjunctionTuplePullTotal.Result Symbol FullSyntax.Formula} →
    (SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after) →
    Memos → Memos → Prop where
  | run {h budget : Nat} {nodes : List Node} {before after : Physical}
      {result : SourceCurrentConjunctionTuplePullTotal.Result Symbol FullSyntax.Formula}
      {actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after}
      {rows : List (List Edge)} {memos saved : Memos} (steps : Nat)
      (observed : SourceCurrentConjunctionTuplePullAdmission.drive steps h budget (start nodes) [] before =
        .done result.toStatus after)
      (exposed : Exposures (demands steps h budget (start nodes) [] before) before.heap rows after.heap)
      (calls : ExposuresReads exposed memos saved) : SampleReads actual memos saved

/-- Only positive admission adds allocated requirement reads after sampling. -/
inductive AdmissionReads : {budget : Nat} → {nodes : List Node} → {before after : Physical} →
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol FullSyntax.Formula} →
    Admission budget nodes before result after → Memos → Memos → Prop where
  | overflow (calls : SampleReads sampled memos saved) :
      AdmissionReads (.overflow sampled) memos saved
  | zero (calls : SampleReads sampled memos saved) :
      AdmissionReads (.zero sampled) memos saved
  | positive (sampleCalls : SampleReads sampled memos middleMemo)
      (allocatedCalls : TuplesReads allocated middleMemo saved) :
      AdmissionReads (.positive sampled allocated) memos saved

/-- Actual sampling derives memo calls in its full demand order and exact final heap. -/
theorem sample_memos {h budget : Nat} {nodes : List Node} {before after : Physical}
    {result : SourceCurrentConjunctionTuplePullTotal.Result Symbol FullSyntax.Formula}
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after)
    (semantic : SemanticReady before.heap) (costs : CostHeap before.heap) (available : Values before.heap nodes)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, SampleReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  obtain ⟨steps, eventual⟩ := SourceCurrentConjunctionTuplePullTotal.sample_observation h budget nodes before
  have observed := eventual 0
  simp only [Nat.add_zero, actual, SourceCurrentConjunctionTuplePullTotal.observe,
    SourceCurrentConjunctionTuplePullAdmission.sample] at observed
  obtain ⟨rows, exposed⟩ := SourceCurrentConjunctionTuplePullReadTrace.drive_reads
    steps h budget (start nodes) [] before after result.toStatus observed
  have included := SourceCurrentConjunctionTuplePullReadTrace.demands_supported
    steps h budget (start nodes) [] before nodes
    (SourceCurrentConjunctionTuplePullReads.start_supported nodes)
  obtain ⟨saved, calls, coherent, retained, same⟩ :=
    SourceCurrentConjunctionGlobalMemos.exposures_memos exposed semantic costs
      (fun node member => available node (included node member)) memos valid
  exact ⟨saved, .run steps observed exposed calls, coherent, retained, same⟩

/-- Supplied sampling calls preserve their own returned memo bundle. -/
theorem sample_valid {h budget : Nat} {nodes : List Node} {before after : Physical}
    {result : SourceCurrentConjunctionTuplePullTotal.Result Symbol FullSyntax.Formula}
    {actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after}
    {memos saved : Memos} (reads : SampleReads actual memos saved)
    (semantic : SemanticReady before.heap) (costs : CostHeap before.heap) (available : Values before.heap nodes)
    (valid : Valid before.heap memos) :
    Valid after.heap saved ∧ Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases reads with
  | run steps observed exposed calls =>
      have included := SourceCurrentConjunctionTuplePullReadTrace.demands_supported
        steps h budget (start nodes) [] before nodes
        (SourceCurrentConjunctionTuplePullReads.start_supported nodes)
      exact SourceCurrentAllocatedConjunctionReadValidity.exposures calls semantic costs
        (fun node member => available node (included node member)) valid

private theorem fit_inputs {h budget : Nat} {nodes : List Node} {before middle : Physical}
    {tuples : List (List Edge)}
    {actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done (.fit tuples) middle}
    {memos saved : Memos} (_reads : SampleReads actual memos saved) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    Effects before middle ∧ (∀ tuple ∈ tuples, Edges middle.heap tuple) ∧
      (∀ tuple ∈ tuples, ClosedEdges tuple) := by
  have checked := SourceCurrentConjunctionTuplePullTotalEffects.sample_effects h budget nodes before ready available
  refine ⟨?_, checked.2 (.fit tuples) middle actual,
    SourceCurrentConjunctionTuplePullClosedSample.sample_fit h budget nodes before middle tuples actual
      ready available closed⟩
  simpa only [actual, SourceCurrentConjunctionRowsWorker.Outcome.state] using checked.1

/-- Actual admission derives its returned memos without extra or compressed logical reads. -/
theorem admission_memos {budget : Nat} {nodes : List Node} {before after : Physical}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol FullSyntax.Formula}
    (actual : Admission budget nodes before result after) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (memos : Memos) (valid : Valid before.heap memos) :
    ∃ saved, AdmissionReads actual memos saved ∧ Valid after.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  obtain ⟨h, sampled, middle, _readNodes, _views, sampleActual, _exposed, _included, _equality, aligned⟩ :=
    actual.demand_reads
  obtain ⟨middleMemo, sampleCalls, coherent, retained, same⟩ :=
    sample_memos sampleActual ready.semantic ready.costs available memos valid
  cases result with
  | overflow =>
      cases sampled with
      | fit tuples => exact False.elim aligned
      | overflow tuples cursor =>
          change middle = after at aligned
          subst middle
          exact ⟨middleMemo, .overflow sampleCalls, coherent, retained, same⟩
  | zero =>
      cases sampled with
      | overflow tuples cursor => exact False.elim aligned
      | fit tuples =>
          cases tuples with
          | nil =>
              change middle = after at aligned
              subst middle
              exact ⟨middleMemo, .zero sampleCalls, coherent, retained, same⟩
          | cons first rest => exact False.elim aligned
  | positive predecessor requirements =>
      cases sampled with
      | overflow tuples cursor => exact False.elim aligned
      | fit tuples =>
          obtain ⟨count, allocated⟩ := aligned
          cases tuples with
          | nil => simp only [List.length_nil] at count; omega
          | cons first rest =>
              have predecessorEq : rest.length = predecessor := by
                simp only [List.length_cons] at count
                omega
              subst predecessor
              have own := fit_inputs sampleCalls ready available closed
              obtain ⟨saved, calls, finalValid, finalRetained, finalSame⟩ :=
                SourceCurrentConjunctionGlobalMemos.tuples_memos allocated own.1.ready own.2.1 own.2.2
                  middleMemo coherent
              exact ⟨saved, .positive sampleCalls calls, finalValid,
                extends_trans retained finalRetained, finalSame.trans same⟩

/-- Supplied admission histories preserve that exact returned bundle at the actual heap. -/
theorem admission_valid {budget : Nat} {nodes : List Node} {before after : Physical}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol FullSyntax.Formula}
    {actual : Admission budget nodes before result after} {memos saved : Memos}
    (reads : AdmissionReads actual memos saved) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) (valid : Valid before.heap memos) :
    Valid after.heap saved ∧ Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases reads with
  | overflow calls => exact sample_valid calls ready.semantic ready.costs available valid
  | zero calls => exact sample_valid calls ready.semantic ready.costs available valid
  | positive sampleCalls allocatedCalls =>
      have first := sample_valid sampleCalls ready.semantic ready.costs available valid
      have own := fit_inputs sampleCalls ready available closed
      have later := SourceCurrentAllocatedConjunctionReadValidity.tuples allocatedCalls own.1.ready
        own.2.1 own.2.2 first.1
      exact ⟨later.1, extends_trans first.2.1 later.2.1, later.2.2.trans first.2.2⟩

end MicroCFTA.SourceCurrentConjunctionDemandMemos
