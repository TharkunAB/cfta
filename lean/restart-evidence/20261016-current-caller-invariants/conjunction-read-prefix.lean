import MicroCFTA.SourceCurrentAllocatedReadDeterminism
import MicroCFTA.SourceCurrentConjunctionGlobalMemos

/-!
# Validity of supplied current conjunction read receipts

Each theorem uses the supplied operational read graph. Actual physical
effects derive the inputs for its next read. The proof retains the exact
returned global bundle. It does not compare different read schedules.
-/
namespace MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionCompletionReads (Exposures Projections Inputs jobs)
open SourceCurrentConjunctionRequirements (ClassRequirements Requirements)
open SourceCurrentConjunctionRowsAllocation (Tuple Tuples Rows Ready)
open SourceCurrentConjunctionWorklist (Run PendingReady)
open SourceCurrentConjunctionGlobalMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A supplied completed exposure derives coherence for its own saved bundle. -/
theorem read
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    {actual : SourceEqualityProjectionRead.Read value before edges after} {memos final : Memos}
    (reads : ReadReads actual memos final) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  rcases reads with ⟨calls, same⟩
  cases calls with
  | @done fuel value before after edges completed memo saved calls =>
      simpa only [completed, MergedSourceExposure.Result.state] using
        SourceCurrentAllocatedReadDeterminism.exposure ⟨calls, same⟩ semantic costs available valid

/-- The actual exposure prefix derives each following original operand's residency. -/
theorem exposures
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {edges : List (List (EdgeValue Symbol Guard))} {actual : Exposures values before edges after}
    {memos final : Memos} (reads : ExposuresReads actual memos final)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (valid : Valid before memos) :
    Valid after final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  induction reads with
  | nil => exact ⟨valid, extends_refl _, rfl⟩
  | @cons value before edges middle first memos middleMemo values more after rest final firstRead restRead ih =>
      have firstMemo := read firstRead semantic costs (available _ List.mem_cons_self) valid
      have own := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      have later := ih own.2.1 own.2.2.1
        (fun value member => own.1.available value (available value (List.mem_cons_of_mem _ member))) firstMemo.1
      exact ⟨later.1, extends_trans firstMemo.2.1 later.2.1, later.2.2.trans firstMemo.2.2⟩


end MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity
