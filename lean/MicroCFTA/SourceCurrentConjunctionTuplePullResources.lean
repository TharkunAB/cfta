import MicroCFTA.SourceCurrentConjunctionTuplePullReadTrace
import MicroCFTA.SourceCurrentConjunctionFirstDemandResources

/-!
# Original-support resources for actual physical tuple sampling

The actual total sampler supplies its read trace. First-demand compression
then bounds its returned constructor heap by the original operand count.
The receipt retains that exact heap and every original row list. This proof
does not bound scan work or the state of a failed final read.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullResources
open InternedConstructorTemplates
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConjunctionRowsWorker (Physical)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionCompletionReads (Exposures)
open SourceCurrentConjunctionExposureResources (forecast)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Actual sampling derives a bounded distinct-demand receipt at its exact returned heap. -/
theorem sample_resources (h budget : Nat) (nodes : List Node) (before after : Physical Symbol Formula)
    (result : SourceCurrentConjunctionTuplePullTotal.Result Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after)
    (resource : Nat) (ready : Ready before) (available : Values before.heap nodes)
    (closed : ClosedValues nodes) (fits : Fits resource before.heap) :
    ∃ reads rows, Exposures reads before.heap rows after.heap ∧ reads.Nodup ∧
      reads.length ≤ nodes.length ∧ (∀ node ∈ reads, node ∈ nodes) ∧
      Fits (forecast nodes.length resource) after.heap ∧
      (∀ row ∈ rows, row.length ≤ forecast nodes.length resource) := by
  letI : DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula)) :=
    fun left right => Classical.propDecidable (left = right)
  obtain ⟨demanded, originalRows, receipt, supported⟩ :=
    SourceCurrentConjunctionTuplePullReadTrace.sample_reads h budget nodes before after result actual
  obtain ⟨reads, rows, compressed, distinct, members, length, bounded, _width, _coverage, _replay⟩ :=
    SourceCurrentConjunctionFirstDemandResources.bounded receipt nodes supported resource
      ready.semantic ready.costs available closed fits
  have inputs : Values before.heap reads := by
    intro node member
    exact available node (supported node ((members node).mp member))
  have noFree : ClosedValues reads := by
    intro node member
    exact closed node (supported node ((members node).mp member))
  have numeric := SourceCurrentConjunctionExposureResources.bounded compressed nodes.length resource
    ready.semantic ready.costs inputs noFree fits length
  exact ⟨reads, rows, compressed, distinct, length,
    fun node member => supported node ((members node).mp member), bounded, numeric.2.2.1⟩

/-- Initial operand support bounds the returned heap of every successful total sample. -/
theorem sample_fits (h budget : Nat) (nodes : List Node) (before after : Physical Symbol Formula)
    (result : SourceCurrentConjunctionTuplePullTotal.Result Symbol Formula)
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after)
    (resource : Nat) (ready : Ready before) (available : Values before.heap nodes)
    (closed : ClosedValues nodes) (fits : Fits resource before.heap) :
    Fits (forecast nodes.length resource) after.heap := by
  obtain ⟨_, _, _, _, _, _, bounded, _⟩ :=
    sample_resources h budget nodes before after result actual resource ready available closed fits
  exact bounded

end MicroCFTA.SourceCurrentConjunctionTuplePullResources
