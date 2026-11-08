import MicroCFTA.SourceCurrentConjunctionFirstDemands
import MicroCFTA.SourceCurrentConjunctionExposureResources

set_option autoImplicit false

/-!
The original operand support bounds allocations from successful demanded
reads. Compression retains the actual final heap and every returned row
list. The bound counts first demands. It does not change tuple width or
bound repeated scans. A failing last read is not removed or bounded here.
-/
namespace MicroCFTA.SourceCurrentConjunctionFirstDemandResources
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionCompletionReads (Exposures)
open SourceCurrentConjunctionExposureResources (forecast)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Initial support resources control the exact final heap of repeated successful demands. -/
theorem bounded {demands : List Node} {before after : State Symbol Guard} {rows : List (List Edge)}
    (actual : Exposures demands before rows after) (support : List Node)
    (included : ∀ node ∈ demands, node ∈ support) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before support) (closed : ClosedValues support) (fits : Fits resource before) :
    ∃ nodes compactRows, Exposures nodes before compactRows after ∧ nodes.Nodup ∧
      (∀ node, node ∈ nodes ↔ node ∈ demands) ∧ nodes.length ≤ support.length ∧
      Fits (forecast support.length resource) after ∧
      (∀ row ∈ rows, row.length ≤ forecast support.length resource) ∧
      (∀ row ∈ rows, row ∈ compactRows) ∧
      (∀ operations fuel, SourceCurrentProjectionUnionResources.readFuel (forecast support.length resource) ≤ fuel →
        SourceCurrentConjunctionRowsWorker.exposures fuel nodes ⟨before, operations⟩ =
          .done compactRows ⟨after, operations⟩) := by
  have valid := semantic.ready.semantic.1.normal.facts.coherent.valid
  obtain ⟨nodes, compact, compressed, distinct, members, length, covered⟩ :=
    SourceCurrentConjunctionFirstDemands.compress_supported actual valid support included
  have inputs : Values before nodes := by
    intro node member
    exact available node (included node ((members node).mp member))
  have closedInputs : ClosedValues nodes := by
    intro node member
    exact closed node (included node ((members node).mp member))
  have numeric := SourceCurrentConjunctionExposureResources.bounded compressed support.length resource
    semantic costs inputs closedInputs fits length
  exact ⟨nodes, compact, compressed, distinct, members, length, numeric.1,
    (fun row member => numeric.2.2.1 row (covered row member)), covered, numeric.2.2.2⟩

end MicroCFTA.SourceCurrentConjunctionFirstDemandResources
