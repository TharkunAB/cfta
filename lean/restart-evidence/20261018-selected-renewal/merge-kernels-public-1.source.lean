import MicroCFTA.SourceCurrentMergePositiveRowOrigins
import MicroCFTA.SourceCurrentMemoMergeWorkerProofs
import MicroCFTA.InternedFreshOrdinaryCosts
set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.MergePositiveRowKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentMemoMergeGraph
open SourceCurrentMergePositiveRowOrigins
local notation "Node" => Value Nat Nat
local notation "Edge" => EdgeValue Nat Nat

private def expression : InternedNestedConstruction.Syntax Nat Nat :=
  .node [.mk 7 9 [.node [.mk 8 1 [],.mk 8 2 [],.mk 8 3 [],.mk 8 4 [],.mk 8 5 []]]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def input : Node := match built with | .done value _ => value | _ => .empty
private def heap := built.state
private def clear : Nat → Bool := fun _ => false
private def cold := SourceCurrentMemoMergeWorker.call clear 0 64 0 input heap SourceCurrentMemoMergeGraph.empty
private def output : Node := match cold with | .done value _ _ => value | _ => .empty
private def after := cold.heap
private def saved := cold.memo
private def warm := SourceCurrentMemoMergeWorker.call clear 0 1 0 input after saved
private def row : Edge := (nodeEdges output)[0]?.getD (run (makeEdge 99 99 []) heap).1

private theorem built_done : built = .done input heap := by cbv
private theorem semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression input heap built_done
private theorem available : Available heap input :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result input heap built_done
private theorem costs : InternedFreshOrdinaryCostHeap.Heap heap := by
  simpa only [built,heap] using InternedFreshOrdinaryCosts.closed_heap expression
private theorem cold_done : cold = .done output after saved := by
  have tag : (match cold with | .done .. => true | _ => false) = true := by cbv
  cases found : cold <;> simp_all only [output,after,saved,SourceCurrentMemoMergeWorker.Outcome.heap,
    SourceCurrentMemoMergeWorker.Outcome.memo,Bool.false_eq_true]
private theorem warm_done : warm = .done output after saved := by cbv
private theorem cold_graph : Call clear 0 input heap SourceCurrentMemoMergeGraph.empty output after saved :=
  SourceCurrentMemoMergeWorkerProofs.call_sound cold_done
private theorem warm_graph : Call clear 0 input after saved output after saved :=
  SourceCurrentMemoMergeWorkerProofs.call_sound warm_done
private theorem initial_raw : Raw clear 0 (SourceCurrentMemoMergeGraph.empty : Memo Nat Nat) := by
  intro key entry absent
  cases absent
private theorem selected : row ∈ nodeEdges output :=
  List.mem_of_getElem? (show (nodeEdges output)[0]? = some row by cbv)
private theorem nonTop : row.entry.key.constraint ≠ 0 := by cbv

private def Claim : Prop :=
  ∃ (program : InternedNestedConstruction.Syntax Nat Nat) (original result : Node)
      (initial final : State Nat Nat) (memo : Memo Nat Nat) (returned : Edge),
    InternedFreshOrdinaryConstruction.build program [] empty = .done original initial ∧
    SourceEqualityRequiredSemanticCache.SemanticReady initial ∧ Available initial original ∧
    SourceCurrentMemoMergeWorker.call clear 0 64 0 original initial SourceCurrentMemoMergeGraph.empty =
      .done result final memo ∧
    SourceCurrentMemoMergeWorker.call clear 0 1 0 original final memo = .done result final memo ∧
    Raw clear 0 memo ∧ Writer clear 0 original result ∧
    returned ∈ nodeEdges result ∧ returned.entry.key.constraint ≠ 0 ∧
    result ≠ original ∧ returned.children.length = 1 ∧
    (∃ (sourceIndex : Nat) (source : Edge), (nodeEdges original)[sourceIndex]? = some source ∧
      returned.entry.key.symbol = source.entry.key.symbol ∧
      returned.entry.key.constraint = source.entry.key.constraint ∧ returned.children ≠ source.children ∧
      ∃ before current after saved,
        Run clear 0 (map Code.request source.children) before current returned.children after saved) ∧
    (∃ (sourceIndex : Nat) (source : Edge), (nodeEdges original)[sourceIndex]? = some source ∧
      returned.entry.key.symbol = source.entry.key.symbol ∧
      returned.entry.key.constraint = source.entry.key.constraint ∧ returned.children ≠ source.children ∧
      ∃ before current after saved,
        Run clear 0 (map Code.request source.children) before current returned.children after saved)

private theorem checked_witness : Claim := by
  have physical := SourceCurrentMemoMergeEffects.call_effects cold_graph semantic costs
    (SourceCurrentMemoMergeEffects.stored_empty heap) available
  obtain ⟨raw,firstWriter⟩ := SourceCurrentMergePositiveRowOrigins.call cold_graph semantic costs
    (SourceCurrentMemoMergeEffects.stored_empty heap) initial_raw available
  obtain ⟨_sameRaw,lastWriter⟩ := SourceCurrentMergePositiveRowOrigins.call warm_graph physical.1.semantic
    physical.1.costs physical.2.1 raw (physical.1.keeps.available input available)
  have origins (writer : Writer clear 0 input output) :
      ∃ (sourceIndex : Nat) (source : Edge), (nodeEdges input)[sourceIndex]? = some source ∧
        row.entry.key.symbol = source.entry.key.symbol ∧ row.entry.key.constraint = source.entry.key.constraint ∧
        row.children ≠ source.children ∧ ∃ before current after saved,
          Run clear 0 (map Code.request source.children) before current row.children after saved := by
    obtain ⟨index,source,found,symbol,guard,unchangedOrCalls⟩ :=
      SourceCurrentMergePositiveRowOrigins.positive writer row selected nonTop
    have singleton : nodeEdges input = [(nodeEdges input)[0]?.getD row] := by cbv
    have sourceOnly : source = (nodeEdges input)[0]?.getD row := by
      have member := List.mem_of_getElem? found
      rw [singleton] at member
      exact List.mem_singleton.mp member
    have different : row.children ≠ source.children := by
      rw [sourceOnly]
      cbv
      intro impossible
      cases impossible
    rcases unchangedOrCalls with same | calls
    · exact (different (congrArg EdgeValue.children same)).elim
    · exact ⟨index,source,found,symbol,guard,different,calls⟩
  have different : output ≠ input := by
    intro same
    have identities := congrArg Value.referenceOf same
    cbv at identities
    cases identities
  exact ⟨expression,input,output,heap,after,saved,row,built_done,semantic,available,cold_done,warm_done,
    raw,lastWriter,selected,nonTop,different,by cbv,origins firstWriter,origins lastWriter⟩

/-- Actual cold and warm calls retain a non-Top source row while its nonempty child changes. -/
theorem actual_cold_and_warm :
  ∃ (program : InternedNestedConstruction.Syntax Nat Nat) (original result : Node)
      (initial final : State Nat Nat) (memo : Memo Nat Nat) (returned : Edge),
    InternedFreshOrdinaryConstruction.build program [] empty = .done original initial ∧
    SourceEqualityRequiredSemanticCache.SemanticReady initial ∧ Available initial original ∧
    SourceCurrentMemoMergeWorker.call clear 0 64 0 original initial SourceCurrentMemoMergeGraph.empty =
      .done result final memo ∧
    SourceCurrentMemoMergeWorker.call clear 0 1 0 original final memo = .done result final memo ∧
    Raw clear 0 memo ∧ Writer clear 0 original result ∧
    returned ∈ nodeEdges result ∧ returned.entry.key.constraint ≠ 0 ∧
    result ≠ original ∧ returned.children.length = 1 ∧
    (∃ (sourceIndex : Nat) (source : Edge), (nodeEdges original)[sourceIndex]? = some source ∧
      returned.entry.key.symbol = source.entry.key.symbol ∧
      returned.entry.key.constraint = source.entry.key.constraint ∧ returned.children ≠ source.children ∧
      ∃ before current after saved,
        Run clear 0 (map Code.request source.children) before current returned.children after saved) ∧
    (∃ (sourceIndex : Nat) (source : Edge), (nodeEdges original)[sourceIndex]? = some source ∧
      returned.entry.key.symbol = source.entry.key.symbol ∧
      returned.entry.key.constraint = source.entry.key.constraint ∧ returned.children ≠ source.children ∧
      ∃ before current after saved,
        Run clear 0 (map Code.request source.children) before current returned.children after saved) := checked_witness

end MicroCFTA.MergePositiveRowKernels

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.MergePositiveRowKernels.actual_cold_and_warm
#print MicroCFTA.MergePositiveRowKernels.actual_cold_and_warm
#print axioms MicroCFTA.MergePositiveRowKernels.actual_cold_and_warm
