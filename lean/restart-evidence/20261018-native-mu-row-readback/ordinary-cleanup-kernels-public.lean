import MicroCFTA.SourceCurrentNativeConstructReaderReadback
import MicroCFTA.SourceCurrentNativeMuHistory

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace MicroCFTA.OrdinaryCleanupKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentNativeMuPublication (History)
open InternedBinderProtocol (Reference)
local notation "Heap" => State Nat Unit

private def old : Reference := .intersection 0 1
private def captures : List (Value Nat Unit) := [.reference old]
private def expression : Syntax Nat Unit := .union [.var 0,.node [.mk 7 () []]]
private def source := InternedFreshOrdinaryConstruction.build expression captures (empty : Heap)
private def body : Value Nat Unit := match source with
  | .done value _ => value
  | .pending _ _ => .empty
private def before : Heap := source.state
private def constructed := SourceRecursiveIntersectionMaybeMu.construct old body before
private def value : Value Nat Unit := match constructed with
  | .done value _ => value
  | .pending _ _ => .empty
private def after : Heap := constructed.state
private def row : EdgeValue Nat Unit := (run (makeEdge 7 () []) (empty : Heap)).1
private def reader : Heap := (run (makeEdge 99 () []) after).2

private theorem source_done : source = .done body before := by cbv
private theorem construct_done : constructed = .done value after := by cbv
private theorem pair_used : old ∈ body.free := by cbv; exact List.mem_cons_self
private theorem selected_row : (nodeEdges value)[0]? = some row := by cbv
private theorem maybe_done : SourceRecursiveIntersectionMaybeMu.maybeMu (0,1) body before = .done value after := by
  have used : Reference.intersection 0 1 ∈ body.free := pair_used
  simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu,used,ite_true,constructed,old] using construct_done

private theorem capture_available : Available (empty : Heap) (.reference old) := by
  apply reference_available
  intro identity impossible
  simp only [old,Value.free,List.mem_singleton] at impossible
  cases impossible

private theorem initial_context : SourceCurrentConstrainedCapSourceHistory.Context (empty : Heap) captures := by
  refine ⟨SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap
    captures ?_,InternedFreshOrdinaryDepthHeap.empty_heap⟩
  intro child member
  have same : child = .reference old := by simpa only [captures,List.mem_singleton] using member
  subst child
  exact capture_available

private theorem initial_semantic : SemanticHeap before := by
  have context := initial_context.build expression
  refine ⟨⟨context.base.normal,?_,context.base.profiles,context.base.freeNames⟩,context.depth⟩
  intro child member
  cases member

private theorem body_available : Available before body :=
  (InternedFreshOrdinaryFacts.build_verified expression captures empty
    initial_context.base.normal.facts initial_context.base.inputs).result body before source_done

private noncomputable def source_history : History (empty : Heap) before :=
  Classical.choice (SourceCurrentNativeMuPublication.build_history expression captures empty initial_context)

private noncomputable def construct_history : History before after :=
  Classical.choice (SourceCurrentNativeMuHistory.construct old body before initial_semantic body_available)

private theorem reader_growth : Grows after reader := by
  have checked := SourceRecursiveIntersectionMaybeMu.verified (0,1) body before
    initial_semantic.1.normal.facts body_available
  have facts : InternedNestedFacts.Facts after := by
    simpa only [maybe_done,Outcome.state] using checked.facts
  exact (run_correct (makeEdge 99 () []) after facts.coherent.valid).2

private noncomputable def reader_history : History (empty : Heap) reader :=
  .trans source_history (.trans construct_history (.retain after reader (fun _ _ _ _ _ present => present)))

/-- A used pair cleans up to an ordinary row and retains readback after a later allocation. -/
theorem used_pair_ordinary_row :
    source = .done body before ∧ SemanticHeap before ∧ Available before body ∧
    old ∈ body.free ∧ constructed = .done value after ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu (0,1) body before = .done value after ∧
    reader.edges.next = after.edges.next + 1 ∧ Grows after reader ∧
    Nonempty (History (empty : Heap) reader) ∧ (nodeEdges value)[0]? = some row ∧
    row.entry.key.symbol = 7 ∧ row.entry.key.constraint = () ∧ row.children = [] ∧
    SourceCurrentNativeConstructReaderReadback.RowReadback old body before value after reader 0 row ∧
    SourceRecursiveIntersectionMaybeMu.construct old body reader = .done value reader := by
  have readback := SourceCurrentNativeConstructReaderReadback.construct_row old body before initial_semantic
    body_available value after construct_done reader reader_history reader_growth 0 row selected_row
  have replay := SourceRecursiveIntersectionMaybeMu.replay (0,1) body before after reader
    initial_semantic.1.normal.facts body_available value maybe_done reader_growth
  have warm : SourceRecursiveIntersectionMaybeMu.construct old body reader = .done value reader := by
    have used : Reference.intersection 0 1 ∈ body.free := pair_used
    simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu,used,ite_true,old] using replay
  exact ⟨source_done,initial_semantic,body_available,pair_used,construct_done,maybe_done,
    by cbv,reader_growth,⟨reader_history⟩,selected_row,by cbv,rfl,rfl,readback,warm⟩

end MicroCFTA.OrdinaryCleanupKernels

#check @MicroCFTA.OrdinaryCleanupKernels.used_pair_ordinary_row
#print MicroCFTA.OrdinaryCleanupKernels.used_pair_ordinary_row
#print axioms MicroCFTA.OrdinaryCleanupKernels.used_pair_ordinary_row
