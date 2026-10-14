import MicroCFTA.SourceRecursiveIntersectionProductRowView
import MicroCFTA.SourceRecursiveIntersectionNativeRangeCertificate
import MicroCFTA.SourceRecursiveIntersectionNativeApi

/-!
# Physical product-row readback of completed native ordinary calls

The checked actual native run supplies a completed guarded kernel call.
Its ordinary branch derives the exact normalized synchronous rows. No
child-language, row-membership, or kernel-execution contract is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode SymbolicGraphView
open SourcePreparedSharedRows (interpretedEdge)

/-- A completed checked native ordinary branch derives normalized product rows at every larger bound and later valid cache. -/
theorem native_ordinary_product_rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (domain : Interned DomainKey)
    (leftEntry rightEntry : Interned NodeKey) (leftEdges rightEdges : List (EdgeValue Symbol Guard))
    (leftDepth rightDepth : Nat) (leftFree rightFree : List Reference)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine ⟨domain, .node leftEntry leftEdges leftDepth leftFree, .node rightEntry rightEdges rightDepth rightFree⟩)
    (ordinary : SourceRecursiveIntersectionControl.decision domain.key (.node leftEntry leftEdges leftDepth leftFree)
      (.node rightEntry rightEdges rightDepth rightFree) = .ordinary)
    (done : execute emptyGuard conjoin fuel
      (.node ⟨domain, .node leftEntry leftEdges leftDepth leftFree, .node rightEntry rightEdges rightDepth rightFree⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin
      (.node ⟨domain, .node leftEntry leftEdges leftDepth leftFree, .node rightEntry rightEdges rightDepth rightFree⟩ .pure) state)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∃ bound, ∀ extra (view : Machine Symbol Guard), SourceRecursiveIntersectionKernel.Valid view → Extension after.machine view →
      let call := SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra)
      let meet := childValue call domain view
      let keep := keepProduct call domain view
      (∀ row, row ∈ (nodeEdges value).map (interpretedEdge holds) ↔
        ∃ original ∈ Language.intersect (fun (_ : Value Symbol Guard) => leftEdges.map (interpretedEdge holds))
          (fun (_ : Value Symbol Guard) => rightEdges.map (interpretedEdge holds)) (.empty, .empty),
          keep original = true ∧ row = renameEdge meet original) ∧
      (∀ target : Automaton (Value Symbol Guard) Symbol, target .empty = [] → ∀ original,
        original ∈ Language.intersect (fun (_ : Value Symbol Guard) => leftEdges.map (interpretedEdge holds))
          (fun (_ : Value Symbol Guard) => rightEdges.map (interpretedEdge holds)) (.empty, .empty) →
        keep original = false → DropReason target meet original) := by
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ state after value done
  have bounds := evaluated.bounds_of_ranges ranges
  obtain ⟨_, earlier, _, bound, completed⟩ := native_node_correct emptyGuard conjoin fuel _ state after value valid ready done bounds
  refine ⟨bound, ?_⟩
  intro extra view viewValid growth
  have returned := SourceRecursiveIntersectionKernel.execute_larger_replay emptyGuard conjoin (bound + 1) extra domain
    (.node leftEntry leftEdges leftDepth leftFree) (.node rightEntry rightEdges rightDepth rightFree) state.machine view
    valid.machine ready.1 ready.2.1 ready.2.2 value after.machine (completed 1) growth
  rw [Nat.add_right_comm bound 1 extra] at returned
  change onNode emptyGuard conjoin (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra)) domain
    (.node leftEntry leftEdges leftDepth leftFree) (.node rightEntry rightEdges rightDepth rightFree) view = .done value view at returned
  simp only [onNode, ordinary] at returned
  have totalGrowth := earlier.trans growth
  have leftResident : ∀ edge ∈ leftEdges, EdgeResident view.heap edge := by
    intro edge member
    exact edge_grows _ _ totalGrowth.heap _ (valid.machine.1.linked leftEntry.key _ (ready.2.1.resident leftEntry rfl) edge member)
  have rightResident : ∀ edge ∈ rightEdges, EdgeResident view.heap edge := by
    intro edge member
    exact edge_grows _ _ totalGrowth.heap _ (valid.machine.1.linked rightEntry.key _ (ready.2.2.resident rightEntry rfl) edge member)
  constructor
  · intro row
    exact node_product_members emptyGuard conjoin _ (execute_checked emptyGuard conjoin (bound + extra)) (execute_replay emptyGuard conjoin (bound + extra))
      domain leftEdges rightEdges view viewValid (ready.1.grows domain totalGrowth) leftResident rightResident value view returned holds conjoined row
  · intro target empty original member rejected
    exact node_product_rejected emptyGuard conjoin _ (execute_checked emptyGuard conjoin (bound + extra)) (execute_replay emptyGuard conjoin (bound + extra))
      domain leftEdges rightEdges view viewValid (ready.1.grows domain totalGrowth) leftResident rightResident value view returned holds target empty original member rejected

end MicroCFTA.SourceRecursiveIntersectionNative
