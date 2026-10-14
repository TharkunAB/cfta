import MicroCFTA.SourceRecursiveIntersectionRelatedRows
import MicroCFTA.SourceRecursiveIntersectionNativeOrdinaryRows

/-!
# Actual native ordinary calls supply related physical rows

Checked native execution derives local related rows at every larger kernel
bound and later valid cache. Related children are actual completed calls in
the retained source domain. Mu and union closure of this local relation
remain separate obligations.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourcePreparedSharedRows (interpretedEdge)

/-- A completed checked native ordinary branch derives local related-row soundness and completeness without a child-value projection. -/
theorem native_ordinary_related_rows [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (target : Automaton (Value Symbol Guard) Symbol) (empty : target .empty = []) :
    ∃ bound, ∀ extra (view : Machine Symbol Guard), SourceRecursiveIntersectionKernel.Valid view → Extension after.machine view →
      let related := fun pair child => SourceRecursiveIntersectionKernel.execute emptyGuard conjoin (bound + extra)
        domain pair.1 pair.2 view = .done child view
      let originals := Language.intersect (fun (_ : Value Symbol Guard) => leftEdges.map (interpretedEdge holds))
        (fun (_ : Value Symbol Guard) => rightEdges.map (interpretedEdge holds)) (.empty, .empty)
      (∀ edge ∈ (nodeEdges value).map (interpretedEdge holds), ∃ original ∈ originals, RelatedRows.Match related original edge) ∧
        (∀ original ∈ originals,
          (∃ children, All₂ related original.children children ∧ ∃ child ∈ children, target child = []) ∨
          ∃ edge ∈ (nodeEdges value).map (interpretedEdge holds), RelatedRows.Match related original edge) := by
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ state after value done
  obtain ⟨_, earlier, _, bound, completed⟩ := native_node_correct emptyGuard conjoin fuel _ state after value valid ready done
    (evaluated.bounds_of_ranges ranges)
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
  have leftResident : ∀ edge ∈ leftEdges, EdgeResident view.heap edge := fun edge member =>
    edge_grows _ _ totalGrowth.heap _ (valid.machine.1.linked leftEntry.key _ (ready.2.1.resident leftEntry rfl) edge member)
  have rightResident : ∀ edge ∈ rightEdges, EdgeResident view.heap edge := fun edge member =>
    edge_grows _ _ totalGrowth.heap _ (valid.machine.1.linked rightEntry.key _ (ready.2.2.resident rightEntry rfl) edge member)
  exact node_related_product_rows emptyGuard conjoin _ (execute_checked emptyGuard conjoin (bound + extra)) (execute_replay emptyGuard conjoin (bound + extra))
    domain leftEdges rightEdges view viewValid (ready.1.grows domain totalGrowth) leftResident rightResident value view returned holds conjoined target empty

end MicroCFTA.SourceRecursiveIntersectionNative
