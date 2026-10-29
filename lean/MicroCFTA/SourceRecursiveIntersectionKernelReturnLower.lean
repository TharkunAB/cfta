import MicroCFTA.SourceRecursiveIntersectionKernelRowsLower
import MicroCFTA.SourceRecursiveIntersectionKernelUnionLower
import MicroCFTA.SourceRecursiveIntersectionKernelMuLower
import MicroCFTA.SourceRecursiveIntersectionCompileNodeBounds

/-!
# Original-input body bounds for every actual kernel outcome

Natural induction on runtime fuel supplies every recursive allocation bound.
The conclusion includes failure, exhaustion and pending construction.
Each complete Mu is an exact input record or has a body below the bound.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionCode InternedStoredPlanBinderDepthProgress
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Every actual original request outcome bounds all new complete Mu bodies. -/
theorem node_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) :
    ∀ (request : NodeRequest Symbol Guard) (_scope : NodeScope source request)
      (complete : Completes (view source holds) (nodeSemantic request))
      (state : Machine Symbol Guard),
      Valid state → NodeReady state request →
      Grows source state.heap → Extends source.nodes.issued state.heap.nodes.issued →
      SemanticHeap state.heap → InternedOpenDepthReadback.Heap state.heap →
      Lower state.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
        (execute emptyGuard conjoin fuel request.domain request.left request.right state).state.heap := by
  induction fuel with
  | zero =>
      intro request scope complete state valid ready growth history semantic opened
      exact lower_refl state.heap _
  | succ fuel ih =>
      intro request scope complete state valid ready growth history semantic opened
      cases request with
      | mk domain left right =>
          obtain ⟨known, leftAvailable, rightAvailable⟩ := ready
          let bound := requiredFuel (view source holds) (nodeSemantic ⟨domain, left, right⟩) complete
          have recurse (child : NodeRequest Symbol Guard) (below : NodeBelow source holds bound child)
              (childReady : NodeReady state child) :
              Lower state.heap (limit + bound)
                (execute emptyGuard conjoin fuel child.domain child.left child.right state).state.heap := by
            obtain ⟨childScope, childComplete, childLess⟩ := below
            exact (ih child childScope childComplete state valid childReady growth history semantic opened).mono
              (Nat.add_le_add_left (Nat.le_of_lt childLess) limit)
          simp only [execute]
          cases selected : decision domain.key left right with
          | empty | self | repeated | unsupported =>
              simpa only [onNode, selected, unsupported, Result.state] using lower_refl state.heap (limit + bound)
          | reset =>
              simp only [onNode, selected]
              apply recurse ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ ?_
                ⟨empty_domain state, leftAvailable, rightAvailable⟩
              apply node_child_below source facts holds _ _ scope complete (scope.reset source domain left right)
              simp only [selected, branchCalls, List.mem_singleton]
              rfl
          | swap =>
              simp only [onNode, selected]
              apply recurse ⟨domain, right, left⟩ ?_ ⟨known, rightAvailable, leftAvailable⟩
              apply node_child_below source facts holds _ _ scope complete (scope.swap source domain left right)
              simp only [selected, branchCalls, List.mem_singleton]
              rfl
          | bothMu =>
              simp only [onNode, selected]
              exact mu_lower source facts limit sourceBounded holds emptyGuard conjoin fuel ih
                ⟨domain, left, right⟩ scope complete (.inl selected) state valid
                ⟨known, leftAvailable, rightAvailable⟩ growth history semantic opened
          | leftMu =>
              simp only [onNode, selected]
              exact mu_lower source facts limit sourceBounded holds emptyGuard conjoin fuel ih
                ⟨domain, left, right⟩ scope complete (.inr (.inl selected)) state valid
                ⟨known, leftAvailable, rightAvailable⟩ growth history semantic opened
          | rightMu =>
              simp only [onNode, selected]
              exact mu_lower source facts limit sourceBounded holds emptyGuard conjoin fuel ih
                ⟨domain, left, right⟩ scope complete (.inr (.inr selected)) state valid
                ⟨known, leftAvailable, rightAvailable⟩ growth history semantic opened
          | leftUnion =>
              simp only [onNode, selected]
              cases left with
              | union entry members depth free =>
                  exact union_lower source facts limit sourceBounded holds emptyGuard conjoin fuel ih domain members right true bound
                    state valid known rightAvailable (fun child member => leftAvailable.children child member)
                    growth history semantic opened
                    (fun child member => leftUnion_member_below source facts holds domain entry members depth free right scope complete selected child member)
              | empty | reference | node | mu => exact lower_refl state.heap _
          | rightUnion =>
              simp only [onNode, selected]
              cases right with
              | union entry members depth free =>
                  exact union_lower source facts limit sourceBounded holds emptyGuard conjoin fuel ih domain members left false bound
                    state valid known leftAvailable (fun child member => rightAvailable.children child member)
                    growth history semantic opened
                    (fun child member => rightUnion_member_below source facts holds domain left entry members depth free scope complete selected child member)
              | empty | reference | node | mu => exact lower_refl state.heap _
          | leftReference =>
              simp only [onNode, selected]
              cases scope.left with
              | reference name =>
                  by_cases boundName : name ∈ names domain.key
                  · obtain ⟨stored, found, _original, available, _encoded⟩ :=
                      scope.bindings.read source state.heap valid.1 growth history domain.key name boundName
                    have below := leftReference_below source facts holds domain name right scope complete selected state valid growth history
                    simp only [compileReference, boundName, ite_true, SourceRecursiveIntersectionCode.Below, found, requestNode] at below
                    simp only [reference, boundName, ite_true, found]
                    exact recurse ⟨domain, stored, right⟩ below.1
                      ⟨known, available.grows source state.heap growth history, rightAvailable⟩
                  · simpa only [reference, boundName, ite_false, Result.state] using lower_refl state.heap (limit + bound)
              | empty | node | union | mu => exact lower_refl state.heap _
          | rightReference =>
              simp only [onNode, selected]
              cases scope.right with
              | reference name =>
                  by_cases boundName : name ∈ names domain.key
                  · obtain ⟨stored, found, _original, available, _encoded⟩ :=
                      scope.bindings.read source state.heap valid.1 growth history domain.key name boundName
                    have below := rightReference_below source facts holds domain left name scope complete selected state valid growth history
                    simp only [compileReference, boundName, ite_true, SourceRecursiveIntersectionCode.Below, found, requestNode] at below
                    simp only [reference, boundName, ite_true, found]
                    exact recurse ⟨domain, left, stored⟩ below.1
                      ⟨known, leftAvailable, available.grows source state.heap growth history⟩
                  · simpa only [reference, boundName, ite_false, Result.state] using lower_refl state.heap (limit + bound)
              | empty | node | union | mu => exact lower_refl state.heap _
          | ordinary =>
              simp only [onNode, selected]
              cases scope.left with
              | node first leftEdges leftDepth leftFree _ =>
                  cases scope.right with
                  | node second rightEdges rightDepth rightFree _ =>
                      exact rows_lower source facts limit sourceBounded holds emptyGuard conjoin fuel ih bound domain leftEdges rightEdges
                        (fun rows member => rows_member_below source facts holds domain first leftEdges leftDepth leftFree second
                          rightEdges rightDepth rightFree scope complete selected rows member)
                        state valid known
                        (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
                        (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member)
                        growth history semantic opened
                  | empty | reference | union | mu => exact lower_refl state.heap _
              | empty | reference | union | mu => exact lower_refl state.heap _

end MicroCFTA.SourceRecursiveIntersectionKernel
