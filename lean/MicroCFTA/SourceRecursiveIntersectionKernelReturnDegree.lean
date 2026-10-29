import MicroCFTA.SourceRecursiveIntersectionKernelRowsDegree
import MicroCFTA.SourceRecursiveIntersectionKernelUnionDegree
import MicroCFTA.SourceRecursiveIntersectionKernelMuDegree
import MicroCFTA.SourceRecursiveIntersectionCompileNodeBounds
import MicroCFTA.InternedMuDepthAvailableBounds

/-!
# Actual kernel return degree from the original input

Natural induction on runtime fuel supplies all actual child results.
Each original semantic child has a strictly smaller required fuel.
The conclusion retains the actual returned value and both reached heaps.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionCode InternedStoredPlanBinderDepth
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Every actual completed original request satisfies its original-input degree bound. -/
theorem node_result_degree
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) :
    ∀ (request : NodeRequest Symbol Guard) (_scope : NodeScope source request)
      (complete : Completes (view source holds) (nodeSemantic request))
      (state after : Machine Symbol Guard),
      Valid state → NodeReady state request →
      Grows source state.heap → Extends source.nodes.issued state.heap.nodes.issued →
      SemanticHeap state.heap → InternedOpenDepthReadback.Heap state.heap →
      ∀ value, execute emptyGuard conjoin fuel request.domain request.left request.right state = .done value after →
      SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧
        valueDepth value ≤ limit + requiredFuel (view source holds) (nodeSemantic request) complete := by
  induction fuel with
  | zero =>
      intro request scope complete state after valid ready growth history semantic opened value done
      cases done
  | succ fuel ih =>
      intro request scope complete state after valid ready growth history semantic opened value done
      cases request with
      | mk domain left right =>
          obtain ⟨known, leftAvailable, rightAvailable⟩ := ready
          let bound := requiredFuel (view source holds) (nodeSemantic ⟨domain, left, right⟩) complete
          have recurse (child : NodeRequest Symbol Guard) (below : NodeBelow source holds bound child)
              (childReady : NodeReady state child)
              (returned : execute emptyGuard conjoin fuel child.domain child.left child.right state = .done value after) :
              SemanticHeap after.heap ∧ InternedOpenDepthReadback.Heap after.heap ∧ valueDepth value ≤ limit + bound := by
            obtain ⟨childScope, childComplete, childLess⟩ := below
            obtain ⟨afterSemantic, afterOpened, childDegree⟩ := ih child childScope childComplete state after valid childReady
              growth history semantic opened value returned
            exact ⟨afterSemantic, afterOpened,
              Nat.le_trans childDegree (Nat.add_le_add_left (Nat.le_of_lt childLess) limit)⟩
          simp only [execute] at done
          cases selected : decision domain.key left right with
          | empty =>
              simp only [onNode, selected] at done
              cases done
              exact ⟨semantic, opened, by simp [valueDepth, Value.free]⟩
          | self =>
              simp only [onNode, selected] at done
              cases done
              exact ⟨semantic, opened, Nat.le_trans
                (InternedMuDepthAvailableBounds.value_le source limit sourceBounded _ scope.leftAvailable) (Nat.le_add_right _ _)⟩
          | repeated key =>
              simp only [onNode, selected] at done
              cases done
              exact ⟨semantic, opened, by simp [repeatedValue, valueDepth, Value.free]⟩
          | unsupported =>
              simp only [onNode, selected, unsupported] at done
              cases done
          | reset =>
              simp only [onNode, selected] at done
              apply recurse ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ ?_
                ⟨empty_domain state, leftAvailable, rightAvailable⟩ done
              apply node_child_below source facts holds _ _ scope complete (scope.reset source domain left right)
              simp only [selected, branchCalls, List.mem_singleton]
              rfl
          | swap =>
              simp only [onNode, selected] at done
              apply recurse ⟨domain, right, left⟩ ?_ ⟨known, rightAvailable, leftAvailable⟩ done
              apply node_child_below source facts holds _ _ scope complete (scope.swap source domain left right)
              simp only [selected, branchCalls, List.mem_singleton]
              rfl
          | bothMu =>
              simp only [onNode, selected] at done
              exact mu_degree source facts limit sourceBounded holds emptyGuard conjoin fuel ih
                ⟨domain, left, right⟩ scope complete (.inl selected) state after valid
                ⟨known, leftAvailable, rightAvailable⟩ growth history semantic opened value done
          | leftMu =>
              simp only [onNode, selected] at done
              exact mu_degree source facts limit sourceBounded holds emptyGuard conjoin fuel ih
                ⟨domain, left, right⟩ scope complete (.inr (.inl selected)) state after valid
                ⟨known, leftAvailable, rightAvailable⟩ growth history semantic opened value done
          | rightMu =>
              simp only [onNode, selected] at done
              exact mu_degree source facts limit sourceBounded holds emptyGuard conjoin fuel ih
                ⟨domain, left, right⟩ scope complete (.inr (.inr selected)) state after valid
                ⟨known, leftAvailable, rightAvailable⟩ growth history semantic opened value done
          | leftUnion =>
              simp only [onNode, selected] at done
              cases left with
              | union entry members depth free =>
                  exact union_degree source facts limit sourceBounded holds emptyGuard conjoin fuel ih domain members right true bound
                    state after valid known rightAvailable (fun child member => leftAvailable.children child member)
                    growth history semantic opened
                    (fun child member => leftUnion_member_below source facts holds domain entry members depth free right scope complete selected child member)
                    value done
              | empty | reference | node | mu => cases done
          | rightUnion =>
              simp only [onNode, selected] at done
              cases right with
              | union entry members depth free =>
                  exact union_degree source facts limit sourceBounded holds emptyGuard conjoin fuel ih domain members left false bound
                    state after valid known leftAvailable (fun child member => rightAvailable.children child member)
                    growth history semantic opened
                    (fun child member => rightUnion_member_below source facts holds domain left entry members depth free scope complete selected child member)
                    value done
              | empty | reference | node | mu => cases done
          | leftReference =>
              simp only [onNode, selected] at done
              cases scope.left with
              | reference name =>
                  by_cases boundName : name ∈ names domain.key
                  · obtain ⟨stored, found, _original, available, _encoded⟩ :=
                      scope.bindings.read source state.heap valid.1 growth history domain.key name boundName
                    have below := leftReference_below source facts holds domain name right scope complete selected state valid growth history
                    simp only [compileReference, boundName, ite_true, SourceRecursiveIntersectionCode.Below, found, requestNode] at below
                    simp only [reference, boundName, ite_true, found] at done
                    exact recurse ⟨domain, stored, right⟩ below.1
                      ⟨known, available.grows source state.heap growth history, rightAvailable⟩ done
                  · simp only [reference, boundName, ite_false] at done
                    cases done
              | empty | node | union | mu => cases done
          | rightReference =>
              simp only [onNode, selected] at done
              cases scope.right with
              | reference name =>
                  by_cases boundName : name ∈ names domain.key
                  · obtain ⟨stored, found, _original, available, _encoded⟩ :=
                      scope.bindings.read source state.heap valid.1 growth history domain.key name boundName
                    have below := rightReference_below source facts holds domain left name scope complete selected state valid growth history
                    simp only [compileReference, boundName, ite_true, SourceRecursiveIntersectionCode.Below, found, requestNode] at below
                    simp only [reference, boundName, ite_true, found] at done
                    exact recurse ⟨domain, left, stored⟩ below.1
                      ⟨known, leftAvailable, available.grows source state.heap growth history⟩ done
                  · simp only [reference, boundName, ite_false] at done
                    cases done
              | empty | node | union | mu => cases done
          | ordinary =>
              simp only [onNode, selected] at done
              cases scope.left with
              | node first leftEdges leftDepth leftFree _ =>
                  cases scope.right with
                  | node second rightEdges rightDepth rightFree _ =>
                      exact rows_degree source facts holds emptyGuard conjoin limit fuel ih bound domain leftEdges rightEdges
                        (fun rows member => rows_member_below source facts holds domain first leftEdges leftDepth leftFree second
                          rightEdges rightDepth rightFree scope complete selected rows member)
                        state after valid known
                        (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
                        (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member)
                        growth history semantic opened value done
                  | empty | reference | union | mu => cases done
              | empty | reference | union | mu => cases done

end MicroCFTA.SourceRecursiveIntersectionKernel
