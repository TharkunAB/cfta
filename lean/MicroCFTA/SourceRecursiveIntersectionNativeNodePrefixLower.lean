import MicroCFTA.SourceRecursiveIntersectionNativeMuPrefixLower
import MicroCFTA.SourceRecursiveIntersectionNativeUnionPrefixLower
import MicroCFTA.SourceRecursiveIntersectionNativeRowsPrefixLower
import MicroCFTA.SourceRecursiveIntersectionCompileNodeBounds

namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionCode IntersectSchedule
open InternedStoredPlanBinderDepthProgress SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Each compiled node prefix derives its bound from strictly smaller original requests. -/
theorem compiled_node_prefix_lower
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (limit : Nat) (sourceBounded : InternedMuDepthInventory.Bounded source limit)
    (holds : Guard → Language.Term Symbol → Bool) (width : Nat)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (nodeSemantic request))
    (nodeIH : ∀ (child : NodeRequest Symbol Guard) (_scope : NodeScope source child)
      (childComplete : Completes (view source holds) (nodeSemantic child)),
      requiredFuel (view source holds) (nodeSemantic child) childComplete <
        requiredFuel (view source holds) (nodeSemantic request) complete →
      ∀ (current : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current → NodeReady current.machine child →
      Grows source current.machine.heap → Extends source.nodes.issued current.machine.heap.nodes.issued →
      SemanticHeap current.machine.heap → InternedOpenDepthReadback.Heap current.machine.heap →
      WordRanges emptyGuard conjoin (.node child .pure) current → ∀ fuel,
      Lower current.machine.heap (limit + requiredFuel (view source holds) (nodeSemantic child) childComplete)
        (execute emptyGuard conjoin fuel (.node child .pure) current).state.machine.heap)
    (edgeIH : ∀ (child : EdgeRequest Symbol Guard) (_scope : EdgeScope source child)
      (childComplete : Completes (view source holds) (edgeSemantic holds child)),
      requiredFuel (view source holds) (edgeSemantic holds child) childComplete <
        requiredFuel (view source holds) (nodeSemantic request) complete →
      ∀ (current : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current → EdgeReady current.machine child →
      Grows source current.machine.heap → Extends source.nodes.issued current.machine.heap.nodes.issued →
      SemanticHeap current.machine.heap → InternedOpenDepthReadback.Heap current.machine.heap →
      WordRanges emptyGuard conjoin (.edge child .pure) current → ∀ fuel,
      Lower current.machine.heap (limit + requiredFuel (view source holds) (edgeSemantic holds child) childComplete)
        (execute emptyGuard conjoin fuel (.edge child .pure) current).state.machine.heap)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ready : NodeReady state.machine request)
    (growth : Grows source state.machine.heap) (history : Extends source.nodes.issued state.machine.heap.nodes.issued)
    (semantic : SemanticHeap state.machine.heap) (opened : InternedOpenDepthReadback.Heap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin (compileNode request) state) (fuel : Nat) :
    Lower state.machine.heap (limit + requiredFuel (view source holds) (nodeSemantic request) complete)
      (execute emptyGuard conjoin fuel (compileNode request) state).state.machine.heap := by
  let bound := requiredFuel (view source holds) (nodeSemantic request) complete
  have nodeParent (child : NodeRequest Symbol Guard) (below : NodeBelow source holds bound child)
      (current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
      (currentValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current)
      (inputs : NodeReady current.machine child) (grown : Grows source current.machine.heap)
      (retained : Extends source.nodes.issued current.machine.heap.nodes.issued)
      (meaning : SemanticHeap current.machine.heap) (openDepth : InternedOpenDepthReadback.Heap current.machine.heap)
      (callRanges : WordRanges emptyGuard conjoin (.node child .pure) current) (inner : Nat) :
      Lower current.machine.heap (limit + bound)
        (execute emptyGuard conjoin inner (.node child .pure) current).state.machine.heap := by
    obtain ⟨childScope, childComplete, smaller⟩ := below
    exact (nodeIH child childScope childComplete smaller current currentValid inputs grown retained meaning openDepth callRanges inner).mono
      (Nat.add_le_add_left (Nat.le_of_lt smaller) limit)
  have edgeParent (child : EdgeRequest Symbol Guard) (below : EdgeBelow source holds bound child)
      (current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
      (currentValid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin current)
      (inputs : EdgeReady current.machine child) (grown : Grows source current.machine.heap)
      (retained : Extends source.nodes.issued current.machine.heap.nodes.issued)
      (meaning : SemanticHeap current.machine.heap) (openDepth : InternedOpenDepthReadback.Heap current.machine.heap)
      (callRanges : WordRanges emptyGuard conjoin (.edge child .pure) current) (inner : Nat) :
      Lower current.machine.heap (limit + bound)
        (execute emptyGuard conjoin inner (.edge child .pure) current).state.machine.heap := by
    obtain ⟨childScope, childComplete, smaller⟩ := below
    exact (edgeIH child childScope childComplete smaller current currentValid inputs grown retained meaning openDepth callRanges inner).mono
      (Nat.add_le_add_left (Nat.le_of_lt smaller) limit)
  cases request with
  | mk domain left right =>
      obtain ⟨known, leftAvailable, rightAvailable⟩ := ready
      have recurse (child : NodeRequest Symbol Guard) (below : NodeBelow source holds bound child)
          (inputs : NodeReady state.machine child)
          (callRanges : WordRanges emptyGuard conjoin (.node child .pure) state) (inner : Nat) :=
        nodeParent child below state valid inputs growth history semantic opened callRanges inner
      cases selected : decision domain.key left right with
      | empty => simpa only [compileNode, selected] using pure_lower emptyGuard conjoin fuel (.empty : Value Symbol Guard) state (limit + bound)
      | self => simpa only [compileNode, selected] using pure_lower emptyGuard conjoin fuel left state (limit + bound)
      | repeated key => simpa only [compileNode, selected] using pure_lower emptyGuard conjoin fuel (repeatedValue key) state (limit + bound)
      | unsupported =>
          simp only [compileNode, selected]
          exact fail_lower emptyGuard conjoin fuel (.unsupported left.referenceOf right.referenceOf) state (limit + bound)
      | reset =>
          simp only [compileNode, selected] at ranges ⊢
          apply recurse ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ ?_
            ⟨SourceRecursiveIntersectionKernel.empty_domain state.machine, leftAvailable, rightAvailable⟩ ranges fuel
          apply node_child_below source facts holds _ _ scope complete (scope.reset source domain left right)
          simp only [selected, branchCalls, List.mem_singleton]
          rfl
      | swap =>
          simp only [compileNode, selected] at ranges ⊢
          apply recurse ⟨domain, right, left⟩ ?_ ⟨known, rightAvailable, leftAvailable⟩ ranges fuel
          apply node_child_below source facts holds _ _ scope complete (scope.swap source domain left right)
          simp only [selected, branchCalls, List.mem_singleton]
          rfl
      | bothMu =>
          simp only [compileNode, selected] at ranges ⊢
          exact compiled_mu_prefix_lower source facts limit sourceBounded holds width emptyGuard conjoin _ scope complete
            (.inl selected) nodeIH state valid ⟨known, leftAvailable, rightAvailable⟩ growth history semantic opened ranges fuel
      | leftMu =>
          simp only [compileNode, selected] at ranges ⊢
          exact compiled_mu_prefix_lower source facts limit sourceBounded holds width emptyGuard conjoin _ scope complete
            (.inr (.inl selected)) nodeIH state valid ⟨known, leftAvailable, rightAvailable⟩ growth history semantic opened ranges fuel
      | rightMu =>
          simp only [compileNode, selected] at ranges ⊢
          exact compiled_mu_prefix_lower source facts limit sourceBounded holds width emptyGuard conjoin _ scope complete
            (.inr (.inr selected)) nodeIH state valid ⟨known, leftAvailable, rightAvailable⟩ growth history semantic opened ranges fuel
      | leftUnion =>
          simp only [compileNode, selected] at ranges ⊢
          cases left with
          | union entry members depth free =>
              exact union_prefix_lower source facts limit sourceBounded holds width emptyGuard conjoin bound nodeParent
                domain members right true state valid known rightAvailable (fun child member => leftAvailable.children child member)
                growth history semantic opened
                (fun child member => leftUnion_member_below source facts holds domain entry members depth free right scope complete selected child member)
                ranges fuel
          | empty | reference | node | mu => exact fail_lower emptyGuard conjoin fuel _ state (limit + bound)
      | rightUnion =>
          simp only [compileNode, selected] at ranges ⊢
          cases right with
          | union entry members depth free =>
              exact union_prefix_lower source facts limit sourceBounded holds width emptyGuard conjoin bound nodeParent
                domain members left false state valid known leftAvailable (fun child member => rightAvailable.children child member)
                growth history semantic opened
                (fun child member => rightUnion_member_below source facts holds domain left entry members depth free scope complete selected child member)
                ranges fuel
          | empty | reference | node | mu => exact fail_lower emptyGuard conjoin fuel _ state (limit + bound)
      | leftReference =>
          simp only [compileNode, selected] at ranges ⊢
          cases scope.left with
          | reference name =>
              by_cases boundName : name ∈ names domain.key
              · obtain ⟨stored, found, _original, available, _encoded⟩ :=
                  scope.bindings.read source state.machine.heap valid.machine.1 growth history domain.key name boundName
                have below := leftReference_below source facts holds domain name right scope complete selected state.machine valid.machine growth history
                simp only [compileReference, boundName, ite_true, SourceRecursiveIntersectionCode.Below, found, requestNode] at below
                cases fuel with
                | zero => exact lower_refl state.machine.heap _
                | succ fuel =>
                    have one : step emptyGuard conjoin (compileReference domain name right true) state =
                        .yielded (.node ⟨domain, stored, right⟩ .pure) state := by
                      simp only [compileReference, boundName, ite_true, step, found, requestNode]
                    have childRanges := ranges.after_step emptyGuard conjoin _ _ _ _ one
                    simpa only [execute, one] using recurse ⟨domain, stored, right⟩ below.1
                      ⟨known, available.grows source state.machine.heap growth history, rightAvailable⟩ childRanges fuel
              · simpa only [compileReference, boundName, ite_false] using
                  fail_lower emptyGuard conjoin fuel (.missingBinder name) state (limit + bound)
          | empty | node | union | mu => exact fail_lower emptyGuard conjoin fuel _ state (limit + bound)
      | rightReference =>
          simp only [compileNode, selected] at ranges ⊢
          cases scope.right with
          | reference name =>
              by_cases boundName : name ∈ names domain.key
              · obtain ⟨stored, found, _original, available, _encoded⟩ :=
                  scope.bindings.read source state.machine.heap valid.machine.1 growth history domain.key name boundName
                have below := rightReference_below source facts holds domain left name scope complete selected state.machine valid.machine growth history
                simp only [compileReference, boundName, ite_true, SourceRecursiveIntersectionCode.Below, found, requestNode] at below
                cases fuel with
                | zero => exact lower_refl state.machine.heap _
                | succ fuel =>
                    have one : step emptyGuard conjoin (compileReference domain name left false) state =
                        .yielded (.node ⟨domain, left, stored⟩ .pure) state := by
                      simp only [compileReference, boundName, ite_true, step, found, requestNode, Bool.false_eq_true, ite_false]
                    have childRanges := ranges.after_step emptyGuard conjoin _ _ _ _ one
                    simpa only [execute, one] using recurse ⟨domain, left, stored⟩ below.1
                      ⟨known, leftAvailable, available.grows source state.machine.heap growth history⟩ childRanges fuel
              · simpa only [compileReference, boundName, ite_false] using
                  fail_lower emptyGuard conjoin fuel (.missingBinder name) state (limit + bound)
          | empty | node | union | mu => exact fail_lower emptyGuard conjoin fuel _ state (limit + bound)
      | ordinary =>
          simp only [compileNode, selected] at ranges ⊢
          cases scope.left with
          | node first leftEdges leftDepth leftFree _ =>
              cases scope.right with
              | node second rightEdges rightDepth rightFree _ =>
                  exact rows_prefix_lower source facts limit sourceBounded holds width emptyGuard conjoin bound edgeParent
                    domain leftEdges rightEdges
                    (fun rows member => rows_member_below source facts holds domain first leftEdges leftDepth leftFree second
                      rightEdges rightDepth rightFree scope complete selected rows member)
                    state valid known
                    (fun edge member => valid.machine.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
                    (fun edge member => valid.machine.1.linked second.key _ (rightAvailable.resident second rfl) edge member)
                    growth history semantic opened ranges fuel
              | empty | reference | union | mu => exact fail_lower emptyGuard conjoin fuel _ state (limit + bound)
          | empty | reference | union | mu => exact fail_lower emptyGuard conjoin fuel _ state (limit + bound)

end MicroCFTA.SourceRecursiveIntersectionNative
