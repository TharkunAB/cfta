import MicroCFTA.SourceRecursiveIntersectionCompileReferenceBounds
import MicroCFTA.SourceRecursiveIntersectionCompileEdgeBounds

/-!
# Strict request limits of every compiled physical node branch

Original operand and binder scope, exact physical branch selection, and the
least semantic parent bound supply every recursive request limit. Actual
source effects and continuations retain the same body limit.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionControl

/-- Every compiled original node body derives its strict request limit through all actual continuations. -/
theorem compileNode_below [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts source) (holds : Guard → Language.Term Symbol → Bool) (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (complete : Completes (view source holds) (nodeSemantic request))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (ready : NodeReady state request)
    (growth : Grows source state.heap) (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Below source holds (requiredFuel (view source holds) (nodeSemantic request) complete) (compileNode request) state := by
  cases request with
  | mk domain left right =>
      obtain ⟨known, leftAvailable, rightAvailable⟩ := ready
      let bound := requiredFuel (view source holds) (nodeSemantic ⟨domain, left, right⟩) complete
      cases selected : decision domain.key left right with
      | empty | self | repeated key | unsupported => simp only [compileNode, selected, unsupported, Below]
      | reset =>
          simp only [compileNode, selected]
          apply below_requestNode source holds bound ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ state
          apply node_child_below source facts holds _ _ scope complete (scope.reset source domain left right)
          simp only [selected, branchCalls, List.mem_singleton]
          rfl
      | swap =>
          simp only [compileNode, selected]
          apply below_requestNode source holds bound ⟨domain, right, left⟩ state
          apply node_child_below source facts holds _ _ scope complete (scope.swap source domain left right)
          simp only [selected, branchCalls, List.mem_singleton]
          rfl
      | bothMu =>
          simpa only [compileNode, selected] using compileMu_below source facts holds ⟨domain, left, right⟩ scope complete (.inl selected) state valid
      | leftMu =>
          simpa only [compileNode, selected] using compileMu_below source facts holds ⟨domain, left, right⟩ scope complete (.inr (.inl selected)) state valid
      | rightMu =>
          simpa only [compileNode, selected] using compileMu_below source facts holds ⟨domain, left, right⟩ scope complete (.inr (.inr selected)) state valid
      | leftUnion =>
          simp only [compileNode, selected]
          cases left with
          | union entry members depth free =>
              exact union_below source holds bound domain members right true state valid known rightAvailable
                (fun value member => leftAvailable.children value member)
                (fun child member => leftUnion_member_below source facts holds domain entry members depth free right scope complete selected child member)
          | empty | reference | node | mu => trivial
      | rightUnion =>
          simp only [compileNode, selected]
          cases right with
          | union entry members depth free =>
              exact union_below source holds bound domain members left false state valid known leftAvailable
                (fun value member => rightAvailable.children value member)
                (fun child member => rightUnion_member_below source facts holds domain left entry members depth free scope complete selected child member)
          | empty | reference | node | mu => trivial
      | leftReference =>
          simp only [compileNode, selected]
          cases left <;> try trivial
          rename_i name
          cases name <;> try trivial
          rename_i identity
          exact leftReference_below source facts holds domain identity right scope complete selected state valid growth history
      | rightReference =>
          simp only [compileNode, selected]
          cases right <;> try trivial
          rename_i name
          cases name <;> try trivial
          rename_i identity
          exact rightReference_below source facts holds domain left identity scope complete selected state valid growth history
      | ordinary =>
          simp only [compileNode, selected]
          cases left <;> cases right <;> try trivial
          rename_i first leftEdges leftDepth leftFree second rightEdges rightDepth rightFree
          exact compileRows_below source holds bound domain leftEdges rightEdges state valid known
            (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
            (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member)
            (fun rows member => rows_member_below source facts holds domain first leftEdges leftDepth leftFree second rightEdges rightDepth rightFree
              scope complete selected rows member)

end MicroCFTA.SourceRecursiveIntersectionCode
