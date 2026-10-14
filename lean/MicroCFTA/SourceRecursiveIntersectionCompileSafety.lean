import MicroCFTA.SourceRecursiveIntersectionCompileSafetyCalls

/-!
# Physical safety of every compiled source branch

Original valid physical inputs derive the safety of the full source body.
The proof preserves actual guards, domains, record lookup, child order, and
constructor effects. Word bounds and completed memo provenance are not
replaced with assumptions about callback purity or product language.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks

/-- Every actual compiled node body derives source continuation safety from its original physical inputs. -/
theorem compileNode_safe [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (request : NodeRequest Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (ready : NodeReady state request) :
    Safe (compileNode request) state (fun after value => Available after.heap value) := by
  cases request with
  | mk domain left right =>
    obtain ⟨known, leftAvailable, rightAvailable⟩ := ready
    cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
    | empty => simpa only [compileNode, selected, Safe] using empty_available state.heap
    | reset =>
      simp only [compileNode, selected]
      exact safe_requestNode IntersectionEmptyDomain.emptyDomain left right state ⟨empty_domain state, leftAvailable, rightAvailable⟩
    | self => simpa only [compileNode, selected, Safe] using leftAvailable
    | swap =>
      simp only [compileNode, selected]
      exact safe_requestNode domain right left state ⟨known, rightAvailable, leftAvailable⟩
    | repeated key =>
      simp only [compileNode, selected, Safe]
      apply reference_available state.heap (.intersection key.1 key.2)
      intro name member
      simp [Value.free] at member
    | bothMu | leftMu | rightMu => simpa only [compileNode, selected] using compileMu_safe domain left right state valid known leftAvailable rightAvailable
    | leftUnion =>
      simp only [compileNode, selected]
      cases left with
      | union entry members depth free =>
        exact union_safe domain members right true state valid known rightAvailable
          (fun value member => leftAvailable.children value (by simpa only [children] using member))
      | empty | reference | node | mu => trivial
    | rightUnion =>
      simp only [compileNode, selected]
      cases right with
      | union entry members depth free =>
        exact union_safe domain members left false state valid known leftAvailable
          (fun value member => rightAvailable.children value (by simpa only [children] using member))
      | empty | reference | node | mu => trivial
    | leftReference =>
      simp only [compileNode, selected]
      cases left <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_safe _ _ _ _ state valid known rightAvailable | trivial
    | rightReference =>
      simp only [compileNode, selected]
      cases right <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_safe _ _ _ _ state valid known leftAvailable | trivial
    | ordinary =>
      simp only [compileNode, selected]
      cases left <;> cases right <;> try trivial
      rename_i first firstEdges firstDepth firstFree second secondEdges secondDepth secondFree
      exact compileRows_safe domain firstEdges secondEdges state valid known
        (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
        (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member)
    | unsupported => simp only [compileNode, selected, unsupported, Safe]

end MicroCFTA.SourceRecursiveIntersectionCode
