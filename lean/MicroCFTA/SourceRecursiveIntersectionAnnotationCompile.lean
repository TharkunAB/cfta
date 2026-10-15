import MicroCFTA.SourceRecursiveIntersectionAnnotationCalls

/-!
# Annotation conditions of every actual compiled node branch

The proof uses original available operands and source domains. The actual
compiler supplies each local annotation condition before native execution.
-/
namespace MicroCFTA.SourceRecursiveIntersectionAnnotationCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Every actual compiled node body derives source semantic heap conditions from its original physical inputs. -/
theorem compileNode_annotation (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (request : NodeRequest Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (ready : NodeReady state request) :
    Certified annotation (compileNode request) state := by
  cases request with
  | mk domain left right =>
    obtain ⟨known, leftAvailable, rightAvailable⟩ := ready
    cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
    | empty => simp only [compileNode, selected, Certified]
    | reset =>
      simp only [compileNode, selected]
      exact annotation_requestNode annotation IntersectionEmptyDomain.emptyDomain left right state ⟨empty_domain state, leftAvailable, rightAvailable⟩
    | self => simp only [compileNode, selected, Certified]
    | swap =>
      simp only [compileNode, selected]
      exact annotation_requestNode annotation domain right left state ⟨known, rightAvailable, leftAvailable⟩
    | repeated key => simp only [compileNode, selected, Certified]
    | bothMu | leftMu | rightMu => simpa only [compileNode, selected] using compileMu_annotation annotation domain left right state valid known leftAvailable rightAvailable
    | leftUnion =>
      simp only [compileNode, selected]
      cases left with
      | union entry members depth free =>
        exact union_annotation annotation domain members right true state valid known rightAvailable
          (fun value member => leftAvailable.children value (by simpa only [children] using member))
      | empty | reference | node | mu => trivial
    | rightUnion =>
      simp only [compileNode, selected]
      cases right with
      | union entry members depth free =>
        exact union_annotation annotation domain members left false state valid known leftAvailable
          (fun value member => rightAvailable.children value (by simpa only [children] using member))
      | empty | reference | node | mu => trivial
    | leftReference =>
      simp only [compileNode, selected]
      cases left <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_annotation annotation _ _ _ _ state valid known rightAvailable | trivial
    | rightReference =>
      simp only [compileNode, selected]
      cases right <;> try trivial
      rename_i name
      cases name <;> first | exact compileReference_annotation annotation _ _ _ _ state valid known leftAvailable | trivial
    | ordinary =>
      simp only [compileNode, selected]
      cases left <;> cases right <;> try trivial
      rename_i first firstEdges firstDepth firstFree second secondEdges secondDepth secondFree
      exact compileRows_annotation annotation domain firstEdges secondEdges state valid known
        (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
        (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member)
    | unsupported => simp only [compileNode, selected, SourceRecursiveIntersectionCode.unsupported, Certified]

end MicroCFTA.SourceRecursiveIntersectionAnnotationCode
