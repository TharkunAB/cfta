import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDepth
namespace FiniteOrdinaryDepthKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Domain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual edge and node construction derives cached zero depth for any complete raw guard. -/
theorem literal_constructors (symbol : Symbol) (guard : Guard) (state : State Symbol Guard)
    (semantic : SemanticReady state) :
    let edge := run (makeEdge symbol guard []) state
    let node := run (makeNode [edge.1]) edge.2
    Available node.2 node.1 ∧ Domain node.1 ∧ node.1.depth = 0 ∧ node.1.free = [] := by
  let edge := run (makeEdge symbol guard []) state
  let node := run (makeNode [edge.1]) edge.2
  have emptyValues : InternedNestedProvenance.Values state ([] : List (Value Symbol Guard)) := by intro value member; cases member
  have edgeFacts := SourceEqualityRequiredCache.edge symbol guard [] state semantic.ready emptyValues
  have edgeSemantic := SourceEqualityRequiredSemanticCache.edge symbol guard [] state semantic emptyValues
  have resident : InternedNestedProvenance.Edges edge.2 [edge.1] := by
    intro value member
    cases List.mem_singleton.mp member
    exact edgeFacts.2.1
  have closed : MergedColdReaderClosedInputs.ClosedEdges [edge.1] := by
    intro value member child selected
    cases List.mem_singleton.mp member
    rw [edgeFacts.2.2] at selected
    cases selected
  have nodeFacts := SourceEqualityRequiredCache.node [edge.1] edge.2 edgeSemantic.ready resident closed
  have nodeDomain := SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode [edge.1] edge.2
    edgeSemantic.ready.semantic.1.normal.facts.coherent edgeSemantic.ready.semantic.1.normal.facts.linked resident
    (.cons (by change SourceCurrentAllocatedFiniteOrdinaryDomain.Children edge.1.children; rw [edgeFacts.2.2]; exact .nil) .nil)
  have ready := nodeFacts.1.ready
  exact ⟨nodeFacts.2.1, nodeDomain,
    SourceCurrentAllocatedFiniteOrdinaryDepth.depth node.2 ready.semantic.1.normal.facts.coherent node.1 nodeFacts.2.1 nodeDomain,
    SourceCurrentAllocatedFiniteOrdinaryFinite.closed node.2 ready.semantic.1.normal.facts.coherent node.1 nodeFacts.2.1 nodeDomain⟩
end FiniteOrdinaryDepthKernels
#print axioms FiniteOrdinaryDepthKernels.literal_constructors
#check @FiniteOrdinaryDepthKernels.literal_constructors
