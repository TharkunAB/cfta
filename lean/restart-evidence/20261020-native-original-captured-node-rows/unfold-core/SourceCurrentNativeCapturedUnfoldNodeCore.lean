import MicroCFTA.SourceCurrentNativeOriginalNodeRowOrigins
import MicroCFTA.SourceCurrentNativeCapturedMuUnfoldRows

namespace MicroCFTA.SourceCurrentNativeOriginalCapturedNodeRows
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildEdges)
open InternedStoredSubstitution (leaves)
open InternedBinderProtocol (NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentNativeOriginalPublicationTrace (events)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentNativeOriginalUnionDescent (UnionDescent)
open SourceCurrentNativeOriginalObservedResume (SyntaxBound)
open SourceCurrentLiteralRootParts (Row)
open SourceCurrentStoredSubstitutionCalls (Calls)
open InternedEdgeResidency (nodeEdges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]

private theorem captured_unfold_nodes (original : Syntax Symbol Guard) (sourceRoot : Node)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (before current : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (sourceBuilt : build original [] empty = .done sourceRoot before.native.machine.heap)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) current)
    (available : Available current.native.machine.heap siteBody)
    (leafIndex : Nat) (entry : Interned NodeKey) (body depth ordinary : Node)
    (found : (leaves siteBody)[leafIndex]? = some (.mu entry body depth ordinary))
    (path : Path empty before.native.machine.heap)
    (outerIndex : Nat) (outer : @Publication Symbol Guard _)
    (selectedOuter : (events path)[outerIndex]? = some outer)
    (bodySame : body = outer.body)
    (nodeOrigins : ∀ (index : Nat) outer, (events path)[index]? = some outer →
        ∀ row, RowAt outer.body row →
      ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ index ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached original [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after row ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some row ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = row ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued) :
    SemanticHeap current.native.machine.heap ∧
      Available current.native.machine.heap (.mu entry body depth ordinary) ∧
      Nonempty (SourceCurrentNativeMuPublication.History empty current.native.machine.heap) ∧
      ∀ value after,
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary)
          current.native.machine.heap = .done value after →
        SemanticHeap after ∧ Grows current.native.machine.heap after ∧
          Extends current.native.machine.heap.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
            ∃ storedRow, RowAt body storedRow ∧
              row.entry.key.symbol = storedRow.entry.key.symbol ∧
              row.entry.key.constraint = storedRow.entry.key.constraint ∧
              row.children.length = storedRow.children.length ∧
              (row = storedRow ∨ ∃ lexical start finish, Calls lexical storedRow.children start row.children finish) ∧
              ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached original [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after storedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some storedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = storedRow ∧ Grows after outer.afterBody ∧
            Extends after.nodes.issued outer.afterBody.nodes.issued := by
  have initial : before.native.machine.heap = (build original [] empty).state := by
    rw [sourceBuilt]
    rfl
  obtain ⟨currentSemantic,⟨currentPublished⟩⟩ :=
    SourceCurrentNativePublicationTrace.source_trace original actual initial
  have captured := InternedStoredSubstitution.leaves_available siteBody current.native.machine.heap
    available (.mu entry body depth ordinary) (List.mem_of_getElem? found)
  refine ⟨currentSemantic,captured,⟨currentPublished⟩,?_⟩
  intro value after unfolded
  obtain ⟨semanticAfter,growth,issued,valueAvailable,published,anchors⟩ :=
    SourceCurrentNativeCapturedMuUnfoldRows.unfold_rows entry body depth ordinary current.native.machine.heap
      currentSemantic captured currentPublished value after unfolded
  refine ⟨semanticAfter,growth,issued,valueAvailable,published,?_⟩
  intro row literal
  obtain ⟨storedRow,inside,symbol,guard,arity,calls⟩ := anchors row literal
  exact ⟨storedRow,inside,symbol,guard,arity,calls,
    nodeOrigins outerIndex outer selectedOuter storedRow (bodySame ▸ inside)⟩

end MicroCFTA.SourceCurrentNativeOriginalCapturedNodeRows
