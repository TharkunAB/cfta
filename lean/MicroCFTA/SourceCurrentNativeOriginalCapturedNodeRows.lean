import MicroCFTA.SourceCurrentNativeOriginalNodeRowOrigins
import MicroCFTA.SourceCurrentNativeCapturedMuUnfoldRows

/-!
# Original node calls for actual captured Mu rows

The exact initial source heap fixes an indexed writer before all rows.
Actual unfolds keep their stored anchors and ordered changed-child calls.
The later-generated capture branch retains its existing receipts.
-/

namespace MicroCFTA.SourceCurrentNativeOriginalCapturedNodeRows
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildEdges)
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceCurrentNativeCapturedMuStoredRows (Stored)
open SourceCurrentNativeCapturedMuUnfoldRows (Observed)
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

/-- An actual captured initial Mu retains indexed original node calls for its stored and unfolded rows. -/
theorem capture_node_rows (original : Syntax Symbol Guard) (sourceRoot : Node)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (before current : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (sourceBuild : build original [] empty = .done sourceRoot before.native.machine.heap)
    (good : Good before) (history : History before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) current)
    (available : Available current.native.machine.heap siteBody)
    (index : Nat) (entry : Interned NodeKey) (body depth ordinary : Node)
    (found : (leaves siteBody)[index]? = some (.mu entry body depth ordinary)) :
    (before.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      ∃ path : Path empty before.native.machine.heap,
        (∀ (index : Nat) event, (events path)[index]? = some event →
          Reached original [] (.binder event.smart event.expression) event.environment event.before) ∧
        (∀ key selectedEntry selectedBody selectedDepth selectedOrdinary,
          before.native.machine.heap.nodeRecords key = some (.mu selectedEntry selectedBody selectedDepth selectedOrdinary) →
          ∃ index : Nat, ∃ event, (events path)[index]? = some event ∧
            Reached original [] (.binder event.smart event.expression) event.environment event.before ∧
            key = event.key ∧ Value.mu selectedEntry selectedBody selectedDepth selectedOrdinary = event.candidate ∧
            event.afterBody.nodeRecords event.key = none ∧
            Nonempty (Path empty event.before) ∧
            Nonempty (Path event.before event.afterDepth) ∧
            Nonempty (Path event.afterDepth event.cut) ∧
            Nonempty (Path event.allocated event.afterBody) ∧
            Grows event.after before.native.machine.heap ∧
            Extends event.after.nodes.issued before.native.machine.heap.nodes.issued) ∧
        ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,
          (events path)[outerIndex]? = some outer ∧
          Reached original [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
          entry.key = outer.key ∧ Value.mu entry body depth ordinary = outer.candidate ∧
          entry = outer.entry ∧ body = outer.body ∧ depth = outer.depth ∧ ordinary = outer.ordinary ∧
          outer.afterBody.nodeRecords outer.key = none ∧
          Nonempty (Path empty outer.before) ∧
          Nonempty (Path outer.before outer.afterDepth) ∧
          Nonempty (Path outer.afterDepth outer.cut) ∧
          Nonempty (Path outer.allocated outer.afterBody) ∧
          Grows outer.after before.native.machine.heap ∧
          Extends outer.after.nodes.issued before.native.machine.heap.nodes.issued ∧
          (∀ storedRow, RowAt body storedRow →
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
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∧
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
            Extends after.nodes.issued outer.afterBody.nodes.issued) ∨
    ∃ prefixFuel suffixFuel priorPair parent next siteBefore siteAfter result heap,
      fuel = prefixFuel + 1 + suffixFuel ∧ prefixFuel < fuel ∧
      Trace prefixFuel (.code (requestNode request.domain request.left request.right)) before
        (.code (.optionalBinder priorPair parent next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap parent ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu priorPair parent siteBefore.native.machine.heap = .done result heap ∧
      siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩ ∧
      step (.code (.optionalBinder priorPair parent next)) siteBefore = .yielded (.code (next result)) siteAfter ∧
      Trace suffixFuel (.code (next result)) siteAfter (.code (.optionalBinder pair siteBody siteNext)) current ∧
      siteBefore.native.machine.heap.nodeRecords entry.key = none ∧
      heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows heap current.native.machine.heap ∧ Extends heap.nodes.issued current.native.machine.heap.nodes.issued ∧
      Reference.intersection priorPair.1 priorPair.2 ∈ parent.free ∧
      Context siteBefore.native.machine.heap (leaves parent) ∧
      InternedFreshOrdinaryConstruction.build
        (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap = .done result heap ∧
      Written (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent)) (leaves parent)
        siteBefore.native.machine.heap heap entry.key (.mu entry body depth ordinary) ∧
      SourceCurrentNativeOptionalRowProduction.Origin request prefixFuel before siteBefore priorPair parent next ∧
      Stored (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary ∧
      Observed (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary
        current.native.machine.heap := by
  have semantic := SourceRecursiveIntersectionSemanticHeap.constructed original sourceRoot before.native.machine.heap sourceBuild
  have publications : SourceCurrentNativeMuPublication.History empty before.native.machine.heap := by
    simpa only [sourceBuild,InternedNestedConstruction.Outcome.state] using SourceCurrentNativeMuPublication.closed_history original
  rcases SourceCurrentNativeCapturedMuUnfoldRows.capture request fuel before current pair siteBody siteNext
      good history semantic publications actual available index entry body depth ordinary found with prior | generated
  · obtain ⟨path,sites,finalWriters,origins⟩ :=
      SourceCurrentNativeOriginalNodeRowOrigins.build_node_row_origins original sourceRoot before.native.machine.heap sourceBuild
    obtain ⟨outerIndex,outer,selectedOuter,rooted,keySame,valueSame,missing,prefixPath,
      depthPath,ordinaryPath,bodyPath,growth,issued⟩ :=
      finalWriters entry.key entry body depth ordinary prior
    obtain ⟨entrySame,bodySame,depthSame,ordinarySame⟩ := Value.mu.inj valueSame
    refine .inl ⟨prior,path,sites,finalWriters,outerIndex,outer,selectedOuter,rooted,keySame,valueSame,
      entrySame,bodySame,depthSame,ordinarySame,missing,prefixPath,depthPath,ordinaryPath,bodyPath,growth,issued,?_,?_⟩
    · intro storedRow inside
      exact origins outerIndex outer selectedOuter storedRow (bodySame ▸ inside)
    · exact captured_unfold_nodes original sourceRoot request fuel before current pair siteBody siteNext
        sourceBuild actual available index entry body depth ordinary found path outerIndex outer
        selectedOuter bodySame origins
  · exact .inr generated

end MicroCFTA.SourceCurrentNativeOriginalCapturedNodeRows
