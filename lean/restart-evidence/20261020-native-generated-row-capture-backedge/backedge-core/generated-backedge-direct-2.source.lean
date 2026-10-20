import MicroCFTA.SourceCurrentNativeOriginalCapturedNodeRows
import MicroCFTA.SourceCurrentSourceRowTerminalSuffix
import MicroCFTA.SourceCurrentSourceCaptureOriginalSlots
import MicroCFTA.InternedStoredLeafShape

namespace MicroCFTA.SourceCurrentNativeGeneratedRowBackedges
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

private theorem capture_same_row (original : Syntax Symbol Guard) (sourceRoot : Node)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (before current : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (sourceBuild : build original [] empty = .done sourceRoot before.native.machine.heap)
    (good : Good before) (history : History before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) current)
    (available : Available current.native.machine.heap siteBody)
    (index : Nat) (entry : Interned NodeKey) (body depth ordinary : Node)
    (found : (leaves siteBody)[index]? = some (.mu entry body depth ordinary))
    (selectedRow : EdgeValue Symbol Guard) (selectedInside : RowAt body selectedRow) :
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
      (∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached original [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after selectedRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some selectedRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = selectedRow ∧ Grows after outer.afterBody ∧
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
  rcases SourceCurrentNativeOriginalCapturedNodeRows.capture_node_rows original sourceRoot request fuel before current
      pair siteBody siteNext sourceBuild good history actual available index entry body depth ordinary found with prior | generated
  · obtain ⟨prior,path,sites,finalWriters,outerIndex,outer,selectedOuter,rooted,keySame,valueSame,
      entrySame,bodySame,depthSame,ordinarySame,missing,prefixPath,depthPath,ordinaryPath,bodyPath,
      growth,issued,origins,readback⟩ := prior
    exact .inl ⟨prior,path,sites,finalWriters,outerIndex,outer,selectedOuter,rooted,keySame,valueSame,
      entrySame,bodySame,depthSame,ordinarySame,missing,prefixPath,depthPath,ordinaryPath,bodyPath,
      growth,issued,origins,origins selectedRow selectedInside,readback⟩
  · exact .inr generated

private theorem generated_terminal (original : Syntax Symbol Guard) (sourceRoot : Node)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (before current : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (sourceBuild : build original [] empty = .done sourceRoot before.native.machine.heap)
    (good : Good before) (history : History before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) current)
    (available : Available current.native.machine.heap siteBody)
    (expression : Syntax Symbol Guard) (inputs : List Node) (start : Heap)
    (raw : Node) (stop : Heap) (fullRow : EdgeValue Symbol Guard)
    (context : Context start inputs)
    (reached : Reached (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody) expression inputs start)
    (source : SourceRow expression inputs start raw stop fullRow) :
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter fullRow ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody) terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression expression ∧
      Grows terminalAfter stop ∧ Extends terminalAfter.nodes.issued stop.nodes.issued ∧
      ((∃ edges, terminalExpression = Syntax.node edges) ∨
       (∃ smart body, terminalExpression = Syntax.binder smart body) ∨
       ∃ (slot : Nat) (captured : Node) (crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard))
         (originalSlot : Nat),
         terminalExpression = Syntax.var slot ∧
         terminalInputs[slot]? = some captured ∧ RowAt captured fullRow ∧
         InternedFreshOrdinaryActiveOrigins.Path (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
           (Syntax.var slot) terminalInputs crossings ∧
         slot = crossings.length + originalSlot ∧
         (leaves siteBody)[originalSlot]? = some captured ∧ captured.free = [] ∧
         ∀ (entry : Interned NodeKey) (body depth ordinary : Node),
           captured = .mu entry body depth ordinary → RowAt body fullRow ∧
             ((before.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
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
      (∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
        ∃ expressions inputs before raw after rows middle,
        ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
          producerIndex ≤ outerIndex ∧ (events path)[producerIndex]? = some producer ∧
          SyntaxBound (Syntax.node expressions) producer.expression ∧
          UnionDescent producer.expression (Syntax.node expressions) ∧
          Context before inputs ∧ Reached original [] (Syntax.node expressions) inputs before ∧
          SourceRow (Syntax.node expressions) inputs before raw after fullRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some fullRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = fullRow ∧ Grows after outer.afterBody ∧
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
        current.native.machine.heap)) := by
  obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
      terminalSource,nonunion,terminalContext,terminalReached,bound,growth,issued⟩ :=
    SourceCurrentSourceRowTerminalSuffix.terminal_source context reached source
  refine ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
    terminalSource,nonunion,terminalContext,terminalReached,bound,growth,issued,?_⟩
  cases terminalSource with
  | @capture currentInputs state value row slot found inside =>
      obtain ⟨crossings,path,_traces⟩ := terminalReached
      obtain ⟨originalSlot,offset,selected⟩ :=
        SourceCurrentSourceCaptureOriginalSlots.original_slot path slot _ found _ inside
      have closed := (InternedStoredLeafShape.leaves_shape siteBody _ (List.mem_of_getElem? selected)).resolve_right (by
        rintro ⟨name,same⟩
        rw [same] at inside
        cases inside)
      refine .inr (.inr ⟨slot,_,crossings,originalSlot,rfl,found,inside,path,offset,selected,closed,?_⟩)
      intro entry body depth ordinary same
      cases same
      have selectedInside : RowAt body fullRow := by
        cases inside with | mu inside => exact inside
      exact ⟨selectedInside,capture_same_row original sourceRoot request fuel before current pair siteBody siteNext
        sourceBuild good history actual available originalSlot entry body depth ordinary selected fullRow selectedInside⟩
  | node => exact .inl ⟨_,rfl⟩
  | binder => exact .inr (.inl ⟨_,_,rfl⟩)
  | union => exact (nonunion _ rfl).elim

end MicroCFTA.SourceCurrentNativeGeneratedRowBackedges
