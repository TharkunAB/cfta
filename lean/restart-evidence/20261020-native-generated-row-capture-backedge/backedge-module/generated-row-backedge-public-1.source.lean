import MicroCFTA.SourceCurrentNativeOriginalCapturedNodeRows
import MicroCFTA.SourceCurrentSourceRowTerminalSuffix
import MicroCFTA.SourceCurrentSourceCaptureOriginalSlots
import MicroCFTA.InternedStoredLeafShape

namespace MicroCFTA.SourceCurrentNativeGeneratedRowCaptureBackedge
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome work request)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
section SourceDone
variable {Symbol Guard : Type}

private theorem source_done [DecidableEq (EdgeKey Symbol Guard)]
    {expression : Syntax Symbol Guard} {inputs : List (Value Symbol Guard)}
    {before : State Symbol Guard} {raw : Value Symbol Guard} {after : State Symbol Guard}
    {row : EdgeValue Symbol Guard} (source : SourceRow expression inputs before raw after row) :
    build expression inputs before = .done raw after := by
  cases source with
  | capture found _ => simp only [build,found,Option.getD_some]
  | node built made _ _ _ => simp only [build,built,Outcome.bind,work,made]
  | union built made _ _ _ _ _ _ _ => simp only [build,built,Outcome.bind,work,made]
  | @binder smart expression inputs before raw after depth afterDepth ordinary cut entry body row
      depthDone ordinaryDone requested _ _ _ =>
    simp only [build]
    change ((callback expression inputs .depth before).bind fun depth afterDepth =>
      (callback expression inputs (.uninterned (ordinaryLevel depth)) afterDepth).bind
        fun ordinary cut => request smart depth ordinary (callback expression inputs) cut) = .done raw after
    simpa only [depthDone,ordinaryDone,Outcome.bind] using requested

end SourceDone

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
    (targetKey : NodeKey) (targetMissing : current.native.machine.heap.nodeRecords targetKey = none)
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
           Available current.native.machine.heap (.mu entry body depth ordinary) ∧
           current.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
           entry.key ≠ targetKey ∧
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
      have capturedAvailable := InternedStoredSubstitution.leaves_available siteBody current.native.machine.heap
        available (.mu entry body depth ordinary) (List.mem_of_getElem? selected)
      have resident := capturedAvailable.resident entry rfl
      have distinct : entry.key ≠ targetKey := by
        intro sameKey
        rw [sameKey,targetMissing] at resident
        cases resident
      exact ⟨selectedInside,capturedAvailable,resident,distinct,
        capture_same_row original sourceRoot request fuel before current pair siteBody siteNext
        sourceBuild good history actual available originalSlot entry body depth ordinary selected fullRow selectedInside⟩
  | node => exact .inl ⟨_,rfl⟩
  | binder => exact .inr (.inl ⟨_,_,rfl⟩)
  | union => exact (nonunion _ rfl).elim


/-- An executed generated callback row retains its exact capture and an earlier native producer. -/
theorem generated_row_capture_backedge (original : Syntax Symbol Guard) (sourceRoot : Node)
    (request : NodeRequest Symbol Guard) (fuel : Nat) (before current : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (sourceBuild : build original [] empty = .done sourceRoot before.native.machine.heap)
    (good : Good before) (history : History before)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) current)
    (available : Available current.native.machine.heap siteBody)
    (result : Node) (generatedHeap : Heap)
    (executed : SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody current.native.machine.heap = .done result generatedHeap)
    (generatedBuild : build (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody))
      (leaves siteBody) current.native.machine.heap = .done result generatedHeap)
    (initialNonempty : leaves siteBody ≠ [])
    (targetEntry : Interned NodeKey) (targetBody targetDepth targetOrdinary : Node)
    (targetMissing : current.native.machine.heap.nodeRecords targetEntry.key = none)
    (targetSelected : generatedHeap.nodeRecords targetEntry.key =
      some (.mu targetEntry targetBody targetDepth targetOrdinary))
    (reader : Heap)
    (observed : Observed (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody))
      (leaves siteBody) current.native.machine.heap generatedHeap targetEntry.key
      targetEntry targetBody targetDepth targetOrdinary reader) :
    SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody current.native.machine.heap = .done result generatedHeap ∧
    build (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody))
      (leaves siteBody) current.native.machine.heap = .done result generatedHeap ∧
    leaves siteBody ≠ [] ∧
    current.native.machine.heap.nodeRecords targetEntry.key = none ∧
    generatedHeap.nodeRecords targetEntry.key = some (.mu targetEntry targetBody targetDepth targetOrdinary) ∧
    ∃ event : @Publication Symbol Guard _,
      Reached (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody))
        (leaves siteBody) (.binder event.smart event.expression) event.environment event.before ∧
      targetEntry.key = event.key ∧ targetEntry = event.entry ∧ targetBody = event.body ∧
      targetDepth = event.depth ∧ targetOrdinary = event.ordinary ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path current.native.machine.heap event.before) ∧
      Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧
      Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after generatedHeap ∧ Extends event.after.nodes.issued generatedHeap.nodes.issued ∧
      ∃ raw rawAfter,
        build event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated = .done raw rawAfter ∧
        run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
        Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
        Reached (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody))
          (leaves siteBody) event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated ∧
        (∀ storedRow, RowAt targetBody storedRow → RowAt raw storedRow ∧
          SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated raw rawAfter storedRow ∧
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter storedRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody) terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ edges, terminalExpression = Syntax.node edges) ∨
       (∃ smart body, terminalExpression = Syntax.binder smart body) ∨
       ∃ (slot : Nat) (captured : Node) (crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard))
         (originalSlot : Nat),
         terminalExpression = Syntax.var slot ∧
         terminalInputs[slot]? = some captured ∧ RowAt captured storedRow ∧
         InternedFreshOrdinaryActiveOrigins.Path (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
           (Syntax.var slot) terminalInputs crossings ∧
         slot = crossings.length + originalSlot ∧
         (leaves siteBody)[originalSlot]? = some captured ∧ captured.free = [] ∧
         ∀ (entry : Interned NodeKey) (body depth ordinary : Node),
           captured = .mu entry body depth ordinary → RowAt body storedRow ∧
           Available current.native.machine.heap (.mu entry body depth ordinary) ∧
           current.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
           entry.key ≠ targetEntry.key ∧
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
        current.native.machine.heap))) ∧
        ∀ value after,
          InternedFreshOrdinaryStoredSubstitution.unfold (.mu targetEntry targetBody targetDepth targetOrdinary)
            reader = .done value after →
          SemanticHeap after ∧ Grows reader after ∧ Extends reader.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
          ∃ originalRow, RowAt targetBody originalRow ∧
            row.entry.key.symbol = originalRow.entry.key.symbol ∧
            row.entry.key.constraint = originalRow.entry.key.constraint ∧
            row.children.length = originalRow.children.length ∧
            (row = originalRow ∨ ∃ lexical current next, Calls lexical originalRow.children current row.children next) ∧
            RowAt raw originalRow ∧
            SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
              event.allocated raw rawAfter originalRow ∧
    ∃ terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter,
      SourceRow terminalExpression terminalInputs terminalBefore terminalRaw terminalAfter originalRow ∧
      build terminalExpression terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
      (∀ members, terminalExpression ≠ Syntax.union members) ∧
      Context terminalBefore terminalInputs ∧
      Reached (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody) terminalExpression terminalInputs terminalBefore ∧
      SyntaxBound terminalExpression event.expression ∧
      Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
      ((∃ edges, terminalExpression = Syntax.node edges) ∨
       (∃ smart body, terminalExpression = Syntax.binder smart body) ∨
       ∃ (slot : Nat) (captured : Node) (crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard))
         (originalSlot : Nat),
         terminalExpression = Syntax.var slot ∧
         terminalInputs[slot]? = some captured ∧ RowAt captured originalRow ∧
         InternedFreshOrdinaryActiveOrigins.Path (.binder true (encode (leaves siteBody) [.intersection pair.1 pair.2] siteBody)) (leaves siteBody)
           (Syntax.var slot) terminalInputs crossings ∧
         slot = crossings.length + originalSlot ∧
         (leaves siteBody)[originalSlot]? = some captured ∧ captured.free = [] ∧
         ∀ (entry : Interned NodeKey) (body depth ordinary : Node),
           captured = .mu entry body depth ordinary → RowAt body originalRow ∧
           Available current.native.machine.heap (.mu entry body depth ordinary) ∧
           current.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∧
           entry.key ≠ targetEntry.key ∧
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
          SourceRow (Syntax.node expressions) inputs before raw after originalRow ∧
          build (Syntax.node expressions) inputs before = .done raw after ∧
          buildEdges expressions inputs before = .done rows middle ∧
          run (makeNode rows) middle = (raw,after) ∧
          (nodeEdges raw)[outputIndex]? = some originalRow ∧
          ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
            call.output = originalRow ∧ Grows after outer.afterBody ∧
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
  obtain ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    prefixPath,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,built,filtered,
    context,callbackReached,rows,unfolds⟩ := observed
  refine ⟨executed,generatedBuild,initialNonempty,targetMissing,targetSelected,event,reached,
    keySame,entrySame,bodySame,depthSame,ordinarySame,missing,prefixPath,depthPath,ordinaryPath,
    bodyPath,growth,issued,raw,rawAfter,built,filtered,context,callbackReached,?_,?_⟩
  · intro storedRow inside
    obtain ⟨rawRow,source⟩ := rows storedRow inside
    obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
      terminalSource,nonunion,terminalContext,terminalReached,bound,suffix,suffixIssued,classification⟩ :=
      generated_terminal original sourceRoot request fuel before current pair siteBody siteNext
        sourceBuild good history actual available targetEntry.key targetMissing event.expression
        (.reference (.interned event.entry.identity) :: event.environment) event.allocated raw rawAfter
        storedRow context callbackReached source
    exact ⟨rawRow,source,terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
      terminalSource,source_done terminalSource,nonunion,terminalContext,terminalReached,bound,
      suffix,suffixIssued,classification⟩
  · intro value after actualUnfold
    obtain ⟨semanticAfter,unfoldGrowth,unfoldIssued,outputAvailable,publications,anchors⟩ :=
      unfolds value after actualUnfold
    refine ⟨semanticAfter,unfoldGrowth,unfoldIssued,outputAvailable,publications,?_⟩
    intro row literal
    obtain ⟨originalRow,originalInside,symbol,guard,arity,calls,rawRow,source⟩ := anchors row literal
    obtain ⟨terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
      terminalSource,nonunion,terminalContext,terminalReached,bound,suffix,suffixIssued,classification⟩ :=
      generated_terminal original sourceRoot request fuel before current pair siteBody siteNext
        sourceBuild good history actual available targetEntry.key targetMissing event.expression
        (.reference (.interned event.entry.identity) :: event.environment) event.allocated raw rawAfter
        originalRow context callbackReached source
    exact ⟨originalRow,originalInside,symbol,guard,arity,calls,rawRow,source,
      terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
      terminalSource,source_done terminalSource,nonunion,terminalContext,terminalReached,bound,
      suffix,suffixIssued,classification⟩

end MicroCFTA.SourceCurrentNativeGeneratedRowCaptureBackedge

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentNativeGeneratedRowCaptureBackedge.generated_row_capture_backedge
#print MicroCFTA.SourceCurrentNativeGeneratedRowCaptureBackedge.generated_row_capture_backedge
#print axioms MicroCFTA.SourceCurrentNativeGeneratedRowCaptureBackedge.generated_row_capture_backedge
