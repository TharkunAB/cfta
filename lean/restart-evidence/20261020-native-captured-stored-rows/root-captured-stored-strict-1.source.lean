import MicroCFTA.SourceCurrentNativeCapturedMuRowProduction
import MicroCFTA.SourceCurrentPublicationBodySourceRows

/-!
# Actual stored rows of an earlier captured Mu producer

One selected source writer supplies one publication and raw body callback.
Every structural stored-body row retains that same callback's source.
The earlier optional producer and its terminal row receipts stay fixed.
-/
namespace MicroCFTA.SourceCurrentNativeCapturedMuStoredRows
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentNativeEdgeWriterGrowth (History)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open InternedFreshOrdinarySourceHistory (Reached)
open SourceCurrentStoredLiteralRowLineage (RowAt)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One publication and raw callback retain every structural row of the exact stored body. -/
def Stored (root : Syntax Symbol Guard) (initial : List Node) (before reader : Heap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node) : Prop :=
  ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
    Reached root initial (.binder event.smart event.expression) event.environment event.before ∧
    key = event.key ∧ entry = event.entry ∧ body = event.body ∧ depth = event.depth ∧ ordinary = event.ordinary ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path before event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧
    Grows event.after reader ∧ Extends event.after.nodes.issued reader.nodes.issued ∧
    ∃ raw rawAfter,
      InternedFreshOrdinaryConstruction.build event.expression
        (.reference (.interned event.entry.identity) :: event.environment) event.allocated = .done raw rawAfter ∧
      run (withoutSelfReference (.interned event.entry.identity) raw) rawAfter = (event.body,event.afterBody) ∧
      Context event.allocated (.reference (.interned event.entry.identity) :: event.environment) ∧
      Reached root initial event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated ∧
      ∀ row, RowAt body row → RowAt raw row ∧
        SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated raw rawAfter row

private theorem stored (root : Syntax Symbol Guard) (initial : List Node) (before reader : Heap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (written : Written root initial before reader key (.mu entry body depth ordinary)) :
    Stored root initial before reader key entry body depth ordinary := by
  obtain ⟨event,reached,keySame,valueSame,missing,earlier,depthPath,ordinaryPath,bodyPath,growth,issued⟩ := written
  change Value.mu entry body depth ordinary = Value.mu event.entry event.body event.depth event.ordinary at valueSame
  obtain ⟨entrySame,bodySame,depthSame,ordinarySame⟩ := Value.mu.inj valueSame
  have bodyDone : InternedFreshOrdinaryFacts.callback event.expression event.environment
      (.interned event.entry.identity) event.allocated = .done event.body event.afterBody := event.bodyDone
  obtain ⟨raw,rawAfter,built,filtered⟩ := SourceCurrentNativeMuPublicationCallbacks.callback_raw
    event.expression event.environment (.interned event.entry.identity) event.allocated
    event.body event.afterBody bodyDone
  let crossing : InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard :=
    ⟨event.smart,event.expression,event.environment,event.before,.interned event.entry.identity,
      event.allocated,event.context.base,
      .fresh event.depth event.ordinary event.afterDepth event.cut
        event.depthDone event.ordinaryDone event.missing⟩
  have callbackReached : Reached root initial event.expression
      (.reference (.interned event.entry.identity) :: event.environment) event.allocated := reached.enter crossing
  obtain ⟨_,cutContext,allocatedContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have argument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut
      cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
  have context := allocatedContext.local (.interned event.entry.identity) argument
  refine ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    earlier,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,built,filtered,context,callbackReached,?_⟩
  intro row inside
  obtain ⟨other,otherAfter,otherBuilt,_,_,_,rawRow,source⟩ :=
    SourceCurrentPublicationBodySourceRows.publication_body_origin event root initial reached row (bodySame ▸ inside)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (built.symm.trans otherBuilt)
  exact ⟨rawRow,source⟩

variable [DecidableEq Symbol]

/-- The earlier captured producer retains one source callback for every stored-body row. -/
theorem capture (request : NodeRequest Symbol Guard) (fuel : Nat) (before current : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (good : Good before) (history : History before) (semantic : SemanticHeap before.native.machine.heap)
    (actual : Trace fuel (.code (requestNode request.domain request.left request.right)) before
      (.code (.optionalBinder pair siteBody siteNext)) current)
    (available : Available current.native.machine.heap siteBody)
    (index : Nat) (entry : Interned NodeKey) (body depth ordinary : Node)
    (found : (leaves siteBody)[index]? = some (.mu entry body depth ordinary)) :
    before.native.machine.heap.nodeRecords entry.key = some (.mu entry body depth ordinary) ∨
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
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary := by
  rcases SourceCurrentNativeCapturedMuRowProduction.capture request fuel before current pair siteBody siteNext
      good history semantic actual available index entry body depth ordinary found with prior | generated
  · exact .inl prior
  · obtain ⟨prefixFuel,suffixFuel,priorPair,parent,next,siteBefore,siteAfter,result,heap,total,strict,
      earlier,siteSemantic,siteAvailable,called,advanced,one,suffix,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,built,written,origin⟩ := generated
    have rows := stored _ _ _ _ entry.key entry body depth ordinary written
    exact .inr ⟨prefixFuel,suffixFuel,priorPair,parent,next,siteBefore,siteAfter,result,heap,total,strict,
      earlier,siteSemantic,siteAvailable,called,advanced,one,suffix,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,built,written,origin,rows⟩

end MicroCFTA.SourceCurrentNativeCapturedMuStoredRows
