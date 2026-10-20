import MicroCFTA.SourceCurrentNativeCapturedMuStoredRows
import MicroCFTA.SourceCurrentStoredLiteralRowLineage
import MicroCFTA.SourceCurrentNativePublicationTrace

/-!
# Actual unfolded rows of an earlier captured Mu producer

An actual unfold retains the fields and child calls of a stored row.
That stored row reaches the same earlier publication and raw callback.
The actual prefix derives causal history at the active reader.
-/
namespace MicroCFTA.SourceCurrentNativeCapturedMuUnfoldRows
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

open SourceCurrentLiteralRootParts (Row)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceCurrentNativeMuWriterSourceRows (Anchor)
open SourceCurrentNativeCapturedMuStoredRows (Stored)

/-- One fixed source callback retains stored anchors for every actual unfold at the same reader. -/
def Observed (root : Syntax Symbol Guard) (initial : List Node) (before reader : Heap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node) (current : Heap) : Prop :=
  ∃ event : @Publication Symbol Guard _,
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
      (∀ row, RowAt body row → RowAt raw row ∧
        SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated raw rawAfter row) ∧
      ∀ value after,
        InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) current = .done value after →
        SemanticHeap after ∧ Grows current after ∧ Extends current.nodes.issued after.nodes.issued ∧
          Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
          ∀ row, Row value row →
        ∃ original, RowAt body original ∧ row.entry.key.symbol = original.entry.key.symbol ∧
          row.entry.key.constraint = original.entry.key.constraint ∧ row.children.length = original.children.length ∧
          (row = original ∨ ∃ lexical current next, Calls lexical original.children current row.children next) ∧
          RowAt raw original ∧
          SourceRow event.expression (.reference (.interned event.entry.identity) :: event.environment)
            event.allocated raw rawAfter original

/-- Actual unfolded rows retain complete stored row fields and ordered child calls, including nullary rows. -/
theorem unfold_rows (entry : Interned NodeKey) (body depth ordinary : Node)
    (current : Heap) (semantic : SemanticHeap current)
    (available : Available current (.mu entry body depth ordinary))
    (publications : SourceCurrentNativeMuPublication.History empty current)
    (value : Node) (after : Heap)
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) current =
      .done value after) :
    SemanticHeap after ∧ Grows current after ∧ Extends current.nodes.issued after.nodes.issued ∧
      Available after value ∧ Nonempty (SourceCurrentNativeMuPublication.History empty after) ∧
      ∀ row, Row value row → Anchor body row := by
  let environment : InternedStoredSubstitution.Environment Symbol Guard := fun name =>
    if name = .interned entry.identity then some (.mu entry body depth ordinary) else none
  have replacements : InternedStoredSubstitution.Replacements current environment := by
    intro name replacement found
    dsimp only [environment] at found
    split at found
    · cases found; exact available
    · cases found
  have bodyAvailable := available.children body (by simp [children])
  have called : InternedFreshOrdinaryStoredSubstitution.execute body environment current = .done value after := actual
  have effects := SourceCurrentStoredLiteralCalls.execute body environment current semantic bodyAvailable
    replacements value after called
  let inputs := (leaves body).map (InternedStoredSubstitution.input environment)
  have inputsAvailable := InternedStoredSubstitution.inputs_available body environment current bodyAvailable replacements
  have context : Context current inputs :=
    ⟨SourceRecursiveIntersectionSemanticHeap.context current semantic inputs inputsAvailable,semantic.2⟩
  have interval := SourceCurrentNativeMuPublication.build_history (encode (leaves body) [] body) inputs current context
  change Nonempty (SourceCurrentNativeMuPublication.History current
    (InternedFreshOrdinaryStoredSubstitution.execute body environment current).state) at interval
  rw [called,InternedNestedConstruction.Outcome.state] at interval
  obtain ⟨segment⟩ := interval
  have published := publications.trans segment
  refine ⟨effects.1,effects.2.1,effects.2.2.1,effects.2.2.2.1,⟨published⟩,?_⟩
  intro row literal
  have origin := SourceCurrentStoredLiteralRowLineage.execute_row body environment current semantic
    bodyAvailable replacements value after called after published (grows_refl after) row literal
  apply SourceCurrentStoredLiteralRowLineage.source_row origin
  intro name replacement found impossible
  dsimp only [environment] at found
  split at found
  · cases found; cases impossible
  · cases found

/-- The supplied publication stays fixed across every successful unfold at the same current heap. -/
theorem observe (root : Syntax Symbol Guard) (initial : List Node) (before reader : Heap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : Stored root initial before reader key entry body depth ordinary)
    (current : Heap) (semantic : SemanticHeap current)
    (available : Available current (.mu entry body depth ordinary))
    (publications : SourceCurrentNativeMuPublication.History empty current) :
    Observed root initial before reader key entry body depth ordinary current := by
  obtain ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    earlier,depthPath,ordinaryPath,bodyPath,lastGrowth,lastIssued,raw,rawAfter,built,filtered,context,
    callbackReached,rows⟩ := stored
  refine ⟨event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    earlier,depthPath,ordinaryPath,bodyPath,lastGrowth,lastIssued,raw,rawAfter,built,filtered,context,
    callbackReached,rows,?_⟩
  intro value after actual
  obtain ⟨semanticAfter,growth,issued,output,published,anchors⟩ :=
    unfold_rows entry body depth ordinary current semantic available publications value after actual
  refine ⟨semanticAfter,growth,issued,output,published,?_⟩
  intro row literal
  obtain ⟨original,inside,symbol,guard,arity,calls⟩ := anchors row literal
  obtain ⟨rawRow,source⟩ := rows original inside
  exact ⟨original,inside,symbol,guard,arity,calls,rawRow,source⟩

variable [DecidableEq Symbol]

/-- One actual capture derives same-publication row origins for every successful unfold at that reader. -/
theorem capture (request : NodeRequest Symbol Guard) (fuel : Nat) (before current : Checked width)
    (pair : Nat × Nat) (siteBody : Node) (siteNext : Node → Code Symbol Guard Node)
    (good : Good before) (history : History before) (semantic : SemanticHeap before.native.machine.heap)
    (publications : SourceCurrentNativeMuPublication.History empty before.native.machine.heap)
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
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary ∧
      Observed (.binder true (encode (leaves parent) [.intersection priorPair.1 priorPair.2] parent))
        (leaves parent) siteBefore.native.machine.heap heap entry.key entry body depth ordinary
        current.native.machine.heap := by
  rcases SourceCurrentNativeCapturedMuStoredRows.capture request fuel before current pair siteBody siteNext
      good history semantic actual available index entry body depth ordinary found with prior | generated
  · exact .inl prior
  · obtain ⟨prefixFuel,suffixFuel,priorPair,parent,next,siteBefore,siteAfter,result,heap,total,strict,
      earlier,siteSemantic,siteAvailable,called,advanced,one,suffix,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,built,written,origin,stored⟩ := generated
    have captured := InternedStoredSubstitution.leaves_available siteBody current.native.machine.heap available
      (.mu entry body depth ordinary) (List.mem_of_getElem? found)
    obtain ⟨currentSemantic,⟨published⟩⟩ :=
      SourceCurrentNativePublicationTrace.from_history actual semantic publications
    exact .inr ⟨prefixFuel,suffixFuel,priorPair,parent,next,siteBefore,siteAfter,result,heap,total,strict,
      earlier,siteSemantic,siteAvailable,called,advanced,one,suffix,missing,present,
      prefixGrowth,prefixIssued,suffixGrowth,suffixIssued,used,context,built,written,origin,stored,
      observe _ _ _ _ entry.key entry body depth ordinary stored current.native.machine.heap
        currentSemantic captured published⟩

end MicroCFTA.SourceCurrentNativeCapturedMuUnfoldRows
