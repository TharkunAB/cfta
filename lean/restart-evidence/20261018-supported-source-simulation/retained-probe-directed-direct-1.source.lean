import MicroCFTA.SourceCurrentNativeBinderExecution
import MicroCFTA.SourceCurrentNativeRequestProbes
import MicroCFTA.SourceCurrentNativeMuGrowthWriters
import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.SourceCurrentOpenObservations
import MicroCFTA.InternedFreshOrdinaryReplay

/-!
# Actual retained-probe reconstruction schedules

A completed source binder supplies its own exact probes. The selected
record retains those complete probes even when an earlier source wrote
its body. Actual causal reader history recovers that writer. Initial
Ready data constructs the selected Mu unfolding and ordinary-probe
reconstruction. Their endpoints can seed a relation before its local
simulation laws are proved. No observation relation is assumed or proved.
-/
namespace MicroCFTA.SourceCurrentRetainedProbeSchedule
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request finish)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference)
open InternedNestedProvenance (Values)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentNativeMuGrowthHistory (Path)
open SourceEqualityRequiredCache (Keeps)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual requester probes and one selected writer supply concrete reconstruction generator endpoints. -/
def Seed (smart : Bool) (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (result : Value Symbol Guard) (after reader : State Symbol Guard) : Prop :=
  ∃ depth afterDepth ordinary cut raw rawHeap entry body
      (event : Publication (Symbol := Symbol) (Guard := Guard)),
    callback expression environment .depth before = .done depth afterDepth ∧
    callback expression environment (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
    request smart depth ordinary (callback expression environment) cut = .done result after ∧
    build expression (.reference (.uninterned (ordinaryLevel depth)) :: environment) afterDepth = .done raw rawHeap ∧
    run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) rawHeap = (ordinary,cut) ∧
    Context afterDepth environment ∧ Context cut environment ∧
    Context rawHeap (.reference (.uninterned (ordinaryLevel depth)) :: environment) ∧ Context reader environment ∧
    Grows before reader ∧ Extends before.nodes.issued reader.nodes.issued ∧
    Grows rawHeap reader ∧ Extends rawHeap.nodes.issued reader.nodes.issued ∧
    reader.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
    Available reader (.mu entry body depth ordinary) ∧
    result = finish smart (.mu entry body depth ordinary) ∧
    muKey depth ordinary = event.key ∧ .mu entry body depth ordinary = event.candidate ∧
    event.entry = entry ∧ event.body = body ∧ event.depth = depth ∧ event.ordinary = ordinary ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path empty event.before) ∧ Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧ Nonempty (Path event.allocated event.afterBody) ∧
    Grows event.after reader ∧
    ∃ left middle right final,
      unfold (.mu entry body depth ordinary) reader = .done left middle ∧
      execute ordinary
        (fun name => if name = .uninterned (ordinaryLevel depth) then some (.mu entry body depth ordinary) else none)
        middle = .done right final ∧
      unfold (.mu entry body depth ordinary) final = .done left final ∧
      execute ordinary
        (fun name => if name = .uninterned (ordinaryLevel depth) then some (.mu entry body depth ordinary) else none)
        final = .done right final ∧
      left ∈ MergedFreshOrdinaryGraph.successors reader (.mu entry body depth ordinary) ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (History reader middle) ∧ Nonempty (History middle final) ∧
      final.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary)

/-- Literal source execution and causal reader history derive the seed without supplied writer or endpoints. -/
theorem binder (smart : Bool) (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (context : Context before environment)
    (actual : build (.binder smart expression) environment before = .done result after)
    (reader : State Symbol Guard) (current : Keeps after reader) (history : Path empty reader) :
    Seed smart expression environment before result after reader := by
  obtain ⟨depth,afterDepth,ordinary,cut,raw,rawHeap,depthDone,ordinaryDone,requested,
    depthContext,cutContext,afterContext,rawDone,filtered,rawContext,rawGrowth,rawIssued,depthAvailable,ordinaryAvailable⟩ :=
    SourceCurrentNativeBinderExecution.decompose smart expression environment before result after context actual
  obtain ⟨entry,body,present,returned⟩ := SourceCurrentNativeRequestProbes.request_probes smart depth ordinary
    (callback expression environment) cut result after requested afterContext.base.normal.facts depthAvailable ordinaryAvailable
  have selected := current.growth.nodeRecords (muKey depth ordinary) (.mu entry body depth ordinary) present
  have available := current.ready.semantic.1.normal.facts.cached.nodes (muKey depth ordinary) _ selected
  have written := SourceCurrentNativeMuGrowthWriters.from_empty history (muKey depth ordinary) entry body depth ordinary selected
  obtain ⟨event,keySame,valueSame,missing,prefix,depthPath,ordinaryPath,bodyPath,writerGrowth⟩ := written
  have payload : Value.mu entry body depth ordinary = Value.mu event.entry event.body event.depth event.ordinary := valueSame
  obtain ⟨sameEntry,sameBody,sameDepth,sameOrdinary⟩ := Value.mu.inj payload
  have checked := build_verified (.binder smart expression) environment before context.base.normal.facts context.base.inputs
  have initialGrowth : Grows before after := by simpa only [actual,Outcome.state] using checked.growth
  have initialIssued : Extends before.nodes.issued after.nodes.issued := by simpa only [actual,Outcome.state] using checked.history
  have inputs : Values reader environment := fun value member => current.available value (afterContext.base.inputs value member)
  have readerContext : Context reader environment :=
    ⟨SourceRecursiveIntersectionSemanticHeap.context reader current.ready.semantic environment inputs,current.ready.semantic.2⟩
  obtain ⟨left,middle,right,final,firstDone,secondDone,firstKept,secondKept,leftAvailable,rightAvailable,
    firstHistory,secondHistory,retained⟩ :=
    SourceCurrentStoredReconstruction.mu (muKey depth ordinary) entry body depth ordinary (.mu entry body depth ordinary)
      reader current.ready selected available
  have firstWarm := InternedFreshOrdinaryReplay.build_replay (encode (leaves body) [] body)
    ((leaves body).map (InternedStoredSubstitution.input
      (fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none)))
    reader final left middle current.ready.semantic.1.normal.facts.coherent.valid firstDone secondKept.growth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay (encode (leaves ordinary) [] ordinary)
    ((leaves ordinary).map (InternedStoredSubstitution.input
      (fun name => if name = .uninterned (ordinaryLevel depth) then some (.mu entry body depth ordinary) else none)))
    middle final right final firstKept.ready.semantic.1.normal.facts.coherent.valid secondDone (grows_refl _)
  have unfolded : unfold (.mu entry body depth ordinary) reader = .done left middle := firstDone
  have epsilon : left ∈ MergedFreshOrdinaryGraph.successors reader (.mu entry body depth ordinary) := by
    simp only [MergedFreshOrdinaryGraph.successors,unfolded,List.mem_singleton]
  exact ⟨depth,afterDepth,ordinary,cut,raw,rawHeap,entry,body,event,depthDone,ordinaryDone,requested,rawDone,filtered,
    depthContext,cutContext,rawContext,readerContext,grows_trans initialGrowth current.growth,
    extends_trans initialIssued current.history,grows_trans rawGrowth current.growth,extends_trans rawIssued current.history,
    selected,available,returned,keySame,valueSame,sameEntry.symm,sameBody.symm,sameDepth.symm,sameOrdinary.symm,
    missing,prefix,depthPath,ordinaryPath,bodyPath,writerGrowth,
    left,middle,right,final,unfolded,secondDone,firstWarm,secondWarm,epsilon,firstKept,secondKept,
    leftAvailable,rightAvailable,firstHistory,secondHistory,retained⟩

end MicroCFTA.SourceCurrentRetainedProbeSchedule
