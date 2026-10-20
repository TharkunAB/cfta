import MicroCFTA.SourceCurrentNativeCapturedMuStoredRows

/-!
# Fixed stored-row provenance from a public rooted writer

The published capture module keeps its writer conversion private.
This additive public adapter retains its fixed publication and callback.
Every stored row uses that same selected source interval.
-/
namespace MicroCFTA.SourceCurrentNativeRootedMuStoredRows
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (NodeKey)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceCurrentNativeCapturedMuStoredRows (Stored)
open InternedFreshOrdinarySourceHistory (Reached)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The supplied rooted writer fixes one publication and raw callback before all stored rows. -/
theorem of_written (root : Syntax Symbol Guard) (initial : List Node) (before reader : Heap)
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

end MicroCFTA.SourceCurrentNativeRootedMuStoredRows
