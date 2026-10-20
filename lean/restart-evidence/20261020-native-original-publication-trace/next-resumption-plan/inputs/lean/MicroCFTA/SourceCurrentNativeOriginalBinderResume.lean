import MicroCFTA.SourceCurrentNativePublicationRawSuffix
import MicroCFTA.SourceCurrentNativeRootedMuStoredRows

/-!
# Original source writers of selected binder terminals

The selected full cell grows through the actual raw callback suffix.
The same completed original source build supplies its rooted writer.
That writer fixes one stored-row publication and raw callback.
-/
namespace MicroCFTA.SourceCurrentNativeOriginalBinderResume
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax request finish)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceCurrentNativeCapturedMuStoredRows (Stored)
open SourceCurrentBuildStructuralRowOrigins (SourceRow)
open SourceCurrentStoredLiteralRowLineage (RowAt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual binder terminal derives its selected original-source writer and fixed stored-row source. -/
theorem resume (original : Syntax Symbol Guard) (root : Node) (sourceHeap : Heap)
    (sourceBuilt : build original [] empty = .done root sourceHeap)
    (event : @Publication Symbol Guard _) (callbackRaw : Node) (callbackAfter : Heap)
    (context : Context event.allocated (.reference (.interned event.entry.identity) :: event.environment))
    (rawBuilt : build event.expression (.reference (.interned event.entry.identity) :: event.environment)
      event.allocated = .done callbackRaw callbackAfter)
    (filtered : run (withoutSelfReference (.interned event.entry.identity) callbackRaw) callbackAfter =
      (event.body,event.afterBody))
    (growth : Grows event.after sourceHeap)
    (issued : Extends event.after.nodes.issued sourceHeap.nodes.issued)
    (smart : Bool) (terminalExpression : Syntax Symbol Guard) (terminalInputs : List Node)
    (terminalBefore : Heap) (terminalRaw : Node) (terminalAfter : Heap) (row : EdgeValue Symbol Guard)
    (terminal : SourceRow (.binder smart terminalExpression) terminalInputs terminalBefore terminalRaw terminalAfter row)
    (suffix : Grows terminalAfter callbackAfter)
    (suffixIssued : Extends terminalAfter.nodes.issued callbackAfter.nodes.issued) :
    ∃ depth afterDepth ordinary cut entry storedBody,
      callback terminalExpression terminalInputs .depth terminalBefore = .done depth afterDepth ∧
      callback terminalExpression terminalInputs (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      request smart depth ordinary (callback terminalExpression terminalInputs) cut = .done terminalRaw terminalAfter ∧
      terminalAfter.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      sourceHeap.nodeRecords (muKey depth ordinary) = some (.mu entry storedBody depth ordinary) ∧
      terminalRaw = finish smart (.mu entry storedBody depth ordinary) ∧ RowAt storedBody row ∧
      Grows terminalAfter sourceHeap ∧ Extends terminalAfter.nodes.issued sourceHeap.nodes.issued ∧
      Written original [] empty sourceHeap (muKey depth ordinary) (.mu entry storedBody depth ordinary) ∧
      Stored original [] empty sourceHeap (muKey depth ordinary) entry storedBody depth ordinary := by
  cases terminal with
  | @binder smart expression inputs before raw after depth afterDepth ordinary cut entry body row
      depthDone ordinaryDone requested selected returned inside =>
    have callbackSuffix := SourceCurrentNativePublicationRawSuffix.callback_suffix
      event callbackRaw callbackAfter context rawBuilt filtered
    have finalGrowth : Grows terminalAfter sourceHeap :=
      grows_trans suffix (grows_trans callbackSuffix.1 growth)
    have finalIssued : Extends terminalAfter.nodes.issued sourceHeap.nodes.issued :=
      extends_trans suffixIssued (extends_trans callbackSuffix.2 issued)
    have present := finalGrowth.nodeRecords (muKey depth ordinary) _ selected
    have written := SourceCurrentCompletedBuildRootedWriters.build_writer original [] empty
      SourceCurrentConstrainedCapSourceHistory.empty_context
      (by intro key chosen storedBody storedDepth storedOrdinary impossible; cases impossible)
      root sourceHeap sourceBuilt (muKey depth ordinary) entry body depth ordinary present
    have stored := SourceCurrentNativeRootedMuStoredRows.of_written original [] empty sourceHeap
      (muKey depth ordinary) entry body depth ordinary written
    exact ⟨depth,afterDepth,ordinary,cut,entry,body,depthDone,ordinaryDone,requested,
      selected,present,returned,inside,finalGrowth,finalIssued,written,stored⟩

end MicroCFTA.SourceCurrentNativeOriginalBinderResume
