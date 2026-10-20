import MicroCFTA.SourceCurrentCompletedBuildRootedWriters
import MicroCFTA.SourceEqualityRequiredCache

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.CompletedBuildRootedWriterKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (NodeKey)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentCompletedBuildRootedWriters (Written)
open SourceEqualityRequiredCache (Ready)
local notation "Node" => Value Nat Bool
local notation "Heap" => State Nat Bool

private def firstSource : Syntax Nat Bool := .binder true (.node [.mk 7 false [.var 0]])
private def secondSource : Syntax Nat Bool := .binder true (.union [.empty,.node [.mk 7 false [.var 0]]])
private def source : Syntax Nat Bool := .union [firstSource,secondSource]
private def outcomeValue (actual : Outcome Nat Bool Node) : Node :=
  match actual with | .done value _ => value | .pending .. => .empty
private def firstRun := build firstSource [] empty
private def selected : Node := outcomeValue firstRun
private def firstAfter : Heap := firstRun.state
private def fullRun := build source [] empty
private def final : Heap := fullRun.state
private def entry := match selected with
  | .mu entry _ _ _ => entry
  | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def body : Node := match selected with | .mu _ body _ _ => body | _ => .empty
private def depth : Node := match selected with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary : Node := match selected with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def key := muKey depth ordinary

private theorem first_done : build firstSource [] empty = .done selected firstAfter := by cbv
private theorem second_warm : build secondSource [] firstAfter = .done selected firstAfter := by cbv
private theorem full_done : build source [] empty = .done selected final := by cbv
private theorem same_final : final = firstAfter := by cbv
private theorem shape : selected = .mu entry body depth ordinary := by cbv
private theorem present : final.nodeRecords key = some (.mu entry body depth ordinary) := by cbv
private theorem first_present : firstAfter.nodeRecords key = some (.mu entry body depth ordinary) := by
  rw [←same_final]
  exact present
private theorem warm_key : firstAfter.nodes.table key = some entry := by cbv
private theorem used : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true := by cbv
private theorem distinct_sources : firstSource ≠ secondSource := by
  intro same
  change Syntax.binder true (.node [.mk 7 false [.var 0]]) =
    Syntax.binder true (.union [.empty,.node [.mk 7 false [.var 0]]]) at same
  cases same
private theorem final_ready : Ready final :=
  SourceEqualityRequiredCache.constructed source selected final full_done
private theorem final_available : Available final selected :=
  (InternedFreshOrdinaryFacts.closed_verified source).result selected final full_done
private theorem rooted : Written source [] empty final key (.mu entry body depth ordinary) :=
  SourceCurrentCompletedBuildRootedWriters.build_writer source [] empty
    SourceCurrentConstrainedCapSourceHistory.empty_context
    (by intro key entry body depth ordinary impossible; cases impossible)
    selected final full_done key entry body depth ordinary present

private theorem warm_classification :
    firstAfter.nodeRecords key = some (.mu entry body depth ordinary) ∨
      Written secondSource [] firstAfter firstAfter key (.mu entry body depth ordinary) := by
  have context : Context firstAfter [] := by
    simpa only [first_done,Outcome.state] using
      SourceCurrentConstrainedCapSourceHistory.empty_context.build firstSource
  exact SourceCurrentCompletedBuildRootedWriters.build_writer_or_prior secondSource [] firstAfter
    context selected firstAfter second_warm key entry body depth ordinary first_present

private def Claim : Prop :=
  firstSource ≠ secondSource ∧
  build firstSource [] empty = .done selected firstAfter ∧
  firstAfter.nodes.table key = some entry ∧
  firstAfter.nodeRecords key = some (.mu entry body depth ordinary) ∧
  build secondSource [] firstAfter = .done selected firstAfter ∧
  build source [] empty = .done selected final ∧ final = firstAfter ∧
  selected = .mu entry body depth ordinary ∧ Ready final ∧ Available final selected ∧
  InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
  final.nodeRecords key = some (.mu entry body depth ordinary) ∧
  Written source [] empty final key (.mu entry body depth ordinary) ∧
  (firstAfter.nodeRecords key = some (.mu entry body depth ordinary) ∨
    Written secondSource [] firstAfter firstAfter key (.mu entry body depth ordinary)) ∧
  ∃ event : Publication (Symbol := Nat) (Guard := Bool),
    InternedFreshOrdinarySourceHistory.Reached source []
      (.binder event.smart event.expression) event.environment event.before ∧
    key = event.key ∧ .mu entry body depth ordinary = event.candidate ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty event.before) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path event.before event.afterDepth) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path event.afterDepth event.cut) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path event.allocated event.afterBody) ∧
    Grows event.after final ∧ Extends event.after.nodes.issued final.nodes.issued ∧
    SourceCurrentNativeMuIssuedWriters.Written empty final key (.mu entry body depth ordinary)

private theorem checked_witness : Claim := by
  refine ⟨distinct_sources,first_done,warm_key,first_present,second_warm,full_done,same_final,
    shape,final_ready,final_available,used,present,rooted,warm_classification,?_⟩
  obtain ⟨event,site,keySame,valueSame,missing,earlier,depthPath,ordinaryPath,bodyPath,growth,issued⟩ := rooted
  exact ⟨event,site,keySame,valueSame,missing,earlier,depthPath,ordinaryPath,bodyPath,growth,issued,
    ⟨event,keySame,valueSame,missing,earlier,depthPath,ordinaryPath,bodyPath,growth,issued⟩⟩

/-- Two actual source binders retain one selected used Mu with a rooted issued writer. -/
theorem witness :
  firstSource ≠ secondSource ∧
  build firstSource [] empty = .done selected firstAfter ∧
  firstAfter.nodes.table key = some entry ∧
  firstAfter.nodeRecords key = some (.mu entry body depth ordinary) ∧
  build secondSource [] firstAfter = .done selected firstAfter ∧
  build source [] empty = .done selected final ∧ final = firstAfter ∧
  selected = .mu entry body depth ordinary ∧ Ready final ∧ Available final selected ∧
  InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
  final.nodeRecords key = some (.mu entry body depth ordinary) ∧
  Written source [] empty final key (.mu entry body depth ordinary) ∧
  (firstAfter.nodeRecords key = some (.mu entry body depth ordinary) ∨
    Written secondSource [] firstAfter firstAfter key (.mu entry body depth ordinary)) ∧
  ∃ event : Publication (Symbol := Nat) (Guard := Bool),
    InternedFreshOrdinarySourceHistory.Reached source []
      (.binder event.smart event.expression) event.environment event.before ∧
    key = event.key ∧ .mu entry body depth ordinary = event.candidate ∧
    event.afterBody.nodeRecords event.key = none ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty event.before) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path event.before event.afterDepth) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path event.afterDepth event.cut) ∧
    Nonempty (SourceCurrentNativeMuIssuedHistory.Path event.allocated event.afterBody) ∧
    Grows event.after final ∧ Extends event.after.nodes.issued final.nodes.issued ∧
    SourceCurrentNativeMuIssuedWriters.Written empty final key (.mu entry body depth ordinary)
 := checked_witness

end MicroCFTA.CompletedBuildRootedWriterKernels
