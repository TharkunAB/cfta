import MicroCFTA.SourceCurrentStoppingBuildRootedWriters

/-!
# A new rooted writer at an actual pending source state

Actual callbacks prepare the blocked key. Reservation leaves its record
absent. A different raw binder completes before the blocked source request.
The union stops at that request. The selected writer comes from one call to
the stopping producer. The initial-cell alternative is excluded by lookup.
-/
namespace MicroCFTA.StoppingRootedWritersFixture
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedFreshOrdinarySourceHistory (Reached)
open InternedBinderProtocol (NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentStoppingBuildRootedWriters (build_writer_or_prior)
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 10000000
local notation "Node" => Value Nat Bool
local notation "Heap" => State Nat Bool

private def blockedBody : Syntax Nat Bool := .node [.mk 7 true []]
private def blockedSource : Syntax Nat Bool := .binder false blockedBody
private def targetSource : Syntax Nat Bool := .binder false (.node [.mk 9 true []])
private def source : Syntax Nat Bool := .union [targetSource,blockedSource]
private def valueOf (outcome : Outcome Nat Bool Node) : Node :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def depthRun := callback blockedBody [] .depth (empty : Heap)
private def preparedDepth : Node := valueOf depthRun
private def afterDepth : Heap := depthRun.state
private def ordinaryRun := callback blockedBody [] (.uninterned (ordinaryLevel preparedDepth)) afterDepth
private def preparedOrdinary : Node := valueOf ordinaryRun
private def cut : Heap := ordinaryRun.state
private def blockedKey : NodeKey := muKey preparedDepth preparedOrdinary
private def blockedEntry := (Cache.intern cut.nodes blockedKey).1
private def reserved : Heap := {cut with nodes := (Cache.intern cut.nodes blockedKey).2}
private def targetRun := build targetSource [] reserved
private def target : Node := valueOf targetRun
private def afterTarget : Heap := targetRun.state
private def entry := match target with
  | .mu entry _ _ _ => entry
  | _ => (Cache.intern (empty : Heap).nodes .empty).1
private def body : Node := match target with | .mu _ body _ _ => body | _ => .empty
private def depth : Node := match target with | .mu _ _ depth _ => depth | _ => .empty
private def ordinary : Node := match target with | .mu _ _ _ ordinary => ordinary | _ => .empty
private def targetKey : NodeKey := muKey depth ordinary

private theorem initial_context : Context (empty : Heap) [] :=
  SourceCurrentConstrainedCapSourceHistory.empty_context
private theorem depth_done : callback blockedBody [] .depth (empty : Heap) =
    .done preparedDepth afterDepth := by cbv
private theorem ordinary_done : callback blockedBody [] (.uninterned (ordinaryLevel preparedDepth)) afterDepth =
    .done preparedOrdinary cut := by cbv
private theorem cut_missing : cut.nodes.table blockedKey = none := by cbv
private theorem reserved_table : reserved.nodes.table blockedKey = some blockedEntry := by cbv
private theorem reserved_missing : reserved.nodeRecords blockedKey = none := by cbv
private theorem reserved_context : Context reserved [] := by
  have first : Context afterDepth [] := by
    simpa only [depth_done,Outcome.state] using
      initial_context.callback blockedBody .depth (depth_available (empty : Heap))
  have second : Context cut [] := by
    simpa only [ordinary_done,Outcome.state] using
      first.callback blockedBody (.uninterned (ordinaryLevel preparedDepth))
        (ordinary_available afterDepth (ordinaryLevel preparedDepth))
  exact second.reserve blockedKey
private theorem target_done : build targetSource [] reserved = .done target afterTarget := by cbv
private theorem blocked_pending : build blockedSource [] afterTarget = .pending blockedKey afterTarget := by cbv
private theorem whole_pending : build source [] reserved = .pending blockedKey afterTarget := by cbv
private theorem shape : target = .mu entry body depth ordinary := by cbv
private theorem distinct_keys : blockedKey ≠ targetKey := by
  cbv
  intro impossible
  cases impossible
private theorem initial_missing : reserved.nodeRecords targetKey = none := by cbv
private theorem final_present : afterTarget.nodeRecords targetKey = some (.mu entry body depth ordinary) := by cbv

private theorem rooted :
    ∃ event : Publication (Symbol := Nat) (Guard := Bool),
      Reached source [] (.binder event.smart event.expression) event.environment event.before ∧
      targetKey = event.key ∧ (.mu entry body depth ordinary : Node) = event.candidate ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path reserved event.before) ∧
      Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧
      Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after afterTarget ∧ Extends event.after.nodes.issued afterTarget.nodes.issued := by
  have selected : (build source [] reserved).state.nodeRecords targetKey =
      some (.mu entry body depth ordinary) := by
    simpa only [whole_pending,Outcome.state] using final_present
  rcases build_writer_or_prior source [] reserved reserved_context
      targetKey entry body depth ordinary selected with prior | written
  · rw [initial_missing] at prior
    cases prior
  · simpa only [SourceCurrentCompletedBuildRootedWriters.Written,whole_pending,Outcome.state] using written

private theorem checked_witness :
    Context (empty : Heap) [] ∧
    callback blockedBody [] .depth (empty : Heap) = .done preparedDepth afterDepth ∧
    callback blockedBody [] (.uninterned (ordinaryLevel preparedDepth)) afterDepth = .done preparedOrdinary cut ∧
    cut.nodes.table blockedKey = none ∧
    reserved = {cut with nodes := (Cache.intern cut.nodes blockedKey).2} ∧
    reserved.nodes.table blockedKey = some blockedEntry ∧
    reserved.nodeRecords blockedKey = none ∧ Context reserved [] ∧
    blockedKey ≠ targetKey ∧
    build targetSource [] reserved = .done target afterTarget ∧
    build blockedSource [] afterTarget = .pending blockedKey afterTarget ∧
    build source [] reserved = .pending blockedKey afterTarget ∧
    target = .mu entry body depth ordinary ∧
    reserved.nodeRecords targetKey = none ∧
    afterTarget.nodeRecords targetKey = some (.mu entry body depth ordinary) ∧
    ∃ event : Publication (Symbol := Nat) (Guard := Bool),
      Reached source [] (.binder event.smart event.expression) event.environment event.before ∧
      targetKey = event.key ∧ (.mu entry body depth ordinary : Node) = event.candidate ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path reserved event.before) ∧
      Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧
      Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after afterTarget ∧ Extends event.after.nodes.issued afterTarget.nodes.issued := by
  exact ⟨initial_context,depth_done,ordinary_done,cut_missing,rfl,reserved_table,
    reserved_missing,reserved_context,distinct_keys,target_done,blocked_pending,whole_pending,
    shape,initial_missing,final_present,rooted⟩

/-- A real reserved-key pending call retains a new full Mu and the same rooted writer receipt. -/
theorem actual_pending_writer :
    Context (empty : Heap) [] ∧
    callback blockedBody [] .depth (empty : Heap) = .done preparedDepth afterDepth ∧
    callback blockedBody [] (.uninterned (ordinaryLevel preparedDepth)) afterDepth = .done preparedOrdinary cut ∧
    cut.nodes.table blockedKey = none ∧
    reserved = {cut with nodes := (Cache.intern cut.nodes blockedKey).2} ∧
    reserved.nodes.table blockedKey = some blockedEntry ∧
    reserved.nodeRecords blockedKey = none ∧ Context reserved [] ∧
    blockedKey ≠ targetKey ∧
    build targetSource [] reserved = .done target afterTarget ∧
    build blockedSource [] afterTarget = .pending blockedKey afterTarget ∧
    build source [] reserved = .pending blockedKey afterTarget ∧
    target = .mu entry body depth ordinary ∧
    reserved.nodeRecords targetKey = none ∧
    afterTarget.nodeRecords targetKey = some (.mu entry body depth ordinary) ∧
    ∃ event : Publication (Symbol := Nat) (Guard := Bool),
      Reached source [] (.binder event.smart event.expression) event.environment event.before ∧
      targetKey = event.key ∧ (.mu entry body depth ordinary : Node) = event.candidate ∧
      event.afterBody.nodeRecords event.key = none ∧
      Nonempty (Path reserved event.before) ∧
      Nonempty (Path event.before event.afterDepth) ∧
      Nonempty (Path event.afterDepth event.cut) ∧
      Nonempty (Path event.allocated event.afterBody) ∧
      Grows event.after afterTarget ∧ Extends event.after.nodes.issued afterTarget.nodes.issued := checked_witness

end MicroCFTA.StoppingRootedWritersFixture

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.StoppingRootedWritersFixture.actual_pending_writer
#print MicroCFTA.StoppingRootedWritersFixture.actual_pending_writer
#print axioms MicroCFTA.StoppingRootedWritersFixture.actual_pending_writer
