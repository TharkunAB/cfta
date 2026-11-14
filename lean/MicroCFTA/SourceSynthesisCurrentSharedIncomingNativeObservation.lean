import MicroCFTA.SourcePruningEnumerationSharedIncomingNode
import MicroCFTA.SourceCurrentNativeOperationHeap
import MicroCFTA.SourceEqualityNativeDemandTrace

/-!
# Native observations from the actual shared incoming worker

The optimized visitor uses SharedIncomingNode.run.
Its completed native call precedes the actual shared Empty-check phase.
The phase retains its skipped or performed outcome and private snapshot.
All caller, fourth-memo, query, and core endpoints remain literal.
The older incoming worker is a separate operation.
-/
namespace MicroCFTA.SourceSynthesisCurrentSharedIncomingNativeObservation
open Cache EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourcePruningEnumerationObservation (PendingRealized)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceRecursiveIntersectionKernel (Extension)
open SourceRecursiveIntersectionCode (requestNode Code)
open SourceEqualityNativeDemand (Steps)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "top" => SourceEqualityConstraintConstructors.top

set_option autoImplicit false

private theorem native_done_first_step
    {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
    (fuel : Nat) (left right value : Node) (before after : Checked width)
    (actual : SourceEqualityNativeDemand.execute fuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after) :
    ∃ (next : Code Symbol Constraint Node)
        (first : SourceRecursiveIntersectionThunks.State width Symbol Constraint) (tailFuel : Nat),
      SourceRecursiveIntersectionNative.step top SourceEqualityPCSNativeEdge.conjoin
        (requestNode IntersectionEmptyDomain.emptyDomain left right) before.native =
          .yielded next first ∧
      Steps tailFuel (.code next) ⟨first, before.operations⟩ (.code (.pure value)) after := by
  obtain ⟨count, _below, trace⟩ := SourceEqualityNativeDemand.done_trace fuel
    (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before after value actual
  change Steps count (.code (.node
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)) before
    (.code (.pure value)) after at trace
  cases trace with
  | cons control state next reached final last tailFuel one rest =>
      have lifted : SourceEqualityNativeDemand.lift before.operations
          (SourceRecursiveIntersectionNative.step top SourceEqualityPCSNativeEdge.conjoin
            (requestNode IntersectionEmptyDomain.emptyDomain left right) before.native) =
          .yielded next reached := by
        simpa only [SourceEqualityNativeDemand.step, requestNode] using one
      cases observed : SourceRecursiveIntersectionNative.step top SourceEqualityPCSNativeEdge.conjoin
          (requestNode IntersectionEmptyDomain.emptyDomain left right) before.native with
      | yielded code native =>
          rw [observed] at lifted
          obtain ⟨rfl, rfl⟩ := SourceEqualityNativeDemand.Outcome.yielded.inj lifted
          exact ⟨code, native, tailFuel, rfl, rest⟩
      | done result native =>
          simp only [observed, SourceEqualityNativeDemand.lift] at lifted
          cases lifted
      | failed failure native =>
          simp only [observed, SourceEqualityNativeDemand.lift] at lifted
          cases lifted
      | blocked reason code native =>
          simp only [observed, SourceEqualityNativeDemand.lift] at lifted
          cases lifted

/-- A successful actual shared incoming merge derives its native call and exact shared phase. -/
theorem shared_incoming_success_native_or_unchanged
    {width : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Core)
    (checkEmpty : Bool) (representativeFuel nativeFuel p h target : Nat)
    (incoming : Node) (incomingScs : List Suspended) (memos : Memos) (queries : Queries)
    (initial : Context formulas solver inventory caller memos)
    (realized : PendingRealized caller.checked.native.machine.heap before)
    (available : Available caller.checked.native.machine.heap incoming)
    (raw : List (Except EnumerationState.Error (Unit × Core)))
    (afterCaller : Caller width) (savedQueries : Queries) (read : Core)
    (actual : SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel nativeFuel p h
      caller before target incoming incomingScs queries =
        (.ok (some raw), afterCaller, savedQueries, read)) :
    afterCaller = caller ∨
      ∃ (found : UnionFind.Result) (oldHandle : Nat) (oldScs : List Suspended)
          (old query : Node) (queried : Checked width)
          (phase : SourcePruningEnumerationSharedEnabledEmpty.Outcome width)
          (phaseQueries : Queries) (answer : Bool) (handle : Nat),
        UnionFind.findRoot representativeFuel before.representatives target = some found ∧
        before.values[found.representative]? = some (.unenumerated (some oldHandle) oldScs) ∧
        lookupNode caller.checked.native.machine.heap oldHandle = some old ∧
        Available caller.checked.native.machine.heap old ∧ old.free = [] ∧
        SourceEqualityNativeDemand.execute nativeFuel
          (.code (requestNode IntersectionEmptyDomain.emptyDomain incoming old)) caller.checked =
            .done query queried ∧
        (if checkEmpty then SourcePruningEnumerationSharedEnabledEmpty.check p h query queried caller.fourth queries
          else (.skipped queried caller.fourth, queries)) = (phase, phaseQueries) ∧
        phase.completed = some answer ∧
        encodeNode (if answer then .empty else query) = some handle ∧
        afterCaller = SourceCurrentAllocatedPartialState.advance caller phase.state phase.memo caller.merge ∧
        afterCaller.checked = phase.state ∧ afterCaller.fourth = phase.memo ∧ afterCaller.merge = caller.merge ∧
        savedQueries = phaseQueries ∧ read = {before with representatives := found.forest} ∧
        raw = ExceptT.run (SourcePruningEnumerationIncomingNode.finish found.representative handle
          incomingScs oldScs (if answer then .empty else query)
          ({before with representatives := found.forest} : Core)) ∧
        SourceCurrentNativeOperationHeap.Good queried ∧
        Extension caller.checked.native.machine queried.native.machine ∧
        SourceEqualityRequiredCache.Keeps caller.checked.native.machine.heap queried.native.machine.heap ∧
        Grows inventory.source queried.native.machine.heap ∧
        Extends inventory.source.nodes.issued queried.native.machine.heap.nodes.issued ∧
        Available queried.native.machine.heap query ∧
        ∃ (next : Code Symbol Constraint Node)
            (first : SourceRecursiveIntersectionThunks.State width Symbol Constraint) (tailFuel : Nat),
          SourceRecursiveIntersectionNative.step top SourceEqualityPCSNativeEdge.conjoin
            (requestNode IntersectionEmptyDomain.emptyDomain incoming old) caller.checked.native =
              .yielded next first ∧
          Steps tailFuel (.code next) ⟨first, caller.checked.operations⟩ (.code (.pure query)) queried := by
  have unchanged (same :
      (SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel nativeFuel p h
        caller before target incoming incomingScs queries).2.1 = caller) : afterCaller = caller := by
    exact (congrArg (fun result => result.2.1) actual).symm.trans same
  have good : SourceCurrentNativeOperationHeap.Good caller.checked :=
    SourceCurrentNativeOperationHeap.Good.of_native
      (SourceCurrentNativeOperationInvariants.Good.of_checked initial.ready.good)
      initial.ready.semantic initial.ready.costs
  cases reading : UnionFind.findRoot representativeFuel before.representatives target with
  | none =>
      exact Or.inl (unchanged (by simp only [SourcePruningEnumerationSharedIncomingNode.run, reading]))
  | some found =>
      cases slot : before.values[found.representative]? with
      | none =>
          exact Or.inl (unchanged (by simp only [SourcePruningEnumerationSharedIncomingNode.run, reading, slot]))
      | some stored =>
          cases stored with
          | enumerated fragment =>
              exact Or.inl (unchanged (by simp only [SourcePruningEnumerationSharedIncomingNode.run, reading, slot]))
          | eliminated =>
              exact Or.inl (unchanged (by simp only [SourcePruningEnumerationSharedIncomingNode.run, reading, slot]))
          | unenumerated oldNode oldScs =>
              cases oldNode with
              | none =>
                  cases encoded : encodeNode incoming <;>
                    exact Or.inl (unchanged (by
                      simp only [SourcePruningEnumerationSharedIncomingNode.run, reading, slot, encoded]))
              | some oldHandle =>
                  obtain ⟨old, decoded, oldAvailable, oldClosed⟩ :=
                    realized found.representative oldHandle oldScs slot
                  cases completed : SourceEqualityNativeDemand.execute nativeFuel
                      (.code (requestNode IntersectionEmptyDomain.emptyDomain incoming old)) caller.checked with
                  | done query queried =>
                      have ready : SourceRecursiveIntersectionThunks.NodeReady caller.checked.native.machine
                          ⟨IntersectionEmptyDomain.emptyDomain, incoming, old⟩ :=
                        ⟨SourceRecursiveIntersectionKernel.empty_domain caller.checked.native.machine,
                          available, oldAvailable⟩
                      obtain ⟨final, extension, keeps, _operations, known⟩ :=
                        SourceCurrentNativeOperationHeap.node nativeFuel
                          ⟨IntersectionEmptyDomain.emptyDomain, incoming, old⟩ caller.checked queried query
                          good ready completed
                      have first := native_done_first_step nativeFuel incoming old query caller.checked queried completed
                      rcases phaseObserved :
                          (if checkEmpty then
                            SourcePruningEnumerationSharedEnabledEmpty.check p h query queried caller.fourth queries
                          else (.skipped queried caller.fourth, queries)) with
                        ⟨phase, phaseQueries⟩
                      have entered := actual
                      simp only [SourcePruningEnumerationSharedIncomingNode.run, reading, slot, decoded,
                        completed, phaseObserved] at entered
                      cases accepted : phase.completed with
                      | none =>
                          simp only [accepted] at entered
                          cases entered
                      | some answer =>
                          simp only [accepted] at entered
                          cases encoded : encodeNode (if answer then .empty else query) with
                          | none =>
                              simp only [encoded] at entered
                              cases entered
                          | some handle =>
                              simp only [encoded] at entered
                              have callerSame : afterCaller = SourceCurrentAllocatedPartialState.advance
                                  caller phase.state phase.memo caller.merge :=
                                (congrArg (fun result => result.2.1) entered).symm
                              have checkedSame : afterCaller.checked = phase.state := by rw [callerSame]; rfl
                              have fourthSame : afterCaller.fourth = phase.memo := by rw [callerSame]; rfl
                              have mergeSame : afterCaller.merge = caller.merge := by rw [callerSame]; rfl
                              have queriesSame : savedQueries = phaseQueries :=
                                (congrArg (fun result => result.2.2.1) entered).symm
                              have readSame : read = {before with representatives := found.forest} :=
                                (congrArg (fun result => result.2.2.2) entered).symm
                              have rawSame : raw = ExceptT.run
                                  (SourcePruningEnumerationIncomingNode.finish found.representative handle
                                    incomingScs oldScs (if answer then .empty else query)
                                    ({before with representatives := found.forest} : Core)) :=
                                (Option.some.inj (Except.ok.inj (congrArg Prod.fst entered))).symm
                              exact Or.inr ⟨found, oldHandle, oldScs, old, query, queried,
                                phase, phaseQueries, answer, handle, rfl, slot, decoded, oldAvailable, oldClosed,
                                completed, phaseObserved, accepted, encoded, callerSame, checkedSame, fourthSame,
                                mergeSame, queriesSame, readSame, rawSame, final, extension, keeps,
                                grows_trans initial.admitted.growth keeps.growth,
                                extends_trans initial.admitted.history keeps.history, known, first⟩
                  | yielded control current =>
                      have observed := congrArg Prod.fst actual
                      simp only [SourcePruningEnumerationSharedIncomingNode.run, reading, slot, decoded, completed] at observed
                      cases observed
                  | failed failure current =>
                      have observed := congrArg Prod.fst actual
                      simp only [SourcePruningEnumerationSharedIncomingNode.run, reading, slot, decoded, completed] at observed
                      cases observed
                  | constraintError message current =>
                      have observed := congrArg Prod.fst actual
                      simp only [SourcePruningEnumerationSharedIncomingNode.run, reading, slot, decoded, completed] at observed
                      cases observed
                  | blocked reason control current =>
                      have observed := congrArg Prod.fst actual
                      simp only [SourcePruningEnumerationSharedIncomingNode.run, reading, slot, decoded, completed] at observed
                      cases observed

end MicroCFTA.SourceSynthesisCurrentSharedIncomingNativeObservation

