import MicroCFTA.SourceSynthesisCurrentSharedIncomingNativeObservation
import MicroCFTA.SourcePruningEnumerationRecursiveResources
import MicroCFTA.SourcePruningEnumerationOwnInputShape

namespace MicroCFTA.SourcePruningEnumerationSharedIncomingQueryHistory
open Cache EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet QueryHistory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Child" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
variable {Typing : Type} {bits : Nat}
set_option autoImplicit false

theorem prepared_incoming_success_query_history
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (parentEntry : Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry rows depth free))
    (parentClosed : free = []) (edge : EdgeValue Symbol Constraint) (rowSelected : edge ∈ rows)
    (preparationHeap : InternedConstructorTemplates.State Symbol Constraint)
    (parentBucket : List Suspended) (captured own : Cached)
    (symbol : Symbol) (staged : List Child) (residual : Option Constraint)
    (prepared : SourcePruningEnumerationCachedOwn.prepare preparationHeap parentBucket edge captured =
      some [((symbol, staged, residual), own)])
    (position : Nat) (incoming : Node) (bucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (selected : staged[position]? = some (incoming, bucket, action))
    (checkEmpty : Bool) (representativeFuel nativeFuel p h target : Nat)
    (incomingScs : List Suspended)
    (raw : List (Except EnumerationState.Error (Unit × Core)))
    (afterCaller : Caller (bits + 2)) (savedQueries : Queries) (read : Core)
    (actual : SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel nativeFuel p h
      caller before.core target incoming incomingScs memos.query =
        (.ok (some raw), afterCaller, savedQueries, read)) :
    Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      ((afterCaller = caller ∧ QueryHistory 0 caller afterCaller) ∨
        ∃ (found : UnionFind.Result) (oldHandle : Nat) (oldScs : List Suspended)
          (old query : Node) (queried : Checked (bits + 2))
          (phase : SourcePruningEnumerationSharedEnabledEmpty.Outcome (bits + 2))
          (phaseQueries : Queries) (answer : Bool),
          UnionFind.findRoot representativeFuel before.core.representatives target = some found ∧
          before.core.values[found.representative]? = some (.unenumerated (some oldHandle) oldScs) ∧
          lookupNode caller.checked.native.machine.heap oldHandle = some old ∧
          Available caller.checked.native.machine.heap old ∧ old.free = [] ∧
          SourceEqualityNativeDemand.execute nativeFuel
            (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
            caller.checked = .done query queried ∧
          QueryHistory 1 caller
            (SourceCurrentAllocatedPartialState.advance caller queried caller.fourth caller.merge) ∧
          (if checkEmpty then SourcePruningEnumerationSharedEnabledEmpty.check p h query queried caller.fourth memos.query
            else (.skipped queried caller.fourth, memos.query)) = (phase, phaseQueries) ∧
          phase.completed = some answer ∧
          afterCaller = SourceCurrentAllocatedPartialState.advance caller phase.state phase.memo caller.merge ∧
          savedQueries = phaseQueries ∧ read = {before.core with representatives := found.forest} ∧
          (phase = .skipped queried caller.fourth → QueryHistory 1 caller afterCaller) ∧
          (checkEmpty = false → QueryHistory 1 caller afterCaller ∧ savedQueries = memos.query)) := by
  have actualChild : edge.children[position]? = some incoming := by
    have allowed : arityAllows edge.children.length parentBucket = true := by
      by_cases accepted : arityAllows edge.children.length parentBucket = true
      · exact accepted
      · simp [SourcePruningEnumerationCachedOwn.prepare, accepted] at prepared
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        simp [SourcePruningEnumerationCachedOwn.prepare, allowed, projected] at prepared
    | some pair =>
        obtain ⟨tries, projectedResidual⟩ := pair
        have inputShape := SourcePruningEnumerationCachedOwn.prepare_inputs
          preparationHeap parentBucket edge captured own tries projectedResidual
          (symbol, staged, residual) projected prepared
        have stagedSame : staged =
            (SourcePruningEnumerationEdgeInputs.children edge parentBucket captured.core.counter tries).map
              (fun input => (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild
                (EnumGuard := Constraint) input.2 input.1)) :=
          congrArg (fun result => result.2.1) inputShape
        have indexedSelection := selected
        rw [stagedSame, SourcePruningEnumerationEdgeInputs.children,
          List.map_map, List.getElem?_map] at indexedSelection
        obtain ⟨indexed, indexedStored, selectedSame⟩ := Option.map_eq_some_iff.mp indexedSelection
        rw [List.getElem?_zipIdx] at indexedStored
        obtain ⟨child, childStored, rfl⟩ := Option.map_eq_some_iff.mp indexedStored
        have childSame : child = incoming := congrArg Prod.fst selectedSame
        rw [← childSame]
        exact childStored
  have childMember : incoming ∈ edge.children := List.mem_of_getElem? actualChild
  have incomingAvailable : Available caller.checked.native.machine.heap incoming :=
    parentAvailable.children incoming (List.mem_flatMap.mpr ⟨edge, rowSelected, childMember⟩)
  have incomingClosed : incoming.free = [] :=
    MergedColdReaderClosed.node_children_closed caller.checked.native.machine.heap
      packet.context.ready.good.native.machine.1 parentEntry rows depth free
      parentAvailable parentClosed edge rowSelected incoming childMember
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  have observation :=
    SourceSynthesisCurrentSharedIncomingNativeObservation.shared_incoming_success_native_or_unchanged
      formulas solver inventory caller before.core checkEmpty representativeFuel nativeFuel p h target
      incoming incomingScs memos memos.query packet.context realized incomingAvailable
      raw afterCaller savedQueries read actual
  refine ⟨incomingAvailable, incomingClosed, ?_⟩
  rcases observation with same | native
  · refine .inl ⟨same, ?_⟩
    rw [same]
    exact .nil caller
  · obtain ⟨found, oldHandle, oldScs, old, query, queried, phase, phaseQueries, answer, _handle,
      foundEq, storedEq, oldLookup, oldAvailable, oldClosed, nativeDone, phaseEq, completed,
      _encoded, callerSame, _checkedSame, _fourthSame, _mergeSame, savedEq, readEq, _rest⟩ := native
    have history : QueryHistory 1 caller
        (SourceCurrentAllocatedPartialState.advance caller queried caller.fourth caller.merge) :=
      .cons incomingAvailable oldAvailable incomingClosed oldClosed nativeDone (.nil _)
    refine .inr ⟨found, oldHandle, oldScs, old, query, queried, phase, phaseQueries, answer,
      foundEq, storedEq, oldLookup, oldAvailable, oldClosed, nativeDone, history,
      phaseEq, completed, callerSame, savedEq, readEq, ?_, ?_⟩
    · intro skipped
      rw [callerSame, skipped]
      exact history
    · intro disabled
      have bypass :
          (SourcePruningEnumerationSharedEnabledEmpty.Outcome.skipped queried caller.fourth, memos.query) =
            (phase, phaseQueries) := by
        simpa only [disabled, Bool.false_eq_true, ite_false] using phaseEq
      have phaseSame : phase = .skipped queried caller.fourth :=
        (congrArg Prod.fst bypass).symm
      constructor
      · rw [callerSame, phaseSame]
        exact history
      · exact savedEq.trans (congrArg Prod.snd bypass).symm

end MicroCFTA.SourcePruningEnumerationSharedIncomingQueryHistory

#check MicroCFTA.SourcePruningEnumerationSharedIncomingQueryHistory.prepared_incoming_success_query_history
#print axioms MicroCFTA.SourcePruningEnumerationSharedIncomingQueryHistory.prepared_incoming_success_query_history
