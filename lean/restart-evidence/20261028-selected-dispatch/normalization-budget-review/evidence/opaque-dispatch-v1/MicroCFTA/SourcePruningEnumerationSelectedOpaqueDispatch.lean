import MicroCFTA.SourcePruningEnumerationChildCompletion
import MicroCFTA.SourcePruningEnumerationCachedPrepareProper
import MicroCFTA.SourcePruningEnumerationOwnFinalizeProper
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.EnumerationStratifiedTransport

/-!
# The selected opaque and terminal branches after one native preparation

The input value is already prepared. This worker does not enter or unfold it.
Ordinary nonterminal nodes belong to the separate selected-edge dispatcher.
Opaque values use the actual child allocation with an empty stored bucket.
Terminal inputs retain the actual incoming observation and reached caller.
Successful finalization writes the original captured target.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open EnumerationProgress
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Result" => SourcePruningEnumerationSelectedEdge.Result
variable {Typing : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Dispatch an already prepared value and retain every reached child observation. -/
noncomputable def run (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (value : Node) (caller : Caller width) (before : Cached)
    (queries : SourceEndpointMemo.Memos) : Option (Result width) :=
  if value = .empty then some (.rejected caller queries before)
  else if (match value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) then none
  else
    match SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs value caller before queries with
    | ((.ok (some [.ok (fragment, _returned)]), reached, saved, _outer, _waiting), some after) =>
        (SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after).map
          (fun finished => .complete fragment reached saved finished)
    | (observation, candidate) => some (.stopped [] observation candidate)

/-- The selected ordinary nonterminal route never uses a fresh child slot here. -/
theorem ordinary_deferred (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (caller : Caller width) (before : Cached) (queries : SourceEndpointMemo.Memos)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    run checkEmpty r n p h k target scs (.node entry edges depth free) caller before queries = none := by
  simp only [run, reduceCtorEq, ↓reduceIte, nonterminal, Bool.not_false]

/-- Terminal dispatch keeps the actual winner, raw result, caller and cache candidate. -/
theorem terminal_step (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (value : Node) (caller : Caller width) (before : Cached)
    (queries : SourceEndpointMemo.Memos) (nonempty : value ≠ .empty)
    (terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true) :
    run checkEmpty r n p h k target scs value caller before queries =
      match SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k scs value caller before queries with
      | ((.ok (some [.ok (fragment, _returned)]), reached, saved, _outer, _waiting), some after) =>
          (SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after).map
            (fun finished => .complete fragment reached saved finished)
      | (observation, candidate) => some (.stopped [] observation candidate) := by
  have gate : (match value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false := by
    cases value <;> simp only [terminal, Bool.not_true]
  simp only [run, ite_eq_right nonempty, gate, Bool.false_eq_true, ↓reduceIte]

/-- Original selected storage derives the complete opaque allocation and captured write. -/
theorem opaque_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (target originalHandle : Nat) (scs : List Suspended)
    (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some originalHandle) scs))
    (proper : ProperState before.core)
    (incoming : EnumerationReferences.IncomingAvoid target before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    ∃ (bound childHandle : Nat) (middle after : Cached),
      encodeNode value = some childHandle ∧
      lookupNode caller.checked.native.machine.heap childHandle = some value ∧
      middle.core = allocated (some childHandle) before.core ∧
      middle.core.values[before.core.counter]? = some (.unenumerated (some childHandle) []) ∧
      middle.expandable = before.expandable ∧ middle.waiting = before.waiting ∧
      (∀ r n p h extra,
        SourcePruningEnumerationChildDispatch.run checkEmpty r n p h (bound + extra)
          scs value caller before memos.query =
          ((.ok (some [.ok (.hole before.core.counter, middle.core)]), caller, memos.query,
            before.core, before.waiting), some middle)) ∧
      (∀ r n p h extra, run checkEmpty r n p h (bound + extra) target scs value caller before memos.query =
        some (.complete (.hole before.core.counter) caller memos.query after)) ∧
      after.core.counter = before.core.counter + 1 ∧
      after.core.values[target]? = some (.enumerated (.hole before.core.counter)) ∧
      after.core.values[before.core.counter]? = some (.unenumerated (some childHandle) []) ∧
      after.core.expansionAncestry = [] ∧
      Packet formulas solver inventory caller memos metadata after ∧ ProperState after.core ∧
      Post formulas solver inventory caller caller memos := by
  have payload : ProperValue (.unenumerated (some originalHandle) scs : UVarValue Symbol) :=
    proper _ (List.mem_of_getElem? stored)
  have nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false :=
    List.any_eq_false.mpr (fun sc member => (payload sc member).2.2)
  have nonempty : value ≠ .empty := by
    intro same
    subst value
    cases boundary
  have gate : (match value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false := by
    cases value <;> cases boundary <;> rfl
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have avoids := ready.avoids originalHandle scs stored
  have inputsPending := EnumerationReferences.pending_inputs before.core packet.pending
    target (some originalHandle) scs stored
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨childHandle, action, middle, encoded, decoded, prepared, cachedRun, raw, middleCore,
    freshStored, growth, _aligned, forest, middlePaths, middleStorage, middleRealized,
    middleCounts, waitingSame, flagSame, middleFlags, holeBound⟩ :=
    SourcePruningEnumerationCachedPrepare.boundary_complete caller.checked.native.machine.heap before
      value scs roots packet.context.ready.semantic.ready.semantic.1.normal.facts.coherent available closed
      boundary nonterminal storage realized paths counts flags
  have success : Success action before.core (.hole before.core.counter) middle.core := by
    rw [Success, raw]
    simp
  obtain ⟨middleSafe, origin, protects⟩ := SourcePruningEnumerationChildEffects.child
    scs value action before.core middle.core _ packet.safe bounded prepared success
  have frame := protects target ready.inside ready.root
  have currentStored : middle.core.values[target]? = some (.unenumerated (some originalHandle) scs) :=
    frame.value.trans stored
  have referenceEffects : ∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
      EnumerationReferences.InputsAllowed allowed scs →
      EnumerationReferences.ReferencesAllowed allowed middle.core := by
    intro allowed valid inputs
    exact SourcePruningEnumerationNativeReferences.prepared_allowed allowed scs value action
      before.core middle.core _ valid inputs prepared success
  have enumProtects : ∀ held fragment, before.core.values[held]? = some (.enumerated fragment) →
      EnumerationDriver.Protected held before.core middle.core := by
    intro held fragment old
    obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held fragment old
    exact protects held inside root
  have middlePending := SourcePruningEnumerationNativeReferences.pending_preserved before.core middle.core scs
    packet.pending inputsPending origin enumProtects referenceEffects
  have middleIncoming := SourcePruningEnumerationNativeReferences.incoming_preserved before.core middle.core
    target scs incoming avoids frame.classes referenceEffects
  have freshPath : UnionFind.Reaches middle.core.representatives before.core.counter before.core.counter 1 := by
    rw [forest]
    exact .root (by simp [UnionFind.read, outside_forest before.core.representatives
      before.core.counter before.core.counter packet.safe.1.forest (Nat.le_refl _)])
  have pendingHole := pendingFragment_hole middle.core before.core.counter before.core.counter 1
    (some childHandle) [] freshPath freshStored
  have separate : FragmentAvoid middle.core.representatives target (.hole before.core.counter : Fragments.Fragment Symbol) := by
    intro held hole same
    cases hole
    rw [forest] at same
    have equal := outside_class before.core.representatives before.core.counter before.core.counter target
      packet.safe.1.forest (Nat.le_refl _) (UnionFind.sameClass_symm same)
    omega
  obtain ⟨bound, after, finalRun, _finalRaw, finalCore, finalStored, _finalFlag, _finalWaiting,
    afterPaths, afterCounts, afterFlags, afterStorage, afterRealized, safeFinish⟩ :=
    SourcePruningEnumerationFinalize.complete caller.checked.native.machine.heap middle target
      (.hole before.core.counter) (.unenumerated (some originalHandle) scs) currentStored
      roots middlePaths middleCounts middleFlags middleStorage holeBound middleRealized
  have afterSafe := safeFinish middleSafe frame.root
  have afterPending : EnumerationReferences.PendingReferences after.core := by
    have written := EnumerationReferences.setValue_pending target (.hole before.core.counter) middle.core
      {middle.core with values := middle.core.values.set target (.enumerated (.hole before.core.counter))}
      middlePending middleIncoming ((EnumerationDriver.modify_success _ _ _).mpr rfl)
    rw [finalCore]
    exact written
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  obtain ⟨middleLevel, middleOrder⟩ := EnumerationOrder.stratified_preserved before.core middle.core
    middleSafe level frontier ordered origin enumProtects
  obtain ⟨afterLevel, afterOrder⟩ := EnumerationOrder.write_stratified middle.core middleSafe middleLevel
    frontier target middleOrder (some originalHandle) scs currentStored (.hole before.core.counter)
    pendingHole separate
  have afterOrdered : EnumerationOrder.Stratified after.core afterLevel (frontier + 1) := by
    rw [finalCore]
    exact EnumerationOrder.stratified_ancestry _ [] afterLevel (frontier + 1) afterOrder
  have counter : after.core.counter = before.core.counter + 1 := by
    rw [finalCore]
    exact growth
  have afterPacket : Packet formulas solver inventory caller memos metadata after := by
    refine ⟨packet.context, afterSafe, afterPending,
      ⟨roots, afterPaths, afterStorage, afterRealized, afterCounts, afterFlags⟩,
      ⟨afterLevel, frontier + 1, afterOrdered⟩, ?_⟩
    intro group member entry listed
    exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) (by rw [counter]; omega)
  have middleProper : ProperState middle.core := by
    rw [middleCore]
    exact allocation_proper (some childHandle) before.core proper
  have afterProper := SourcePruningEnumerationFinalize.written_proper middle.core after.core target
    (.hole before.core.counter) middleProper finalCore
  have noHere : (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
    simp only [List.partition_eq_filter_filter]
    exact List.filter_eq_nil_iff.mpr (fun sc member => List.any_eq_false.mp nonterminal sc member)
  have childRun : ∀ r n p h fuel,
      SourcePruningEnumerationChildDispatch.run checkEmpty r n p h fuel scs value caller before memos.query =
        ((.ok (some [.ok (.hole before.core.counter, middle.core)]), caller, memos.query,
          before.core, before.waiting), some middle) := by
    intro r n p h fuel
    cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
        have hereSame : here = [] := by simpa only [partitioned] using noHere
        subst here
        simp only [SourcePruningEnumerationChildDispatch.run, SourcePruningEnumerationChildDispatch.observe,
          ite_eq_right nonempty, partitioned, prepared, cachedRun fuel, raw]
  refine ⟨bound, childHandle, middle, after, encoded, decoded, middleCore, freshStored,
    flagSame, waitingSame, ?_, ?_, counter, finalStored, ?_, ?_, afterPacket, afterProper,
    Post.refl packet.context⟩
  · intro r n p h extra
    exact childRun r n p h (bound + extra)
  · intro r n p h extra
    simp only [run, ite_eq_right nonempty, gate, Bool.false_eq_true, ↓reduceIte,
      childRun r n p h (bound + extra), finalRun extra, Option.map_some]
  · rw [finalCore, List.getElem?_set_ne (Nat.ne_of_lt ready.inside)]
    exact freshStored
  · rw [finalCore]

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
