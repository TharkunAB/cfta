import MicroCFTA.SourceCurrentIncomingSomeCounter

/-! Actual optional cache returns carry the original active and target histories. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingHistory
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationNativeBranchCompletion (CacheValid)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos

private theorem read_history {width : Nat} (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (scs : List Suspended) (memos : Memos) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs memos.query
    actual.2.2.2.expansionAncestry = before.expansionAncestry ∧
      actual.2.2.2.recursionAncestry = before.recursionAncestry := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  cases rootRead : UnionFind.findRoot r before.representatives target with
  | none =>
      simpa only [SourcePruningEnumerationIncomingNode.run, rootRead] using
        (show before.expansionAncestry = before.expansionAncestry ∧
          before.recursionAncestry = before.recursionAncestry from ⟨rfl, rfl⟩)
  | some found =>
      have readFacts : ({before with representatives := found.forest} : Core).expansionAncestry =
          before.expansionAncestry ∧
          ({before with representatives := found.forest} : Core).recursionAncestry = before.recursionAncestry :=
        ⟨rfl, rfl⟩
      simp only [SourcePruningEnumerationIncomingNode.run, rootRead]
      repeat' first | exact readFacts | split

variable {bits : Nat}

/-- Every actual Some cache inherits the original active keys and original target history. -/
theorem some_cache_histories (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (before after : Cached) (memos : Memos)
    (checkEmpty : Bool) (r n p h k target : Nat) (incoming : Node) (scs : List Suspended)
    (rooted : IsRoot before.core.representatives target)
    (incomingBound : ∀ sc ∈ scs, sc.var < before.core.counter) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query
    Context formulas solver inventory caller memos → CacheValid caller before →
    Available caller.checked.native.machine.heap incoming → incoming.free = [] →
    Fits profile caller.checked → Room bits profile → actual.2 = some after →
      after.core.recursionAncestry = (fun other => if other = target then
        (before.core.expansionAncestry ++ before.core.recursionAncestry target).eraseDups
        else before.core.recursionAncestry other) ∧
      ∀ key, key ∈ before.core.expansionAncestry ∨ key ∈ before.core.recursionAncestry target →
        key ∈ after.core.recursionAncestry target := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  intro initial valid available closed fits room cacheSome
  have validBefore := valid
  obtain ⟨_roots, _paths, storage, _realized, _counts, _flags⟩ := valid
  obtain ⟨oldNode, oldScs, stored⟩ := SourceCurrentIncomingSomeAdmission.some_stored symbolEquality
    edgeEquality nodeEquality checkEmpty r n p h k target caller before after incoming scs memos.query
    rooted cacheSome
  obtain ⟨inside, bounded⟩ := SourceCurrentIncomingSomeAdmission.stored_admissions before.core
    target oldNode scs oldScs storage stored incomingBound
  have rows := SourceCurrentIncomingSomeAdmission.some_rows symbolEquality edgeEquality nodeEquality
    checkEmpty r n p h k target caller before after incoming scs memos.query cacheSome
  have readHistory := read_history symbolEquality edgeEquality nodeEquality checkEmpty r n p h
    caller before.core target incoming scs memos
  have readFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before.core target incoming scs memos _roots _paths
  dsimp only at readHistory readFacts
  generalize actualRun : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
    caller before target incoming scs memos.query = actual at cacheSome rows ⊢
  rcases actual with ⟨⟨result, reached, savedQueries, read⟩, returnedCache⟩
  dsimp only at cacheSome rows ⊢
  have callSame : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
      caller before target incoming scs memos.query = ((result, reached, savedQueries, read), some after) := by
    rw [actualRun, cacheSome]
  have incomingSame : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before.core target incoming scs memos.query = (result, reached, savedQueries, read) := by
    simpa only [SourcePruningEnumerationIncomingCacheAdapter.run] using congrArg Prod.fst callSame
  rw [incomingSame] at readHistory readFacts
  dsimp only at readHistory readFacts
  have historyFromRead : after.core.recursionAncestry = (fun other => if other = target then
      (read.expansionAncestry ++ read.recursionAncestry target).eraseDups else read.recursionAncestry other) := by
    rcases rows with emptyRows | ⟨returned, singletonRows⟩
    · have observed : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
          caller before target incoming scs memos.query =
            ((.ok (some []), reached, savedQueries, read), some after) := by
        simpa only [emptyRows] using callSame
      have incomingEmpty : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
          caller before.core target incoming scs memos.query = (.ok (some []), reached, savedQueries, read) := by
        simpa only [SourcePruningEnumerationIncomingCacheAdapter.run] using congrArg Prod.fst observed
      have storedRead : read.values[target]? = some (.unenumerated oldNode oldScs) := by
        rw [readFacts.2.1]
        exact stored
      have adapted : SourcePruningEnumerationIncomingCacheAdapter.adapt reached.checked.native.machine.heap
          k target scs before read [] = some after := by
        simpa only [SourcePruningEnumerationIncomingCacheAdapter.run, incomingEmpty] using congrArg Prod.snd observed
      let value : UVarValue Symbol := .unenumerated (some 0) (scs ++ oldScs)
      let produced : Core := {read with
        values := read.values.set target value
        recursionAncestry := fun other => if other = target then
          (read.expansionAncestry ++ read.recursionAncestry target).eraseDups else read.recursionAncestry other}
      have mapped : (SourcePruningEnumerationNativeIndex.write reached.checked.native.machine.heap k target value scs []
          (EnumerationExpandableIndex.frame read before)).map (EnumerationExpandableIndex.frame produced) = some after := by
        simpa only [SourcePruningEnumerationIncomingCacheAdapter.adapt, storedRead, produced, value] using adapted
      obtain ⟨written, _writeObserved, afterSame⟩ := Option.map_eq_some_iff.mp mapped
      have coreSame : after.core = produced := by
        rw [← afterSame]
        rfl
      rw [coreSame]
    · have observed : SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k
          caller before target incoming scs memos.query =
            ((.ok (some [.ok ((), returned)]), reached, savedQueries, read), some after) := by
        simpa only [singletonRows] using callSame
      have rawObserved : (SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
          caller before.core target incoming scs memos.query).1 = .ok (some [.ok ((), returned)]) := by
        rw [incomingSame]
        exact singletonRows
      have effects := SourceCurrentIncomingSingletonCore.singleton_core_effects symbolEquality edgeEquality
        nodeEquality profile formulas solver inventory caller before memos checkEmpty r n p h target incoming
        scs oldScs oldNode rooted stored inside bounded initial validBefore available closed fits room returned rawObserved
      dsimp only at effects
      rw [incomingSame] at effects
      dsimp only at effects
      obtain ⟨_handle, returnedSame, _representatives, _counter, _slot, _references, _storage, _realized⟩ := effects
      have coreSame := SourcePruningEnumerationIncomingCacheAdapter.singleton_core checkEmpty r n p h k
        caller reached before after target incoming scs memos.query savedQueries read returned observed
      rw [coreSame, returnedSame]
  have originalHistory : after.core.recursionAncestry = (fun other => if other = target then
      (before.core.expansionAncestry ++ before.core.recursionAncestry target).eraseDups
      else before.core.recursionAncestry other) := by
    rw [historyFromRead, readHistory.1, readHistory.2]
  refine ⟨originalHistory, ?_⟩
  intro key member
  simpa [originalHistory] using member

end MicroCFTA.SourceCurrentIncomingHistory
