import MicroCFTA.SourceCurrentIncomingSomePending
import MicroCFTA.SourcePruningEnumerationRecursivePacket

/-! Actual optional cache returns preserve the original allocation counter and pending-group bounds. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingSomeCounter
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
variable {bits : Nat}

/-- Original admissions derive counter equality for every actual Some cache. -/
theorem some_cache_counter (symbolEquality : DecidableEq Symbol)
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
    Fits profile caller.checked → Room bits profile →
    actual.2 = some after → after.core.counter = before.core.counter := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  intro initial valid available closed fits room cacheSome
  have validBefore := valid
  obtain ⟨roots, paths, storage, _realized, _counts, _flags⟩ := valid
  obtain ⟨oldNode, oldScs, stored⟩ := SourceCurrentIncomingSomeAdmission.some_stored symbolEquality
    edgeEquality nodeEquality checkEmpty r n p h k target caller before after incoming scs memos.query
    rooted cacheSome
  obtain ⟨inside, bounded⟩ := SourceCurrentIncomingSomeAdmission.stored_admissions before.core
    target oldNode scs oldScs storage stored incomingBound
  have rows := SourceCurrentIncomingSomeAdmission.some_rows symbolEquality edgeEquality nodeEquality
    checkEmpty r n p h k target caller before after incoming scs memos.query cacheSome
  have readFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
    nodeEquality checkEmpty r n p h caller before.core target incoming scs memos roots paths
  dsimp only at readFacts
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
  rw [incomingSame] at readFacts
  dsimp only at readFacts
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
    change read.counter = before.core.counter
    exact readFacts.2.2
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
    obtain ⟨_handle, _returnedSame, _representatives, counterSame, _slot, _references, _storage, _realized⟩ := effects
    have coreSame := SourcePruningEnumerationIncomingCacheAdapter.singleton_core checkEmpty r n p h k
      caller reached before after target incoming scs memos.query savedQueries read returned observed
    rw [coreSame]
    exact counterSame

variable {Typing : Type}

/-- The original current-cache Packet supplies bounds for the same pending groups after the call. -/
theorem some_packet_bounds (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (before after : Cached) (memos : Memos)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (checkEmpty : Bool) (r n p h k target : Nat) (incoming : Node) (scs : List Suspended)
    (rooted : IsRoot before.core.representatives target)
    (incomingBound : ∀ sc ∈ scs, sc.var < before.core.counter) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingCacheAdapter.run checkEmpty r n p h k caller before
      target incoming scs memos.query
    SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before →
    Available caller.checked.native.machine.heap incoming → incoming.free = [] →
    Fits profile caller.checked → Room bits profile → actual.2 = some after →
    ∀ group ∈ metadata.pending, SourcePruningPartialMatch.PendingBound after.core.counter group := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  intro packet available closed fits room observed
  have counterSame := some_cache_counter symbolEquality edgeEquality nodeEquality profile formulas solver
    inventory caller before after memos checkEmpty r n p h k target incoming scs rooted incomingBound
    packet.context packet.valid available closed fits room observed
  rw [counterSame]
  exact packet.bounded

end MicroCFTA.SourceCurrentIncomingSomeCounter
