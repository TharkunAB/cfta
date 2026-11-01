import MicroCFTA.SourceCurrentIncomingFinishWitness

/-! Actual singleton finish executions derive the returned core and exact reference append. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingSingletonCore
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
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

/-- Original admissions derive actual returned core effects for either stored handle option. -/
theorem singleton_core_effects (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (checkEmpty : Bool) (r n p h target : Nat) (incoming : Node) (scs oldScs : List Suspended)
    (oldNode : Option Nat) (rooted : IsRoot before.core.representatives target)
    (stored : before.core.values[target]? = some (.unenumerated oldNode oldScs))
    (inside : target < before.core.counter)
    (bounded : ∀ sc ∈ scs ++ oldScs, sc.var < before.core.counter) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    Context formulas solver inventory caller memos → CacheValid caller before →
    Available caller.checked.native.machine.heap incoming → incoming.free = [] →
    Fits profile caller.checked → Room bits profile →
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before.core target incoming scs memos.query
    ∀ returned, actual.1 = .ok (some [.ok ((), returned)]) →
      ∃ handle,
        returned = {actual.2.2.2 with
          values := actual.2.2.2.values.set target (.unenumerated (some handle) (scs ++ oldScs))
          recursionAncestry := fun other => if other = target then
            (actual.2.2.2.expansionAncestry ++ actual.2.2.2.recursionAncestry target).eraseDups
            else actual.2.2.2.recursionAncestry other} ∧
        returned.representatives = actual.2.2.2.representatives ∧ returned.counter = before.core.counter ∧
        returned.values[target]? = some (.unenumerated (some handle) (scs ++ oldScs)) ∧
        references ((returned.values[target]?).getD .eliminated) = scs ++ oldScs ∧
        StorageValid returned ∧ PendingRealized actual.2.1.checked.native.machine.heap returned := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  intro initial valid available closed fits room returned observed
  have validBefore := valid
  obtain ⟨roots, paths, storage, _realized, _counts, _flags⟩ := valid
  have frameFacts := SourceCurrentIncomingReadFrame.incoming_ok_frame_valid symbolEquality edgeEquality
    nodeEquality profile formulas solver inventory caller before memos checkEmpty r n p h target incoming
    scs inside initial validBefore available closed fits room
  have finishFacts := SourceCurrentIncomingFinishWitness.singleton_finish symbolEquality edgeEquality nodeEquality
    profile formulas solver inventory caller before memos checkEmpty r n p h target incoming scs oldScs
    oldNode rooted stored initial validBefore available closed fits room returned observed
  have readFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality nodeEquality
    checkEmpty r n p h caller before.core target incoming scs memos roots paths
  change (let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h caller before.core target incoming scs memos.query;
    match actual.1 with
    | .ok _ => ∃ next final, Post formulas solver next caller actual.2.1 final ∧
        final.query = actual.2.2.1 ∧ CacheValid actual.2.1 (EnumerationExpandableIndex.frame actual.2.2.2 before)
    | .error _ => True) at frameFacts
  dsimp only at frameFacts finishFacts readFacts ⊢
  generalize actualRun : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
    caller before.core target incoming scs memos.query = actual at frameFacts finishFacts readFacts observed ⊢
  rcases actual with ⟨result, reached, savedQueries, read⟩
  cases result with
  | error fault => simp at observed
  | ok output =>
      dsimp only at frameFacts finishFacts readFacts observed ⊢
      obtain ⟨_next, _final, post, _querySame, frameValid⟩ := frameFacts
      obtain ⟨_readRoots, _readPaths, readStored, readRealized, _readCounts, _readFlags⟩ := frameValid
      obtain ⟨replacement, handle, replacementAvailable, replacementClosed, encoded, finishedActual⟩ := finishFacts
      have coherent := post.context.ready.good.heap.semantic.1.normal.facts.coherent
      have readInside : target < read.values.length := by
        rw [readFacts.2.1, ← storage.aligned]
        exact inside
      have readBound : ∀ sc ∈ scs ++ oldScs, sc.var < read.counter := by
        intro sc member
        rw [readFacts.2.2]
        exact bounded sc member
      obtain ⟨produced, _block, finished, producedSame, producedSlot, producedStored, producedRealized⟩ :=
        SourcePruningEnumerationIncomingNode.finish_complete reached.checked.native.machine.heap read replacement
          target handle scs oldScs coherent replacementAvailable replacementClosed encoded readRealized
          readStored readInside readBound
      rw [finished] at finishedActual
      by_cases empty : replacement = .empty
      · simp [empty] at finishedActual
      · have returnedSame : returned = produced := by simpa [empty] using finishedActual.symm
        have producedRepresentatives : produced.representatives = read.representatives := by rw [producedSame]
        have producedCounter : produced.counter = before.core.counter := by
          rw [producedSame]
          exact readFacts.2.2
        have producedReferences : references ((produced.values[target]?).getD .eliminated) = scs ++ oldScs := by
          rw [producedSlot]
          rfl
        refine ⟨handle, ?_⟩
        rw [returnedSame]
        exact ⟨producedSame, producedRepresentatives, producedCounter, producedSlot,
          producedReferences, producedStored, producedRealized⟩

end MicroCFTA.SourceCurrentIncomingSingletonCore
