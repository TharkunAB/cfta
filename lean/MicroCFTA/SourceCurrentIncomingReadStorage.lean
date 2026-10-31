import MicroCFTA.SourceCurrentIncomingOriginalRoot
import MicroCFTA.EnumerationCorrectness

/-! Actual incoming reads retain storage; original uninstantiated slots give exact raw updates. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingReadStorage
open EnumerationState EnumerationSchedule EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationObservation SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat}

/-- Original allocation and storage derive storage on every literal outer read outcome. -/
theorem incoming_read_storage (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (scs : List Suspended) (memos : Memos)
    (storage : StorageValid before) (inside : target < before.counter) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs memos.query
    StorageValid actual.2.2.2 := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  cases rootRead : UnionFind.findRoot r before.representatives target with
  | none => simpa only [SourcePruningEnumerationIncomingNode.run, rootRead] using storage
  | some found =>
      have readStored : StorageValid ({before with representatives := found.forest} : Core) :=
        EnumerationCorrectness.representative_storage before storage r target inside found rootRead
      simp only [SourcePruningEnumerationIncomingNode.run, rootRead]
      repeat' first | exact readStored | split

/-- A successful raw row at an original uninstantiated slot has the exact reference append. -/
theorem unstored_returned_core (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (scs oldScs : List Suspended) (memos : Memos)
    (roots : Nat → Nat) (paths : Roots before.representatives roots)
    (rooted : IsRoot before.representatives target) (storage : StorageValid before)
    (inside : target < before.counter)
    (coherent : InternedRecordCoherence.Coherent caller.checked.native.machine.heap)
    (realized : PendingRealized caller.checked.native.machine.heap before)
    (available : InternedProbeProvenance.Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (stored : before.values[target]? = some (.unenumerated none oldScs))
    (bounded : ∀ sc ∈ scs ++ oldScs, sc.var < before.counter) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs memos.query
    ∀ returned, actual.1 = .ok (some [.ok ((), returned)]) →
      actual.2.1 = caller ∧ actual.2.2.1 = memos.query ∧
      ∃ handle, encodeNode incoming = some handle ∧
        returned = {actual.2.2.2 with
          values := actual.2.2.2.values.set target (.unenumerated (some handle) (scs ++ oldScs))
          recursionAncestry := fun other => if other = target then
            (actual.2.2.2.expansionAncestry ++ actual.2.2.2.recursionAncestry target).eraseDups
            else actual.2.2.2.recursionAncestry other} ∧
        returned.representatives = actual.2.2.2.representatives ∧
        returned.counter = before.counter ∧
        returned.values[target]? = some (.unenumerated (some handle) (scs ++ oldScs)) ∧
        references ((returned.values[target]?).getD .eliminated) = scs ++ oldScs ∧
        Roots returned.representatives roots ∧ StorageValid returned ∧
        PendingRealized actual.2.1.checked.native.machine.heap returned := by
  letI : DecidableEq Symbol := symbolEquality
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := nodeEquality
  dsimp only
  intro returned observed
  cases rootRead : UnionFind.findRoot r before.representatives target with
  | none => simp [SourcePruningEnumerationIncomingNode.run, rootRead] at observed
  | some found =>
      have targetSame := SourceCurrentIncomingOriginalRoot.original_target
        before.representatives r target rooted found rootRead
      cases encoded : encodeNode incoming with
      | none =>
          simp [SourcePruningEnumerationIncomingNode.run, rootRead, targetSame, stored, encoded] at observed
      | some handle =>
          let read : Core := {before with representatives := found.forest}
          have callerSame : (SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
              caller before target incoming scs memos.query).2.1 = caller := by
            simp only [SourcePruningEnumerationIncomingNode.run, rootRead, targetSame, stored, encoded]
          have queriesSame : (SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
              caller before target incoming scs memos.query).2.2.1 = memos.query := by
            simp only [SourcePruningEnumerationIncomingNode.run, rootRead, targetSame, stored, encoded]
          have coreSame : (SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
              caller before target incoming scs memos.query).2.2.2 = read := by
            simp only [SourcePruningEnumerationIncomingNode.run, rootRead, targetSame, stored, encoded, read]
          have readStored : StorageValid read :=
            EnumerationCorrectness.representative_storage before storage r target inside found rootRead
          have readRealized : PendingRealized caller.checked.native.machine.heap read := by
            intro slot nodeHandle suspensions valueRead
            exact realized slot nodeHandle suspensions valueRead
          have readInside : target < read.values.length := by
            have aligned : before.counter = before.values.length := storage.aligned
            change target < before.values.length
            rw [← aligned]
            exact inside
          have readBound : ∀ sc ∈ scs ++ oldScs, sc.var < read.counter := bounded
          obtain ⟨produced, _block, finished, producedSame, producedSlot, producedStored, producedRealized⟩ :=
            SourcePruningEnumerationIncomingNode.finish_complete caller.checked.native.machine.heap
              read incoming target handle scs oldScs coherent available closed encoded readRealized
              readStored readInside readBound
          have rawObserved : ExceptT.run
              (SourcePruningEnumerationIncomingNode.finish target handle scs oldScs incoming read) =
              [.ok ((), returned)] := by
            simpa [SourcePruningEnumerationIncomingNode.run, rootRead, targetSame, stored, encoded, read] using observed
          rw [finished] at rawObserved
          by_cases empty : incoming = .empty
          · simp [empty] at rawObserved
          · have returnedSame : returned = produced := by simpa [empty] using rawObserved.symm
            have readFacts := SourceCurrentIncomingReadRoots.incoming_read_roots symbolEquality edgeEquality
              nodeEquality checkEmpty r n p h caller before target incoming scs memos roots paths
            dsimp only at readFacts
            rw [coreSame] at readFacts
            have producedRoots : Roots produced.representatives roots := by
              simpa only [producedSame] using readFacts.1
            have producedCounter : produced.counter = before.counter := by rw [producedSame]
            have producedRepresentatives : produced.representatives = read.representatives := by
              rw [producedSame]
            have producedReferences : references ((produced.values[target]?).getD .eliminated) = scs ++ oldScs := by
              rw [producedSlot]
              rfl
            refine ⟨callerSame, queriesSame, handle, rfl, ?_⟩
            rw [coreSame, callerSame, returnedSame]
            exact ⟨producedSame, producedRepresentatives, producedCounter, producedSlot,
              producedReferences, producedRoots, producedStored, producedRealized⟩

end MicroCFTA.SourceCurrentIncomingReadStorage
