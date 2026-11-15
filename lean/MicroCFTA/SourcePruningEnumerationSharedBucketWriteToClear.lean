import MicroCFTA.SourcePruningEnumerationSharedIncomingBucketHistory
import MicroCFTA.SourcePruningEnumerationSharedParkedRawBucketReceipt
import MicroCFTA.SourcePruningEnumerationSharedPreparedOpaqueLanguage
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

/-!
# One actual shared write, finalization, callback, and clear

The calls in this segment use their actual preceding endpoints.
The callback's actual decision selects the original incoming raw target.
The later parked read forces the captured finalization to use another slot.
The removed bucket is the full earlier written bucket, with every index intact.
This receipt does not cover intervening child tasks or produce a joint model.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedBucketWriteToClear
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Metadata" => SourcePruningRecordTypes.Metadata

set_option autoImplicit false
attribute [local instance] SourcePruningEnumerationRecursion.recursionMonadList

variable {Typing Key : Type} {width : Nat}
local notation "Fold" => NativeContinuations.Result
  (SourcePruningEnumerationSharedPreparedRecursive.Output width Typing)
  (SourcePruningEnumerationSharedPreparedRecursive.Failure width Typing) width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Fold) →
  (ChildDispatch.Observation width → Option Cached → Fold) → Fold

/-- Actual consecutive shared calls retain the complete written bucket until its parked removal. -/
theorem written_bucket_removed_after_finalize_callback
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (child : Visitor)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel depth target parentTarget : Nat)
    (incoming : Node) (incomingScs : List Suspended) (fragment : Fragment)
    (caller reached : Caller width) (queries savedQueries : Queries)
    (before read : Core) (written finalized parked : Cached)
    (callbackCore checked core : Core) (metadata recorded updated : Metadata Typing) (next : Option Next)
    (total : UnionFind.Total before.representatives)
    (incomingActual : SourcePruningEnumerationSharedIncomingNode.run
      checkEmpty workFuel workFuel workFuel workFuel caller before target incoming incomingScs queries =
        (.ok (some [.ok ((), written.core)]), reached, savedQueries, read))
    (finalizedActual : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
      workFuel parentTarget fragment written = some finalized)
    (callbackActual : ExceptT.run (SourcePruningRecordTypes.recordTypes
      graph templates workFuel metadata parentTarget (.inl fragment) finalized.core) =
        [.ok ((false, recorded), callbackCore)])
    (selected : SourcePruningEnumerationRestart.decision stop order recorded
      (EnumerationExpandableIndex.frame callbackCore finalized) = some (.expand target))
    (parkedActual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
      stop order recorded workFuel workFuel workFuel workFuel workFuel workFuel target reached
      (EnumerationExpandableIndex.frame callbackCore finalized) savedQueries =
        .parked checked (some parked) (some [.ok ((updated, next), core)])) :
    ∃ (found : UnionFind.Result) (oldNode : Option Nat) (oldScs : List Suspended) (handle : Nat)
        (readAfter : Core) (value : Node) (resolved : Core),
      UnionFind.findRoot workFuel before.representatives target = some found ∧
      before.values[found.representative]? = some (.unenumerated oldNode oldScs) ∧
      parentTarget ≠ found.representative ∧
      written.core.values[found.representative]? =
        some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
      ExceptT.run (getValue workFuel target callbackCore) =
        [.ok (.unenumerated (some handle) (incomingScs ++ oldScs), readAfter)] ∧
      callbackCore.values[found.representative]? =
        some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
      UnionFind.Reaches callbackCore.representatives target found.representative found.size ∧
      lookupNode reached.checked.native.machine.heap handle = some value ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧
      ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        reached.checked.native.machine.heap workFuel target handle (incomingScs ++ oldScs) readAfter) =
          [.ok (true, checked)] ∧
      (recursionKey handle (incomingScs ++ oldScs) ∈ before.expansionAncestry ∨
        recursionKey handle (incomingScs ++ oldScs) ∈ before.recursionAncestry found.representative) ∧
      resolved.values[found.representative]? =
        some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
      Success (setValue found.representative (.unenumerated (some handle) [])) resolved () checked ∧
      checked = {resolved with
        values := resolved.values.set found.representative (.unenumerated (some handle) [])} ∧
      parked.core = checked ∧
      SourcePruningEnumerationParkedRestart.adapt reached.checked.native.machine.heap workFuel target
        handle (incomingScs ++ oldScs) (EnumerationExpandableIndex.frame callbackCore finalized) checked =
          some parked ∧
      ExceptT.run (SourcePruningEnumerationRestart.run stop order recorded parked checked) =
        [.ok ((updated, next), core)] ∧
      updated = recorded ∧ core = checked ∧
      (∀ (occurrence : Nat) (sc : Suspended), incomingScs[occurrence]? = some sc →
        (incomingScs ++ oldScs)[occurrence]? = some sc) ∧
      (∀ (occurrence : Nat) (sc : Suspended), oldScs[occurrence]? = some sc →
        (incomingScs ++ oldScs)[incomingScs.length + occurrence]? = some sc) ∧
      (∀ (occurrence : Nat) (sc : Suspended), (incomingScs ++ oldScs)[occurrence]? = some sc →
        (occurrence < incomingScs.length ∧ incomingScs[occurrence]? = some sc) ∨
        (incomingScs.length ≤ occurrence ∧ oldScs[occurrence - incomingScs.length]? = some sc)) ∧
      (∀ (occurrence : Nat) (sc : Suspended), (incomingScs ++ oldScs)[occurrence]? = some sc →
        ∀ other, UnionFind.SameClass checked.representatives sc.var other ↔
          UnionFind.SameClass before.representatives sc.var other) ∧
      SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
          child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (depth + 1))
        graph templates stop order workFuel metadata parentTarget fragment reached savedQueries finalized =
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
        updated reached savedQueries (EnumerationExpandableIndex.frame core parked) next := by
  obtain ⟨found, oldNode, oldScs, handle, lookup, oldSlot, readSame, writtenSame, writtenSlot, ancestry⟩ :=
    SourcePruningEnumerationSharedIncomingNode.singleton_bucket_history
      checkEmpty workFuel workFuel workFuel workFuel caller before target incoming incomingScs queries
      written.core reached savedQueries read incomingActual
  have writtenForest : written.core.representatives = found.forest := by
    rw [writtenSame, readSame]
  have foundPath := (UnionFind.findRoot_correct workFuel before.representatives target found lookup).1
  have writtenPath : UnionFind.Reaches written.core.representatives
      target found.representative found.size := by
    rw [writtenForest]
    exact (UnionFind.findRoot_correct workFuel before.representatives target found lookup).2 foundPath
  have writtenTotal : UnionFind.Total written.core.representatives := by
    intro uv
    obtain ⟨root, size, path⟩ := total uv
    exact ⟨root, size, by
      rw [writtenForest]
      exact (UnionFind.findRoot_correct workFuel before.representatives target found lookup).2 path⟩
  have finalizedSame :=
    SourcePruningEnumerationSharedSelectedOpaqueDispatch.finalized_core_of_run
      reached.checked.native.machine.heap workFuel parentTarget fragment written finalized finalizedActual
  have finalizedForest : finalized.core.representatives = written.core.representatives := by
    rw [finalizedSame]
  have finalizedTotal : UnionFind.Total finalized.core.representatives := by
    rw [finalizedForest]
    exact writtenTotal
  have callbackSuccess : Success (SourcePruningRecordTypes.recordTypes
      graph templates workFuel metadata parentTarget (.inl fragment))
      finalized.core (false, recorded) callbackCore := by
    simp only [Success, callbackActual, List.mem_singleton]
  have callbackFrame := SourcePruningRecordTypes.recordTypes_frame
    graph templates workFuel metadata parentTarget (.inl fragment)
    finalized.core callbackCore (false, recorded) finalizedTotal callbackSuccess
  have callbackTotal : UnionFind.Total callbackCore.representatives := callbackFrame.total finalizedTotal
  have callbackPath : UnionFind.Reaches callbackCore.representatives
      target found.representative found.size := by
    apply (callbackFrame.reaches target found.representative found.size).mpr
    rw [finalizedForest]
    exact writtenPath
  obtain ⟨clearHandle, bucket, readAfter, value, root, size, resolved, rawRead, clearSlot, clearPath,
      _readFrame, nodeLookup, boundary, repeated, _representative, _resolvedFrame, keyMember, resolvedSlot,
      cleared, checkedSame, parkedSame, adapted, restart, metadataSame, coreSame,
      _nextSame, _notStuck, clearAliases, _baseResume⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.parked_singleton_removed_bucket_receipt
      holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth target recorded updated
      reached savedQueries (EnumerationExpandableIndex.frame callbackCore finalized) parked
      checked core next callbackTotal parkedActual
  obtain ⟨rootSame, sizeSame⟩ := UnionFind.reaches_unique clearPath callbackPath
  subst root size
  change callbackCore.values[found.representative]? = some (.unenumerated (some clearHandle) bucket) at clearSlot
  have finalizedSlot : finalized.core.values[found.representative]? =
      some (.unenumerated (some clearHandle) bucket) := by
    rw [← callbackFrame.values]
    exact clearSlot
  have inside : found.representative < written.core.values.length :=
    (List.getElem?_eq_some_iff.mp writtenSlot).1
  have different : parentTarget ≠ found.representative := by
    intro same
    have impossible := finalizedSlot
    rw [finalizedSame] at impossible
    change (written.core.values.set parentTarget (.enumerated fragment))[found.representative]? =
      some (.unenumerated (some clearHandle) bucket) at impossible
    rw [same, List.getElem?_set_self inside] at impossible
    cases impossible
  have retainedSlot : finalized.core.values[found.representative]? =
      some (.unenumerated (some handle) (incomingScs ++ oldScs)) := by
    rw [finalizedSame]
    change (written.core.values.set parentTarget (.enumerated fragment))[found.representative]? =
      some (.unenumerated (some handle) (incomingScs ++ oldScs))
    rw [List.getElem?_set_ne different]
    exact writtenSlot
  have payloadSame := UVarValue.unenumerated.inj (Option.some.inj (retainedSlot.symm.trans finalizedSlot))
  have handleSame : clearHandle = handle := (Option.some.inj payloadSame.1).symm
  have bucketSame : bucket = incomingScs ++ oldScs := payloadSame.2.symm
  subst clearHandle bucket
  have keyAtWritten : recursionKey handle (incomingScs ++ oldScs) ∈
      written.core.recursionAncestry found.representative := by
    change recursionKey handle (incomingScs ++ oldScs) ∈
      callbackCore.recursionAncestry found.representative at keyMember
    rw [callbackFrame.recursionAncestry, finalizedSame] at keyMember
    exact keyMember
  have callbackPaths : ∀ uv root size,
      UnionFind.Reaches callbackCore.representatives uv root size ↔
        UnionFind.Reaches before.representatives uv root size := by
    intro uv root size
    rw [callbackFrame.reaches, finalizedForest, writtenForest]
    exact UnionFind.findRoot_reaches_iff total lookup uv root size
  have callbackClasses : ∀ left right,
      UnionFind.SameClass callbackCore.representatives left right ↔
        UnionFind.SameClass before.representatives left right := by
    intro left right
    simp only [UnionFind.SameClass, callbackPaths]
  have continued := SourcePruningEnumerationSharedPreparedRecursive.continue_recorded
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
      child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (depth + 1))
    graph templates stop order workFuel metadata recorded parentTarget fragment reached savedQueries
    finalized callbackCore callbackActual
  rw [selected] at continued
  have parkedPrefix : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order recorded
      workFuel workFuel workFuel workFuel workFuel workFuel target reached
      (EnumerationExpandableIndex.frame callbackCore finalized) savedQueries =
        .parked checked (some parked) (some [.ok ((updated, next), core)]) := parkedActual
  have sharedRestart :
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (depth + 1)
        recorded reached savedQueries (EnumerationExpandableIndex.frame callbackCore finalized)
        (some (.expand target)) =
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
        updated reached savedQueries (EnumerationExpandableIndex.frame core parked) next := by
    simp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild,
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow, parkedPrefix]
  refine ⟨found, oldNode, oldScs, handle, readAfter, value, resolved, lookup, oldSlot, different,
    writtenSlot, rawRead, clearSlot, callbackPath, nodeLookup, boundary, repeated,
    (ancestry _).mp keyAtWritten, resolvedSlot, cleared, checkedSame, parkedSame, adapted,
    restart, metadataSame, coreSame, ?_, ?_, ?_, ?_, continued.trans sharedRestart⟩
  · intro occurrence sc stored
    have bound : occurrence < incomingScs.length := (List.getElem?_eq_some_iff.mp stored).1
    simpa only [List.getElem?_append_left bound] using stored
  · intro occurrence sc stored
    have outside : incomingScs.length ≤ incomingScs.length + occurrence := Nat.le_add_right _ _
    simpa only [List.getElem?_append_right outside, Nat.add_sub_cancel_left] using stored
  · intro occurrence sc stored
    by_cases inside : occurrence < incomingScs.length
    · exact Or.inl ⟨inside, by simpa only [List.getElem?_append_left inside] using stored⟩
    · have outside : incomingScs.length ≤ occurrence := Nat.le_of_not_gt inside
      exact Or.inr ⟨outside, by simpa only [List.getElem?_append_right outside] using stored⟩
  · intro occurrence sc stored other
    exact (clearAliases occurrence sc stored other).trans (callbackClasses sc.var other)

end MicroCFTA.SourcePruningEnumerationSharedBucketWriteToClear
