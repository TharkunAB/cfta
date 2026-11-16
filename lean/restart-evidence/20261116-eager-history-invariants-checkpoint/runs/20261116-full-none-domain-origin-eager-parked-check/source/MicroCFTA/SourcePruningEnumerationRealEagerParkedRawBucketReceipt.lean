import MicroCFTA.SourcePruningEnumerationSharedParkedRawBucketReceipt
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
import MicroCFTA.SourcePruningEnumerationSharedEagerChildren

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata

set_option autoImplicit false
attribute [local instance] SourcePruningEnumerationRecursion.recursionMonadList

theorem parked_singleton_removed_bucket_receipt
    {Typing Key : Type} {width : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel depth uv : Nat)
    (metadata updated : Metadata Typing) (caller : Caller width) (queries : Queries)
    (before parked : Cached) (checked core : Core) (next : Option Next)
    (total : UnionFind.Total before.core.representatives)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
      .parked checked (some parked) (some [.ok ((updated, next), core)])) :
    ∃ (handle : Nat) (bucket : List Suspended) (readAfter : Core)
        (value : Node) (root size : Nat) (resolved : Core),
      ExceptT.run (getValue workFuel uv before.core) =
        [.ok (.unenumerated (some handle) bucket, readAfter)] ∧
      before.core.values[root]? = some (.unenumerated (some handle) bucket) ∧
      UnionFind.Reaches before.core.representatives uv root size ∧
      Frame before.core readAfter ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧
      ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap workFuel uv handle bucket readAfter) =
          [.ok (true, checked)] ∧
      Success (representative workFuel uv) readAfter root resolved ∧
      Frame readAfter resolved ∧
      recursionKey handle bucket ∈ before.core.recursionAncestry root ∧
      resolved.values[root]? = some (.unenumerated (some handle) bucket) ∧
      Success (setValue root (.unenumerated (some handle) [])) resolved () checked ∧
      checked = {resolved with values := resolved.values.set root (.unenumerated (some handle) [])} ∧
      parked.core = checked ∧
      SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
        workFuel uv handle bucket before checked = some parked ∧
      ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
        [.ok ((updated, next), core)] ∧
      updated = metadata ∧ core = checked ∧
      next = SourcePruningEnumerationRestart.decision stop order metadata parked ∧
      SourcePruningEnumerationRestart.decision stop order metadata parked ≠ some .stuck ∧
      (∀ (occurrence : Nat) (sc : Suspended), bucket[occurrence]? = some sc →
        ∀ other, UnionFind.SameClass checked.representatives sc.var other ↔
          UnionFind.SameClass before.core.representatives sc.var other) ∧
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel (depth + 1)
        metadata caller queries before (some (.expand uv)) =
      SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel depth
        updated caller queries (EnumerationExpandableIndex.frame core parked) next := by
  obtain ⟨handle, bucket, readAfter, value, root, size, resolved,
      reading, stored, path, readFrame, decoded, boundary, checking, represented, representativeFrame,
      seen, resolvedStored, cleared, checkedEq, parkedEq, adapted, restarted,
      updatedEq, coreEq, nextEq, notStuck, targetAliases, _legacyRestart⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.parked_singleton_removed_bucket_receipt
      holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth uv
      metadata updated caller queries before parked checked core next total actual
  refine ⟨handle, bucket, readAfter, value, root, size, resolved,
    reading, stored, path, readFrame, decoded, boundary, checking, represented, representativeFrame,
    seen, resolvedStored, cleared, checkedEq, parkedEq, adapted, restarted,
    updatedEq, coreEq, nextEq, notStuck, targetAliases, ?_⟩
  have prefixActual : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
      .parked checked (some parked) (some [.ok ((updated, next), core)]) := actual
  rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow, prefixActual]

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

#check MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.parked_singleton_removed_bucket_receipt
#print axioms MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.parked_singleton_removed_bucket_receipt
