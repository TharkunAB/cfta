import MicroCFTA.SourceFlatPruningNativeBranches
import MicroCFTA.SourcePruningEnumerationNativeBranchCompletion

/-!
# Native index correctness at each returned receipt

Indexed states the correctness of a cache when the receipt carries one.
It does not assert completion or Safe. A receipt without a cache satisfies True.
-/

namespace MicroCFTA.SourceFlatPruningNativeReceiptValidity
open SourcePruningEnumerationNativeBranchCompletion (CacheValid Admitted)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "FlatReceipt" => SourceFlatPruningSelectedEdge.Result
variable {width : Nat}

/-- State index correctness only for the cache carried by the actual receipt. -/
def Indexed : FlatReceipt width → Prop
  | .complete _ caller _ after | .rejected caller _ after =>
      EnumerationFlatNativeIndex.Correct caller.checked.native.machine.heap after
  | .stopped _ observation (some after) =>
      EnumerationFlatNativeIndex.Correct observation.2.1.checked.native.machine.heap after
  | _ => True

/-- Original cache validity transfers at the same supplied native caller. -/
theorem cache_of_related (caller : Caller width) {flat : FlatCached} {earlier : Cached}
    (related : EnumerationFlatCached.Related flat earlier) (valid : CacheValid caller earlier) :
    EnumerationFlatNativeIndex.Correct caller.checked.native.machine.heap flat := by
  obtain ⟨roots, paths, storage, _realized, counts, flags⟩ := valid
  exact EnumerationFlatNativeIndex.correct_of_related related caller.checked.native.machine.heap
    roots paths storage.aligned flags counts

/-- An admitted original receipt certifies its related flat cache at its own reached heap. -/
theorem of_related (target : Nat) (flat : FlatReceipt width) (earlier : Receipt width)
    (admitted : Admitted target earlier)
    (related : SourceFlatPruningSelectedEdge.ResultRelated flat earlier) : Indexed flat := by
  cases flat with
  | unhandled => trivial
  | rejected reached saved recovered =>
      change EnumerationFlatNativeIndex.Correct reached.checked.native.machine.heap recovered
      cases earlier with
      | unhandled | complete _ _ _ _ | stopped _ _ _ => cases related
      | rejected oldCaller oldQueries oldAfter =>
          obtain ⟨callerSame, _queriesSame, caches⟩ := related
          rw [callerSame]
          exact cache_of_related oldCaller caches admitted
  | complete fragment reached saved recovered =>
      change EnumerationFlatNativeIndex.Correct reached.checked.native.machine.heap recovered
      cases earlier with
      | unhandled | rejected _ _ _ | stopped _ _ _ => cases related
      | complete oldFragment oldCaller oldQueries oldAfter =>
          obtain ⟨_fragmentSame, callerSame, _queriesSame, caches⟩ := related
          rw [callerSame]
          exact cache_of_related oldCaller caches admitted.1
  | stopped fragments observation candidate =>
      cases candidate with
      | none => trivial
      | some recovered =>
          change EnumerationFlatNativeIndex.Correct observation.2.1.checked.native.machine.heap recovered
          cases earlier with
          | unhandled | rejected _ _ _ | complete _ _ _ _ => cases related
          | stopped oldFragments oldObservation oldCandidate =>
              obtain ⟨oldOutcome, oldCaller, oldQueries, oldOuter, oldWaiting⟩ := oldObservation
              obtain ⟨_fragmentsSame,
                ⟨callerSame, _queriesSame, _outerRelated, _waitingSame, _rowsRelated⟩,
                caches⟩ := related
              cases oldCandidate with
              | none => cases caches
              | some oldAfter =>
                  cases oldOutcome with
                  | error fault => cases admitted
                  | ok returned =>
                      cases returned with
                      | none => cases admitted
                      | some rows =>
                          cases rows with
                          | cons row rest => cases admitted
                          | nil =>
                              dsimp only at callerSame
                              rw [callerSame]
                              exact cache_of_related oldCaller caches admitted

/-- Every related processed receipt keeps index correctness at its own returned cache. -/
theorem processed (target : Nat) {flat : List (FlatReceipt width)} {earlier : List (Receipt width)}
    (related : SourceFlatPruningNativeBranches.ReceiptsRelated flat earlier)
    (admitted : ∀ receipt ∈ earlier, Admitted target receipt) :
    ∀ receipt ∈ flat, Indexed receipt := by
  revert admitted
  induction related with
  | nil =>
      intro _admitted receipt member
      cases member
  | @cons first second rest tail head _ ih =>
      intro admitted receipt member
      rcases List.mem_cons.mp member with same | member
      · subst receipt
        exact of_related target first second (admitted second (by simp)) head
      · exact ih (fun current inside => admitted current (List.mem_cons_of_mem _ inside)) receipt member

end MicroCFTA.SourceFlatPruningNativeReceiptValidity
