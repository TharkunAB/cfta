import MicroCFTA.SourcePruningEnumerationIncomingQuery
import MicroCFTA.EnumerationCompleteness
import MicroCFTA.EnumerationExecution
import MicroCFTA.SourcePruningEnumerationWrites

namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationExecution
open EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation SourcePruningEnumerationWrites
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

local instance incomingNodeMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Write the incoming payload and inherit ancestry before Empty rejection. -/
def finish (target handle : Nat) (incomingScs oldScs : List EnumerationState.Suspended)
    (replacement : Node) : EnumerateM Symbol EnumGuard Unit := do
  setValue target (.unenumerated (some handle) (incomingScs ++ oldScs))
  inheritAncestry target
  match replacement with
  | .empty => reject
  | _ => pure ()

/-- Execute the incoming merge and retain the actual reached read endpoint. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard))))) ×
      Caller width × Queries × EnumerationState.State Symbol EnumGuard :=
  match UnionFind.findRoot representativeFuel before.representatives uv with
  | none => (.ok (some [.error .representativeFuel]), beforeCaller, queries, before)
  | some found =>
      let readState : EnumerationState.State Symbol EnumGuard := {before with representatives := found.forest}
      match before.values[found.representative]? with
      | none => (.ok (some [.error .invalidSlot]), beforeCaller, queries, readState)
      | some (.unenumerated oldNode oldScs) =>
          match oldNode with
          | none =>
              match encodeNode incoming with
              | none => (.ok none, beforeCaller, queries, readState)
              | some handle =>
                  (.ok (some (ExceptT.run (finish found.representative handle incomingScs oldScs incoming readState))),
                    beforeCaller, queries, readState)
          | some oldHandle =>
              match lookupNode beforeCaller.checked.native.machine.heap oldHandle with
              | none => (.ok none, beforeCaller, queries, readState)
              | some old =>
                  let actual : SourceEqualityNativeDemand.Outcome width Node :=
                    SourceEqualityNativeDemand.execute nativeFuel
                      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                      beforeCaller.checked
                  match actual with
                  | .done query queried =>
                      let phase : SourceCurrentAllocatedConjunctionWorker.Outcome width × Queries :=
                        if checkEmpty then
                          SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                        else (.done false queried beforeCaller.fourth, queries)
                      let afterCaller : Caller width :=
                        SourceCurrentAllocatedPartialState.advance beforeCaller phase.1.state phase.1.memo beforeCaller.merge
                      match phase.1 with
                      | .done answer checkedAfter saved =>
                          let replacement : Node := if answer then .empty else query
                          match encodeNode replacement with
                          | none => (.ok none, afterCaller, phase.2, readState)
                          | some handle =>
                              (.ok (some (ExceptT.run (finish found.representative handle incomingScs oldScs replacement readState))),
                                afterCaller, phase.2, readState)
                      | .failed fault checkedAfter saved =>
                          (.error (.inr (.failed fault checkedAfter saved)), afterCaller, phase.2, readState)
                  | other =>
                      (.error (.inl other), SourceCurrentAllocatedPartialState.advance
                        beforeCaller other.state beforeCaller.fourth beforeCaller.merge, queries, readState)
      | some _ => (.ok (some [.error .invalidIntersection]), beforeCaller, queries, readState)

/-- Derive the exact write prefix, raw rejection and preserved storage. -/
theorem finish_complete [DecidableEq Node]
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : EnumerationState.State Symbol EnumGuard) (replacement : Node) (target handle : Nat)
    (incomingScs oldScs : List EnumerationState.Suspended)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : Available heap replacement) (closed : replacement.free = [])
    (encoded : encodeNode replacement = some handle)
    (realized : PendingRealized heap before) (storage : StorageValid before)
    (inside : target < before.values.length)
    (bounded : ∀ sc ∈ incomingScs ++ oldScs, sc.var < before.counter) :
    ∃ after : EnumerationState.State Symbol EnumGuard,
      ExceptT.run ((do
        setValue target (.unenumerated (some handle) (incomingScs ++ oldScs))
        inheritAncestry target) before) = [.ok ((), after)] ∧
      ExceptT.run (finish target handle incomingScs oldScs replacement before) =
        (if replacement = .empty then [] else [.ok ((), after)]) ∧
      after = {before with
        values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = target then
          (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
          else before.recursionAncestry other} ∧
      after.values[target]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
      StorageValid after ∧ PendingRealized heap after := by
  obtain ⟨writtenHandle, middle, writtenEncoded, _written, middleSame, middleStored, middleRealized⟩ :=
    write_available_realized heap before replacement target (incomingScs ++ oldScs)
      coherent available closed realized inside
  have sameHandle : writtenHandle = handle := by
    exact Option.some.inj (writtenEncoded.symm.trans encoded)
  subst writtenHandle
  subst middle
  let after : EnumerationState.State Symbol EnumGuard :=
    {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other}
  have raw : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      (if replacement = .empty then [] else [.ok ((), after)]) := by
    cases replacement with
    | empty => simp only [↓reduceIte]; rfl
    | reference name => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | node entry edges depth free => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | union entry members depth free => simp only [reduceCtorEq, ↓reduceIte]; rfl
    | mu entry body depthShape ordinaryShape => simp only [reduceCtorEq, ↓reduceIte]; rfl
  have afterStorage : StorageValid after := by
    exact ⟨(set_storage before storage target _ bounded).aligned,
      storage.total, storage.forest, (set_storage before storage target _ bounded).values, storage.guards⟩
  exact ⟨after, rfl, raw, rfl, middleStored, afterStorage, middleRealized⟩

/-- Construct finite execution from a realized pending root and current bounds. -/
theorem run_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard)
    (checkEmpty : Bool) (uv : Nat) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (storage : StorageValid before) (root : EnumerationSchedule.IsRoot before.representatives uv)
    (pending : EnumerationCompleteness.PendingAt before uv)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (bounded : ∀ sc ∈ incomingScs, sc.var < before.counter)
    (ranges : match before.values[uv]? with
      | some (.unenumerated (some oldHandle) _) =>
          match lookupNode beforeCaller.checked.native.machine.heap oldHandle with
          | some old => SourceCurrentAllocatedNativeRequestBounds.WordRanges
              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
              beforeCaller.checked
          | none => True
      | _ => True) :
    ∃ (r n p h : Nat) (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
      (read after : EnumerationState.State Symbol EnumGuard) (afterCaller : Caller width)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (replacement : Node) (handle : Nat),
      (∀ extra, ExceptT.run (getValue (r + extra) uv before) =
        [.ok (.unenumerated oldNode oldScs, read)]) ∧
      EnumerationCompressionFrame.Frame before read ∧
      (∀ extra extraNative P H, p ≤ P → h ≤ H →
        run checkEmpty (r + extra) (n + extraNative) P H beforeCaller before uv incoming incomingScs memos.query =
          (.ok (some (if replacement = .empty then [] else [.ok ((), after)])),
            afterCaller, savedQueries, read)) ∧
      ExceptT.run ((do
        setValue uv (.unenumerated (some handle) (incomingScs ++ oldScs))
        inheritAncestry uv) read) = [.ok ((), after)] ∧
      after = {read with
        values := read.values.set uv (.unenumerated (some handle) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = uv then
          (read.expansionAncestry ++ read.recursionAncestry uv).eraseDups else read.recursionAncestry other} ∧
      after.values[uv]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
      StorageValid after ∧ PendingRealized afterCaller.checked.native.machine.heap after ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      Cache.Extends memos.unfolding final.unfolding ∧
      Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
      encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
      (oldNode = none → replacement = incoming ∧ afterCaller = beforeCaller ∧
        savedQueries = memos.query ∧ final = memos ∧ next = inventory) ∧
      (∀ oldHandle, oldNode = some oldHandle →
        ∃ (old query : Node) (queried : Checked width),
          lookupNode beforeCaller.checked.native.machine.heap oldHandle = some old ∧
          next.source = beforeCaller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [incoming, old] ∧
          SourceCurrentAllocatedTargetQuery.Receipt formulas solver next incoming old beforeCaller.checked query queried memos ∧
          (∀ ambient term,
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient old term) ∧
          (checkEmpty = false → replacement = query ∧
            afterCaller = SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge ∧
            final = memos)) := by
  obtain ⟨oldNode, oldScs, stored⟩ := pending
  obtain ⟨size, path⟩ := root
  obtain ⟨r, found, lookup⟩ := UnionFind.findRoot_terminates path
  have representativeSame : found.representative = uv := by
    exact (UnionFind.reaches_unique
      (UnionFind.findRoot_correct r before.representatives uv found lookup).1 path).1
  have lookupMore : ∀ (extra : Nat),
      UnionFind.findRoot (r + extra) before.representatives uv = some found := by
    intro extra
    exact UnionFind.findRoot_moreFuel r extra before.representatives uv found lookup
  let read : EnumerationState.State Symbol EnumGuard := {before with representatives := found.forest}
  have reading : ∀ (extra : Nat), ExceptT.run (getValue (r + extra) uv before) =
      [.ok (.unenumerated oldNode oldScs, read)] := by
    intro extra
    simp [getValue, rawValue, representative, lookupMore extra, representativeSame, stored, read,
      bind, get, getThe, MonadStateOf.get, set, pure,
      StateT.bind, StateT.pure, StateT.get, StateT.set,
      ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run]
  have representativeRun : Success (representative r uv) before uv read := by
    exact (representative_success r uv before read uv).mpr
      ⟨found, lookup, representativeSame.symm, rfl⟩
  have frame : Frame before read := by
    exact representative_frame r uv uv before read storage.total representativeRun
  have readStorage : StorageValid read := by
    exact representative_storage before storage r uv (by
      rw [storage.aligned]
      exact (List.getElem?_eq_some_iff.mp stored).elim (fun bound _elementEquality => bound)) found lookup
  have readRealized : PendingRealized beforeCaller.checked.native.machine.heap read := by
    intro slot node scs currentStored
    exact realized slot node scs currentStored
  have mergedBounded : ∀ sc ∈ incomingScs ++ oldScs, sc.var < read.counter := by
    intro sc member
    rcases List.mem_append.mp member with incomingMember | oldMember
    · exact bounded sc incomingMember
    · exact (storage.values (.unenumerated oldNode oldScs) (List.mem_of_getElem? stored)) sc oldMember
  cases oldNode with
  | none =>
    obtain ⟨handle, encoded, decoded⟩ := available_readback beforeCaller.checked.native.machine.heap incoming
      initial.ready.semantic.1.normal.facts.coherent available closed
    obtain ⟨after, writePrefix, raw, afterSame, afterStored, afterStorage, afterRealized⟩ :=
      finish_complete beforeCaller.checked.native.machine.heap read incoming uv handle incomingScs oldScs
        initial.ready.semantic.1.normal.facts.coherent available closed encoded readRealized readStorage
        ((List.getElem?_eq_some_iff.mp stored).elim (fun bound _elementEquality => bound)) mergedBounded
    refine ⟨r, 0, 0, 0, none, oldScs, read, after, beforeCaller, memos.query, memos, inventory, incoming, handle,
      reading, frame, ?_, writePrefix, afterSame, afterStored, afterStorage, afterRealized,
      Post.refl initial, rfl, Cache.extends_refl _, available, closed, encoded, decoded, ?_, ?_⟩
    · intro extra extraNative P H enoughP enoughH
      simp only [run, lookupMore extra, representativeSame, stored, encoded, raw]
      rfl
    · intro noneEq
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · intro requestedHandle someEq
      cases someEq
  | some oldHandle =>
    obtain ⟨old, oldDecoded, oldAvailable, oldClosed⟩ := realized uv oldHandle oldScs stored
    have decodedRanges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
        beforeCaller.checked := by
      simpa only [stored, oldDecoded] using ranges
    obtain ⟨next, query, queried, answer, checkedAfter, saved, final, queries, replacement, handle, n, p, h,
      nextSource, nextRoots, receipt, nativeStable, checkStable, actualPost, querySame, unfolding,
      _sound, replacementSame, replacementAvailable, replacementClosed, encoded, decoded, meaning, disabled, _enabled⟩ :=
      SourcePruningEnumerationIncomingQuery.complete formulas solver inventory beforeCaller incoming old checkEmpty memos
        initial available oldAvailable closed oldClosed decodedRanges
    have finalRealized : PendingRealized checkedAfter.native.machine.heap read := by
      exact realized_preserved beforeCaller.checked.native.machine.heap checkedAfter.native.machine.heap
        before read realized frame actualPost.effects.keeps
    obtain ⟨after, writePrefix, raw, afterSame, afterStored, afterStorage, afterRealized⟩ :=
      finish_complete checkedAfter.native.machine.heap read replacement uv handle incomingScs oldScs
        actualPost.effects.keeps.ready.semantic.1.normal.facts.coherent replacementAvailable replacementClosed
        encoded finalRealized readStorage
        ((List.getElem?_eq_some_iff.mp stored).elim (fun bound _elementEquality => bound)) mergedBounded
    refine ⟨r, n, p, h, some oldHandle, oldScs, read, after,
      SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge,
      queries, final, next, replacement, handle, reading, frame, ?_, writePrefix, afterSame, afterStored,
      afterStorage, afterRealized, actualPost, querySame, unfolding, replacementAvailable, replacementClosed,
      encoded, decoded, ?_, ?_⟩
    · intro extra extraNative P H enoughP enoughH
      simp only [run, lookupMore extra, representativeSame, stored, oldDecoded, nativeStable extraNative,
        checkStable P H enoughP enoughH, SourceCurrentAllocatedConjunctionWorker.Outcome.state,
        SourceCurrentAllocatedConjunctionWorker.Outcome.memo, ← replacementSame, encoded, raw]
      rfl
    · intro noneEq
      cases noneEq
    · intro requestedHandle someEq
      cases Option.some.inj someEq
      refine ⟨old, query, queried, oldDecoded, nextSource, nextRoots, receipt, meaning, ?_⟩
      intro disabledFlag
      obtain ⟨_answerFalse, replacementQuery, checkedSame, savedSame, _queriesSame, finalSame⟩ := disabled disabledFlag
      exact ⟨replacementQuery, by rw [checkedSame, savedSame], finalSame⟩

end MicroCFTA.SourcePruningEnumerationIncomingNode
