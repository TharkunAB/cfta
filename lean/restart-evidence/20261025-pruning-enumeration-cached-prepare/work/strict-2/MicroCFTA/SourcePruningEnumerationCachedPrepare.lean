import MicroCFTA.SourcePruningEnumerationCachedChild

namespace MicroCFTA.SourcePruningEnumerationCachedPrepare
open EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Keep rejection distinct from partiality in the cached child preparation. -/
def prepareChild
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (scs : List EnumerationState.Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) :
    Option (List (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard)) :=
  match value with
  | .empty => some []
  | .reference _ => none
  | .node _ _ _ _ =>
      (SourcePruningEnumerationCachedChild.prepareOrdinary heap fuel scs value before).map
        fun result => [result]
  | .union _ _ _ _ | .mu _ _ _ _ =>
      if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
      else
        (encodeNode value).bind fun handle =>
          (SourcePruningEnumerationCachedChild.allocate heap (some handle) before).map
            fun allocation => [(.hole allocation.1, allocation.2)]

/-- Derive the native cached allocation and all stored-state invariants. -/
theorem allocate_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (node : Option Nat) (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (roots : Nat → Nat)
    (realizable : ∀ (handle : Nat), node = some handle →
      ∃ value : InternedConstructorTemplates.Value Symbol NativeGuard,
        lookupNode heap handle = some value ∧
        InternedProbeProvenance.Available heap value ∧ value.free = [])
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (flag : Bool) (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      SourcePruningEnumerationNativeIndex.candidate heap (.unenumerated node []) = some flag ∧
      SourcePruningEnumerationCachedChild.allocate heap node before =
        some (before.core.counter, after) ∧
      ExceptT.run (EnumerationState.allocate node before.core) =
        [.ok (before.core.counter, after.core)] ∧
      after.core = EnumerationState.allocated node before.core ∧
      after.core.values[before.core.counter]? = some (.unenumerated node []) ∧
      after.core.counter = before.core.counter + 1 ∧
      after.core.counter = after.core.values.length ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      after.waiting = before.waiting ∧
      after.expandable = (fun slot => if slot = before.core.counter then flag else before.expandable slot) ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) := by
  have classification : ∃ flag : Bool, SourcePruningEnumerationNativeIndex.candidate heap
      (.unenumerated node []) = some flag := by
    cases node with
    | none => exact ⟨false, rfl⟩
    | some handle =>
        obtain ⟨value, decoded, _available, _closed⟩ := realizable handle rfl
        refine ⟨!(MergedOrdinaryHeight.recursiveBoundary value && true), ?_⟩
        simp only [SourcePruningEnumerationNativeIndex.candidate, decoded, Option.map_some,
          List.isEmpty_nil]
  obtain ⟨flag, classified⟩ := classification
  have freshAbsent : before.core.values[before.core.counter]? = none := by
    exact List.getElem?_eq_none (Nat.le_of_eq storage.aligned.symm)
  have freshFalse : before.expandable before.core.counter = false := by
    apply Option.some.inj
    simpa only [freshAbsent, Option.getD_none, SourcePruningEnumerationNativeIndex.candidate]
      using (flags before.core.counter).symm
  have allocatedRealized : PendingRealized heap (EnumerationState.allocated node before.core) := by
    intro storedSlot storedNode storedScs stored
    change (before.core.values ++ [.unenumerated node []])[storedSlot]? =
      some (.unenumerated (some storedNode) storedScs) at stored
    obtain old | fresh := List.mem_append.mp (List.mem_of_getElem? stored)
    · obtain ⟨oldSlot, oldStored⟩ := List.getElem?_of_mem old
      exact realized oldSlot storedNode storedScs oldStored
    · simp only [List.mem_singleton, UVarValue.unenumerated.injEq] at fresh
      obtain ⟨nodeSame, _scsSame⟩ := fresh
      exact realizable storedNode nodeSame.symm
  have allocatedFlags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      (((EnumerationState.allocated node before.core).values[slot]?).getD .eliminated) =
        some (if slot = before.core.counter then flag else before.expandable slot) := by
    intro slot
    by_cases beforeSlot : slot < before.core.values.length
    · have different : slot ≠ before.core.counter := by
        rw [storage.aligned]
        omega
      simpa only [EnumerationState.allocated, List.getElem?_append_left beforeSlot,
        ite_eq_right different] using flags slot
    · by_cases same : slot = before.core.counter
      · subst slot
        simpa only [EnumerationState.allocated_slot node before.core storage.aligned,
          Option.getD_some, ↓reduceIte] using classified
      · have absent : before.core.values[slot]? = none := by
          exact List.getElem?_eq_none (by omega)
        have wholeAbsent : (EnumerationState.allocated node before.core).values[slot]? = none := by
          apply List.getElem?_eq_none
          simp only [EnumerationState.allocated, List.length_append, List.length_singleton]
          rw [storage.aligned] at same
          omega
        simpa only [wholeAbsent, absent, Option.getD_none, ite_eq_right same] using flags slot
  refine ⟨flag, ⟨EnumerationState.allocated node before.core,
    fun slot => if slot = before.core.counter then flag else before.expandable slot,
    before.waiting⟩, classified, ?_, rfl, rfl,
    EnumerationState.allocated_slot node before.core storage.aligned, rfl,
    EnumerationState.allocated_supply node before.core storage.aligned, rfl, paths,
    allocation_storage node before.core storage, allocatedRealized,
    EnumerationCanonicalWaiting.allocate_correct roots before.core.values node before.waiting counts,
    rfl, rfl, allocatedFlags⟩
  simp only [SourcePruningEnumerationCachedChild.allocate, classified, Option.map_some]
  apply congrArg (fun (expandable : Nat → Bool) => some (before.core.counter,
    (⟨EnumerationState.allocated node before.core, expandable, before.waiting⟩ :
      EnumerationExpandableIndex.Cached Symbol EnumGuard)))
  funext slot
  cases flag with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases same : slot = before.core.counter
      · subst slot
        simpa only [↓reduceIte] using freshFalse
      · simp only [ite_eq_right same]
  | true => rfl

/-- Recursive children allocate an empty bucket and preserve waiting counts. -/
theorem boundary_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (scs : List EnumerationState.Suspended) (roots : Nat → Nat)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    ∃ (handle : Nat) (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol))
      (after : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
      SourcePruningEnumerationShallowChild.prepareChild scs value = some action ∧
      (∀ (fuel : Nat), prepareChild heap fuel scs value before =
        some [(.hole before.core.counter, after)]) ∧
      ExceptT.run (action before.core) = [.ok (.hole before.core.counter, after.core)] ∧
      after.core = EnumerationState.allocated (some handle) before.core ∧
      after.core.values[before.core.counter]? = some (.unenumerated (some handle) []) ∧
      after.core.counter = before.core.counter + 1 ∧
      after.core.counter = after.core.values.length ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
      StorageValid after.core ∧ PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      after.waiting = before.waiting ∧ after.expandable = before.expandable ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      FragmentBound («Symbol» := Symbol) after.core.counter (.hole before.core.counter) := by
  have nonempty : value ≠ .empty := by
    intro emptyValue
    subst value
    cases boundary
  obtain ⟨handle, encoded, decoded, _emptyCase, nonemptyCase⟩ :=
    SourcePruningEnumerationShallowChild.prepareChild_complete heap before.core scs value
      coherent available closed realized storage.aligned nonterminal
  obtain ⟨action, _coreAfter, prepared, _observed, _afterShape, _afterSlot,
    _grows, _alignedAfter, _realizedAfter⟩ := nonemptyCase nonempty
  obtain ⟨flag, after, classified, nativeAllocated, _allocationRaw, shape, stored,
    grows, alignedAfter, forestSame, pathsAfter, storageAfter, realizedAfter,
    countsAfter, waitingSame, _flagShape, flagsAfter⟩ :=
    allocate_complete heap (some handle) before roots (fun storedHandle nodeSame => by
      cases Option.some.inj nodeSame
      exact ⟨value, decoded, available, closed⟩) storage realized paths counts flags
  have flagFalse : flag = false := by
    apply Option.some.inj
    simpa only [SourcePruningEnumerationNativeIndex.candidate, decoded, Option.map_some,
      boundary, List.isEmpty_nil] using classified.symm
  subst flag
  have coreRaw : ExceptT.run (action before.core) =
      [.ok (.hole before.core.counter, after.core)] := by
    cases value with
    | empty => cases boundary
    | reference name => cases boundary
    | node entry edges depth free => cases boundary
    | union entry members depth free =>
        simp only [SourcePruningEnumerationShallowChild.prepareChild, nonterminal,
          Bool.false_eq_true, ↓reduceIte, encoded, Option.some.injEq] at prepared
        rw [← prepared]
        change [(.ok (.hole before.core.counter,
          EnumerationState.allocated (some handle) before.core) :
            Except EnumerationState.Error
              (Fragments.Fragment Symbol × EnumerationState.State Symbol EnumGuard))] = _
        rw [shape]
    | mu entry body depthShape ordinaryShape =>
        simp only [SourcePruningEnumerationShallowChild.prepareChild, nonterminal,
          Bool.false_eq_true, ↓reduceIte, encoded, Option.some.injEq] at prepared
        rw [← prepared]
        change [(.ok (.hole before.core.counter,
          EnumerationState.allocated (some handle) before.core) :
            Except EnumerationState.Error
              (Fragments.Fragment Symbol × EnumerationState.State Symbol EnumGuard))] = _
        rw [shape]
  refine ⟨handle, action, after, encoded, decoded, prepared, ?_, coreRaw, shape,
    stored, grows, alignedAfter, forestSame, pathsAfter, storageAfter, realizedAfter,
    countsAfter, waitingSame, ?_, flagsAfter, ?_⟩
  · intro fuel
    cases value with
    | empty => cases boundary
    | reference name => cases boundary
    | node entry edges depth free => cases boundary
    | union entry members depth free =>
        simp only [prepareChild, nonterminal, Bool.false_eq_true, ↓reduceIte,
          encoded, Option.bind_some, nativeAllocated, Option.map_some]
    | mu entry body depthShape ordinaryShape =>
        simp only [prepareChild, nonterminal, Bool.false_eq_true, ↓reduceIte,
          encoded, Option.bind_some, nativeAllocated, Option.map_some]
  · simp only [SourcePruningEnumerationCachedChild.allocate, classified,
      Option.map_some, Bool.false_eq_true, ↓reduceIte] at nativeAllocated
    exact (congrArg (fun (allocation : Nat × EnumerationExpandableIndex.Cached Symbol EnumGuard) =>
      allocation.2.expandable) (Option.some.inj nativeAllocated)).symm
  · change before.core.counter < after.core.counter
    rw [grows]
    exact Nat.lt_succ_self _

/-- Derive every supported cached child row from the same concrete core action. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (scs : List EnumerationState.Suspended) (roots : Nat → Nat)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : InternedProbeProvenance.Available heap value) (closed : value.free = [])
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (nonterminal : value ≠ .empty → scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ∃ (action : EnumerateM Symbol EnumGuard (Fragments.Fragment Symbol)) (fuel : Nat)
      (rows : List (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard)),
      SourcePruningEnumerationShallowChild.prepareChild scs value = some action ∧
      (∀ (extra : Nat), prepareChild heap (fuel + extra) scs value before = some rows) ∧
      ExceptT.run (action before.core) = rows.map (fun result => .ok (result.1, result.2.core)) ∧
      ((value = .empty ∧ rows = []) ∨
        ∃ after : EnumerationExpandableIndex.Cached Symbol EnumGuard,
          value ≠ .empty ∧ rows = [(.hole before.core.counter, after)] ∧
          after.core.counter = before.core.counter + 1 ∧
          after.core.counter = after.core.values.length ∧
          after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
          StorageValid after.core ∧ PendingRealized heap after.core ∧
          EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
          (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
            ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
          FragmentBound («Symbol» := Symbol) after.core.counter (.hole before.core.counter)) := by
  cases value with
  | empty =>
      refine ⟨reject, 0, [], rfl, ?_, rfl, Or.inl ⟨rfl, rfl⟩⟩
      intro extra
      rfl
  | reference name => cases closed
  | node entry edges depth free =>
      obtain ⟨_handle, action, _allocatedCached, after, fuel, _encoded, _decoded,
        prepared, coreRaw, _nativeAllocated, _allocatedShape, _allocatedStored,
        _allocatedStorage, _allocatedRealized, _allocatedCounts, _allocatedFlags,
        _waitingSame, _nativeRun, prepareRun, _afterShape, _afterSlot, grows,
        alignedAfter, forestSame, pathsAfter, storageAfter, realizedAfter, countsAfter,
        flagsAfter, _flagShape, _waitingCount, holeBound⟩ :=
        SourcePruningEnumerationCachedChild.complete heap before entry edges depth free scs roots
          coherent available closed storage realized paths counts flags bounded
          (nonterminal (by intro emptyValue; cases emptyValue))
      refine ⟨action, fuel, [(.hole before.core.counter, after)], prepared, ?_, coreRaw,
        Or.inr ⟨after, (by intro emptyValue; cases emptyValue), rfl, grows, alignedAfter,
          forestSame, pathsAfter, storageAfter, realizedAfter, countsAfter, flagsAfter, holeBound⟩⟩
      intro extra
      simp only [prepareChild, prepareRun extra, Option.map_some]
  | union entry members depth free =>
      obtain ⟨_handle, action, after, _encoded, _decoded, prepared, prepareRun, coreRaw,
        _shape, _stored, grows, alignedAfter, forestSame, pathsAfter, storageAfter,
        realizedAfter, countsAfter, _waitingSame, _flagSame, flagsAfter, holeBound⟩ :=
        boundary_complete heap before (.union entry members depth free) scs roots
          coherent available closed rfl (nonterminal (by intro emptyValue; cases emptyValue))
          storage realized paths counts flags
      refine ⟨action, 0, [(.hole before.core.counter, after)], prepared, ?_, coreRaw,
        Or.inr ⟨after, (by intro emptyValue; cases emptyValue), rfl, grows, alignedAfter,
          forestSame, pathsAfter, storageAfter, realizedAfter, countsAfter, flagsAfter, holeBound⟩⟩
      intro extra
      exact prepareRun (0 + extra)
  | mu entry body depthShape ordinaryShape =>
      obtain ⟨_handle, action, after, _encoded, _decoded, prepared, prepareRun, coreRaw,
        _shape, _stored, grows, alignedAfter, forestSame, pathsAfter, storageAfter,
        realizedAfter, countsAfter, _waitingSame, _flagSame, flagsAfter, holeBound⟩ :=
        boundary_complete heap before (.mu entry body depthShape ordinaryShape) scs roots
          coherent available closed rfl (nonterminal (by intro emptyValue; cases emptyValue))
          storage realized paths counts flags
      refine ⟨action, 0, [(.hole before.core.counter, after)], prepared, ?_, coreRaw,
        Or.inr ⟨after, (by intro emptyValue; cases emptyValue), rfl, grows, alignedAfter,
          forestSame, pathsAfter, storageAfter, realizedAfter, countsAfter, flagsAfter, holeBound⟩⟩
      intro extra
      exact prepareRun (0 + extra)

end MicroCFTA.SourcePruningEnumerationCachedPrepare
