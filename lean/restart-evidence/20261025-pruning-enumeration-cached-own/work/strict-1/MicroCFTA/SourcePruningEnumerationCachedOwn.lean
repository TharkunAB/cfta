import MicroCFTA.SourcePruningEnumerationCachedPrepare
import MicroCFTA.SourcePruningEnumerationEdgePrefix

namespace MicroCFTA.SourcePruningEnumerationCachedOwn
open EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {EnumGuard NativeGuard : Type}

/-- Allocate the selected own-class tries in their actual order. -/
def suspendMany
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) :
    List EqualityTrie.Trie → EnumerationExpandableIndex.Cached Symbol EnumGuard →
      Option (List EnumerationState.Suspended × EnumerationExpandableIndex.Cached Symbol EnumGuard)
  | [], before => some ([], before)
  | trie :: rest, before =>
      (SourcePruningEnumerationCachedChild.allocate heap none before).bind fun allocation =>
        (suspendMany heap rest allocation.2).map fun result =>
          (⟨trie, allocation.1⟩ :: result.1, result.2)

/-- Allocate own classes and capture the existing ordered child actions. -/
noncomputable def prepare
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    Option (List ((Symbol ×
      List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended ×
        Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) × Option Constraint) ×
      EnumerationExpandableIndex.Cached Symbol Constraint)) :=
  if arityAllows edge.children.length scs then
    match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => none
    | some (tries, residual) =>
        (suspendMany heap tries before).map fun result =>
          [((edge.entry.key.symbol,
            edge.children.zipIdx.map (fun indexed =>
              (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 result.1,
                SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                  (descendScs indexed.2 scs ++ descendScs indexed.2 result.1) indexed.1)),
            residual), result.2)]
  else some []

/-- Derive the cached own-class traversal and the exact existing core endpoint. -/
theorem suspendMany_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (tries : List EqualityTrie.Trie) (roots : Nat → Nat) :
    ∀ (before : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      StorageValid before.core → PendingRealized heap before.core →
      Roots before.core.representatives roots →
      EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting →
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) →
      ∃ after : EnumerationExpandableIndex.Cached Symbol EnumGuard,
        suspendMany heap tries before = some (suspendedVars before.core.counter tries, after) ∧
        after.core = suspendedState tries.length before.core ∧
        after.core.counter = before.core.counter + tries.length ∧
        after.core.counter = after.core.values.length ∧
        after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
        StorageValid after.core ∧ PendingRealized heap after.core ∧
        EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
        after.waiting = before.waiting ∧ after.expandable = before.expandable ∧
        (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
          ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) := by
  induction tries with
  | nil =>
    intro before storage realized paths counts flags
    exact ⟨before, rfl, rfl, rfl, storage.aligned, rfl, paths, storage,
      realized, counts, rfl, rfl, flags⟩
  | cons trie rest ih =>
    intro before storage realized paths counts flags
    obtain ⟨_flag, middle, _classified, nativeAllocated, _allocationRaw, middleShape,
      _middleStored, middleCounter, _middleAligned, middleForest, middlePaths,
      middleStorage, middleRealized, middleCounts, middleWaiting, _middleFlagShape,
      middleFlags⟩ := SourcePruningEnumerationCachedPrepare.allocate_complete heap none
        before roots (by intro _handle impossible; cases impossible) storage realized paths counts flags
    have middleFlagsSame : middle.expandable = before.expandable := by
      change some (before.core.counter,
          (⟨EnumerationState.allocated none before.core, before.expandable, before.waiting⟩ :
            EnumerationExpandableIndex.Cached Symbol EnumGuard)) =
        some (before.core.counter, middle) at nativeAllocated
      exact (congrArg (fun allocation : Nat × EnumerationExpandableIndex.Cached Symbol EnumGuard =>
        allocation.2.expandable) (Option.some.inj nativeAllocated)).symm
    obtain ⟨after, tailRun, tailShape, tailCounter, alignedAfter, forestSame, pathsAfter,
      storageAfter, realizedAfter, countsAfter, waitingSame, flagsSame, flagsAfter⟩ :=
        ih middle middleStorage middleRealized middlePaths middleCounts middleFlags
    have coreSame : after.core = suspendedState (trie :: rest).length before.core := by
      simpa only [List.length_cons, suspendedState, middleShape] using tailShape
    refine ⟨after, ?_, coreSame, ?_, alignedAfter, forestSame.trans middleForest,
      pathsAfter, storageAfter, realizedAfter, countsAfter, waitingSame.trans middleWaiting,
      flagsSame.trans middleFlagsSame, flagsAfter⟩
    · simp only [suspendMany, nativeAllocated, Option.bind_some, tailRun, Option.map_some,
        suspendedVars, middleCounter]
    · rw [tailCounter, middleCounter, List.length_cons]
      omega

/-- Match the actual selected-edge prefix and retain both native indexes. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (scs : List EnumerationState.Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint) (roots : Nat → Nat)
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) :
    if arityAllows edge.children.length scs then
      match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
      | none => prepare heap scs edge before = none ∧
          SourcePruningEnumerationEdgePrefix.prepare scs edge = none
      | some (tries, residual) =>
          let own : List EnumerationState.Suspended := suspendedVars before.core.counter tries
          let staged := edge.children.zipIdx.map (fun indexed =>
            (indexed.1, descendScs indexed.2 scs ++ descendScs indexed.2 own,
              SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
                (descendScs indexed.2 scs ++ descendScs indexed.2 own) indexed.1))
          ∃ (action : EnumerateM Symbol Constraint (Symbol ×
              List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended ×
                Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) × Option Constraint))
            (after : EnumerationExpandableIndex.Cached Symbol Constraint),
            SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
            prepare heap scs edge before = some [((edge.entry.key.symbol, staged, residual), after)] ∧
            ExceptT.run (action before.core) = [.ok ((edge.entry.key.symbol, staged, residual), after.core)] ∧
            after.core = suspendedState tries.length before.core ∧
            after.core.counter = before.core.counter + tries.length ∧
            after.core.counter = after.core.values.length ∧
            after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
            StorageValid after.core ∧ PendingRealized heap after.core ∧
            EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
            after.waiting = before.waiting ∧ after.expandable = before.expandable ∧
            (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
              ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot))
    else prepare heap scs edge before = some [] ∧
      SourcePruningEnumerationEdgePrefix.prepare scs edge = some reject := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · simp only [allowed, ↓reduceIte]
    cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
      simp only [prepare, SourcePruningEnumerationEdgePrefix.prepare, allowed, ↓reduceIte, projected]
    | some pair =>
      obtain ⟨tries, residual⟩ := pair
      dsimp only
      let staged : List (InternedConstructorTemplates.Value Symbol Constraint ×
          List EnumerationState.Suspended ×
          Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) :=
        edge.children.zipIdx.map (fun indexed =>
          (indexed.1, descendScs indexed.2 scs ++
            descendScs indexed.2 (suspendedVars before.core.counter tries),
            SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint)
              (descendScs indexed.2 scs ++
                descendScs indexed.2 (suspendedVars before.core.counter tries)) indexed.1))
      obtain ⟨after, ownRun, shape, grows, alignedAfter, forestSame, pathsAfter,
        storageAfter, realizedAfter, countsAfter, waitingSame, flagsSame, flagsAfter⟩ :=
          suspendMany_complete heap tries roots before storage realized paths counts flags
      have sourcePrefix : ∃ action : EnumerateM Symbol Constraint (Symbol ×
          List (InternedConstructorTemplates.Value Symbol Constraint × List EnumerationState.Suspended ×
            Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))) × Option Constraint),
        SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
        ExceptT.run (action before.core) =
          [.ok ((edge.entry.key.symbol, staged, residual), suspendedState tries.length before.core)] ∧
        (suspendedState tries.length before.core).counter = before.core.counter + tries.length ∧
        (suspendedState tries.length before.core).counter =
          (suspendedState tries.length before.core).values.length ∧
        PendingRealized heap (suspendedState tries.length before.core) := by
        simpa only [allowed, ↓reduceIte, projected] using
          SourcePruningEnumerationEdgePrefix.prepare_complete scs edge heap before.core
            realized storage.aligned
      obtain ⟨action, prepared, observed, _counter, _aligned, _realized⟩ := sourcePrefix
      refine ⟨action, after, prepared, ?_, ?_, shape, grows, alignedAfter, forestSame,
        pathsAfter, storageAfter, realizedAfter, countsAfter, waitingSame, flagsSame, flagsAfter⟩
      · simp only [prepare, allowed, ↓reduceIte, projected, ownRun, Option.map_some]
      · rw [shape]
        exact observed
  · simp [allowed, prepare, SourcePruningEnumerationEdgePrefix.prepare]

end MicroCFTA.SourcePruningEnumerationCachedOwn
