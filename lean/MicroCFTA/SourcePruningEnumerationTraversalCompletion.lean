import MicroCFTA.SourcePruningEnumerationChildCompletion

namespace MicroCFTA.SourcePruningEnumerationTraversalCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}

/-- Numeric admission follows actual successful prefixes without assuming suffix completion. -/
def Ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) :
    List (Node × List Suspended) → Caller width → Cached → Queries → Prop
  | [], _, _, _ => True
  | (incoming, bucket) :: rest, caller, before, queries =>
      SourcePruningEnumerationChildCompletion.Ranges checkEmpty bucket incoming caller before queries ∧
      ∀ r n p h k fragment afterCaller after saved outer waiting,
        SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket incoming caller before queries =
          ((.ok (some [.ok (fragment, after.core)]), afterCaller, saved, outer, waiting), some after) →
        Ranges checkEmpty rest afterCaller after saved

/-- Genuine admitted inputs derive a complete traversal or its first valid rejection. -/
theorem complete_with_fragments
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width) (before : Cached)
    (checkEmpty : Bool) (inputs : List (Node × List Suspended))
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (genuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available beforeCaller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket)
    (ranges : Ranges checkEmpty inputs beforeCaller before memos.query) :
    ∃ (r n p h k : Nat) (fragments : List Fragment) (afterCaller : Caller width)
      (after : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (result : SourcePruningEnumerationChildTraversal.Result width),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationChildTraversal.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) inputs beforeCaller before memos.query = result) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held fragment, before.core.values[held]? = some (.enumerated fragment) →
        EnumerationDriver.Protected held before.core after.core) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
        EnumerationDriver.Protected held before.core after.core) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        (∀ incoming bucket, (incoming, bucket) ∈ inputs → EnumerationReferences.InputsAllowed allowed bucket) →
        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (∀ fragment ∈ fragments, FragmentBound after.core.counter fragment) ∧
      ((result = .complete fragments afterCaller savedQueries after ∧ Safe after.core ∧
          ∀ fragment ∈ fragments, PendingFragment after.core fragment ∧
            ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
              (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
              FragmentAvoid after.core.representatives held fragment) ∨
        ∃ outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) := by
  induction inputs generalizing inventory beforeCaller before roots memos with
  | nil =>
      refine ⟨0, 0, 0, 0, 0, [], beforeCaller, before, memos.query, memos, inventory, roots,
        .complete [] beforeCaller memos.query before, ?_, Post.refl initial, rfl, Nat.le_refl _,
        paths, safe.1, realized, counts, flags, .refl _, ?_, ?_, (fun _ valid _ => valid),
        (fun valid => valid), ?_, .inl ⟨rfl, safe, by simp⟩⟩
      · intros; rfl
      · intro held fragment stored
        exact EnumerationDriver.Protected.refl held before.core (enumerated_root before.core safe held fragment stored).2
      · intro held _ root _
        exact EnumerationDriver.Protected.refl held before.core root
      · simp
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      obtain ⟨available, closed, bounded, pending⟩ := genuine incoming bucket (by simp)
      obtain ⟨r, n, p, h, k, raw, middleCaller, middle, middleQueries, middleMemos, middleInventory,
        middleRoots, outer, waiting, headRun, headPost, headQueries, growth, middlePaths,
        middleStorage, middleRealized, middleCounts, middleFlags, headOrigin, headProtected,
        headReferences, headPending, shape⟩ :=
        SourcePruningEnumerationChildCompletion.complete_with_fragments formulas solver inventory beforeCaller before
          checkEmpty bucket incoming roots memos initial safe paths counts flags realized bounded pending available closed ranges.1
      have protects : ∀ held fragment, before.core.values[held]? = some (.enumerated fragment) →
          EnumerationDriver.Protected held before.core middle.core := by
        intro held fragment stored
        obtain ⟨inside, root⟩ := enumerated_root before.core safe held fragment stored
        exact headProtected held inside root (pending held fragment stored)
      rcases shape with rejected | ⟨fragment, singleton, middleSafe, fragmentBound, fragmentPending, fragmentSeparate⟩
      · subst raw
        refine ⟨r, n, p, h, k, [], middleCaller, middle, middleQueries, middleMemos, middleInventory,
          middleRoots, .stopped [] (.ok (some []), middleCaller, middleQueries, outer, waiting) (some middle),
          ?_, headPost, headQueries, growth, middlePaths, middleStorage, middleRealized, middleCounts,
          middleFlags, headOrigin, protects, ?_, ?_, headPending, ?_, .inr ⟨outer, waiting, rfl⟩⟩
        · intro er en P H ek largeP largeH
          simp only [SourcePruningEnumerationChildTraversal.run, headRun er en P H ek largeP largeH]
        · intro held inside root avoids
          exact headProtected held inside root (avoids incoming bucket (by simp))
        · intro allowed valid allowedInputs
          exact headReferences allowed valid (allowedInputs incoming bucket (by simp))
        · simp
      · have tailGenuine : ∀ value bucket, (value, bucket) ∈ rest →
            Available middleCaller.checked.native.machine.heap value ∧ value.free = [] ∧
            (∀ sc ∈ bucket, sc.var < middle.core.counter) ∧ InputsPending middle.core bucket := by
          intro value retained member
          obtain ⟨childAvailable, childClosed, childBounded, childPending⟩ :=
            genuine value retained (List.mem_cons_of_mem _ member)
          refine ⟨headPost.effects.keeps.available value childAvailable, childClosed,
            fun sc member => Nat.lt_of_lt_of_le (childBounded sc member) growth, ?_⟩
          intro held storedFragment stored
          have old := headOrigin held storedFragment stored
          exact (protects held storedFragment old).avoids retained (childPending held storedFragment old)
        have firstRun := headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
        simp only [Nat.add_zero, singleton] at firstRun
        have tailRanges : Ranges checkEmpty rest middleCaller middle middleMemos.query := by
          rw [headQueries]
          exact ranges.2 r n p h k fragment middleCaller middle middleQueries outer waiting firstRun
        obtain ⟨tailR, tailN, tailP, tailH, tailK, tailFragments, afterCaller, after, savedQueries,
          final, next, afterRoots, tailResult, tailRun, tailPost, querySame, tailGrowth, afterPaths,
          storage, afterRealized, afterCounts, afterFlags, tailOrigin, tailProtected, tailRootsProtected,
          tailReferences, tailPending, tailBounds, tailShape⟩ :=
          ih middleInventory middleCaller middle middleRoots middleMemos headPost.context middleSafe
            middlePaths middleCounts middleFlags middleRealized tailGenuine tailRanges
        let result : SourcePruningEnumerationChildTraversal.Result width := match tailResult with
          | .complete fragments caller queries cache => .complete (fragment :: fragments) caller queries cache
          | .stopped fragments observation candidate => .stopped (fragment :: fragments) observation candidate
        refine ⟨r + tailR, n + tailN, max p tailP, max h tailH, k + tailK,
          fragment :: tailFragments, afterCaller, after, savedQueries, final, next, afterRoots, result,
          ?_, headPost.trans tailPost, querySame, Nat.le_trans growth tailGrowth, afterPaths,
          storage, afterRealized, afterCounts, afterFlags, headOrigin.trans tailOrigin, ?_, ?_, ?_,
          (fun valid => tailPending (headPending valid)), ?_, ?_⟩
        · intro er en P H ek largeP largeH
          have head := headRun (tailR + er) (tailN + en) P H (tailK + ek)
            (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH)
          have tail := tailRun (r + er) (n + en) P H (k + ek)
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
          have headExact : SourcePruningEnumerationChildDispatch.run checkEmpty ((r + tailR) + er)
              ((n + tailN) + en) P H ((k + tailK) + ek) bucket incoming beforeCaller before memos.query =
              ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle) := by
            simpa only [Nat.add_assoc, singleton] using head
          have tailExact : SourcePruningEnumerationChildTraversal.run checkEmpty ((r + tailR) + er)
              ((n + tailN) + en) P H ((k + tailK) + ek) rest middleCaller middle middleQueries = tailResult := by
            simpa only [headQueries, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail
          simp only [SourcePruningEnumerationChildTraversal.run, headExact, tailExact, result]
          cases tailResult <;> rfl
        · intro held storedFragment stored
          have first := protects held storedFragment stored
          have middleStored : middle.core.values[held]? = some (.enumerated storedFragment) := first.value.trans stored
          exact first.trans (tailProtected held storedFragment middleStored)
        · intro held inside root avoids
          have first := headProtected held inside root (avoids incoming bucket (by simp))
          apply first.trans
          apply tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root
          intro value retained member
          exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member))
        · intro allowed valid allowedInputs
          apply tailReferences allowed
            (headReferences allowed valid (allowedInputs incoming bucket (by simp)))
          intro value retained member
          exact allowedInputs value retained (List.mem_cons_of_mem _ member)
        · intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact fragmentBound_mono _ _ tailGrowth _ fragmentBound
          · exact tailBounds child member
        · rcases tailShape with ⟨completed, afterSafe, fragmentHistory⟩ | ⟨outer, waiting, stopped⟩
          · subst tailResult
            refine .inl ⟨rfl, afterSafe, ?_⟩
            intro child member
            rcases List.mem_cons.mp member with rfl | member
            · refine ⟨pendingFragment_preserved middle.core after.core middleSafe afterSafe tailGrowth
                child fragmentBound fragmentPending tailOrigin tailProtected, ?_⟩
              intro held inside root avoids
              have first := headProtected held inside root (avoids incoming bucket (by simp))
              have last := tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root (by
                intro value retained member
                exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member)))
              exact (fragmentAvoid_classes middle.core.representatives after.core.representatives held child
                last.classes).mpr (fragmentSeparate held inside root (avoids incoming bucket (by simp)))
            · obtain ⟨childPending, childSeparate⟩ := fragmentHistory child member
              refine ⟨childPending, ?_⟩
              intro held inside root avoids
              have first := headProtected held inside root (avoids incoming bucket (by simp))
              apply childSeparate held (Nat.lt_of_lt_of_le inside growth) first.root
              intro value retained member
              exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member))
          · subst tailResult
            exact .inr ⟨outer, waiting, rfl⟩

/-- The original completion interface retains its exact declaration type. -/
theorem complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width) (before : Cached)
    (checkEmpty : Bool) (inputs : List (Node × List Suspended))
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (genuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available beforeCaller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket)
    (ranges : Ranges checkEmpty inputs beforeCaller before memos.query) :
    ∃ (r n p h k : Nat) (fragments : List Fragment) (afterCaller : Caller width)
      (after : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (result : SourcePruningEnumerationChildTraversal.Result width),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationChildTraversal.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) inputs beforeCaller before memos.query = result) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held fragment, before.core.values[held]? = some (.enumerated fragment) →
        EnumerationDriver.Protected held before.core after.core) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
        EnumerationDriver.Protected held before.core after.core) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        (∀ incoming bucket, (incoming, bucket) ∈ inputs → EnumerationReferences.InputsAllowed allowed bucket) →
        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (∀ fragment ∈ fragments, FragmentBound after.core.counter fragment) ∧
      ((result = .complete fragments afterCaller savedQueries after ∧ Safe after.core) ∨
        ∃ outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) := by
  obtain ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next, afterRoots, result,
    running, post, queries, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, protects, rootsProtects, references, pendingHistory, bounds, shape⟩ :=
    complete_with_fragments formulas solver inventory beforeCaller before checkEmpty inputs roots memos
      initial safe paths counts flags realized genuine ranges
  refine ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next, afterRoots, result,
    running, post, queries, growth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
    origin, protects, rootsProtects, references, pendingHistory, bounds, ?_⟩
  rcases shape with ⟨completed, afterSafe, _fragments⟩ | stopped
  · exact .inl ⟨completed, afterSafe⟩
  · exact .inr stopped

/-- Enumerated origin and protected old roots retain every separate parent bucket. -/
theorem retained_inputs (before after : EnumerationState.State Symbol Constraint) (scs : List Suspended)
    (pending : InputsPending before scs) (origin : EnumeratedOrigin before after)
    (protects : ∀ held fragment, before.values[held]? = some (.enumerated fragment) →
      EnumerationDriver.Protected held before after) : InputsPending after scs := by
  intro held fragment stored
  have old := origin held fragment stored
  exact (protects held fragment old).avoids scs (pending held fragment old)

end MicroCFTA.SourcePruningEnumerationTraversalCompletion
