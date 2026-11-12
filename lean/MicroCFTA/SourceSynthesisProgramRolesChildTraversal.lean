import MicroCFTA.SourcePruningEnumerationSharedTraversalResources
import MicroCFTA.SourceSynthesisProgramRolesChildRetained
import MicroCFTA.SourceSynthesisProgramRolesNativeHeap
import MicroCFTA.SourceSynthesisProgramChildScope

/-!
# Program roles through actual ordered shallow children

Each reached child supplies its actual native caller and enumeration cache.
The traversal retains its complete resource receipt and branch marks.
The source row determines Program positions. Type positions remain unrestricted.
This result does not establish eager traversal or whole driver completion.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesChildTraversal
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceSynthesisProgramEnumerationRoles (FragmentRoles SlotRole ProgramSlots)
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "cost" => SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.cost
variable {bits : Nat}

local instance traversalMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem fragment_mono {marked extended : Nat → Prop}
    (included : ∀ uv, marked uv → extended uv) {fragment : Fragment}
    (roles : FragmentRoles literal marked fragment) : FragmentRoles literal extended fragment := by
  induction roles with
  | hole uv known => exact .hole uv (included uv known)
  | component symbol annotation => exact .component symbol annotation
  | application annotation marker function argument _first _second firstIH secondIH =>
      exact .application annotation marker function argument firstIH secondIH
  | filter goal candidates _body ih => exact .filter goal candidates ih

private theorem retained_slots (valid : Constraint → Prop) (marked : Nat → Prop)
    (beforeHeap afterHeap : NativeHeap) (before after : Core)
    (slots : ProgramSlots valid literal beforeHeap before marked)
    (kept : SourceEqualityRequiredCache.Keeps beforeHeap afterHeap) (growth : before.counter ≤ after.counter)
    (protects : ∀ uv, marked uv → EnumerationDriver.Protected uv before after)
    (references : ∀ uv, marked uv → EnumerationReferences.ReferencesAllowed
      (fun target => ¬UnionFind.SameClass before.representatives uv target) after) :
    ProgramSlots valid literal afterHeap after marked := by
  have carried := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots beforeHeap afterHeap before marked kept slots
  refine ⟨fun uv known => Nat.lt_of_lt_of_le (slots.bounded uv known) growth,
    fun uv known => (protects uv known).root, ?_, ?_⟩
  · intro uv known payload member sc listed same
    exact references uv known payload member sc listed (((protects uv known).classes sc.var).mp same)
  · intro uv known
    obtain ⟨payload, stored, role⟩ := carried.stored uv known
    exact ⟨payload, (protects uv known).value.trans stored, role⟩

private theorem program_action
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    {width : Nat} (checkEmpty : Bool) (r n p h k : Nat)
    (bucket : List Suspended) (incoming : Node) (caller reached : Caller width)
    (before after : Cached) (queries saved : Queries) (fragment : Fragment) (outer : Core)
    (waiting : EnumerationWaitingIndex.Waiting)
    (scope : ∀ sc ∈ bucket, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (observed : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty r n p h k
      bucket incoming caller before queries =
      ((.ok (some [.ok (fragment, after.core)]), reached, saved, outer, waiting), some after)) :
    ∃ action : EnumerateM Symbol Constraint Fragment,
      SourcePruningEnumerationShallowChild.prepareChild bucket incoming = some action ∧
      Success action before.core fragment after.core := by
  have noTerminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
    apply List.any_eq_false.mpr
    intro sc member tagged
    have terminal : sc.trie = .terminal := by
      cases trieRead : sc.trie with
      | empty => simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
      | terminal => rfl
      | branch children => simp only [trieRead, EqualityTrie.isTerminal, Bool.false_eq_true] at tagged
    obtain ⟨tail, impossible⟩ := (scope sc member).2 [] ((EqualityTrie.nil_mem sc.trie).mpr terminal)
    cases impossible
  have erased := (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.erase
    checkEmpty r n p h k bucket incoming caller before queries).symm.trans (congrArg Prod.fst observed)
  by_cases empty : incoming = .empty
  · simp [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe, empty] at erased
  · cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
        have noHere : here = [] := by
          have filtered : bucket.filter (fun sc => EqualityTrie.isTerminal sc.trie) = [] :=
            List.filter_eq_nil_iff.mpr (List.any_eq_false.mp noTerminal)
          simpa only [List.partition_eq_filter_filter, filtered] using (congrArg Prod.fst partitioned).symm
        subst here
        simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe,
          ite_eq_right empty, partitioned] at erased
        cases prepared : SourcePruningEnumerationShallowChild.prepareChild bucket incoming with
        | none => simp [prepared] at erased
        | some action =>
            rw [prepared] at erased
            have raw : ExceptT.run (action before.core) = [.ok (fragment, after.core)] :=
              Option.some.inj (Except.ok.inj (congrArg Prod.fst erased))
            exact ⟨action, rfl, by simp only [Success, raw, List.mem_singleton]⟩

private theorem complete_aux
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
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
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (cost inputs))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (valid : Constraint → Prop) (marked : Nat → Prop) (programIndex : Nat → Prop)
    (slots : ProgramSlots valid literal beforeCaller.checked.native.machine.heap before.core marked)
    (childFields : ∀ index incoming bucket, inputs[index]? = some (incoming, bucket) → programIndex index →
      ValueFields valid literal incoming ∧
      ∀ sc ∈ bucket, EqualityTrie.Valid sc.trie ∧
        ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (avoids : ∀ uv, marked uv → ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Avoids before.core.representatives uv bucket) :
    ∃ (r n p h k : Nat) (fragments : List Fragment) (afterCaller : Caller (bits + 2))
      (after : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (result : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.Result (bits + 2)),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run checkEmpty (r + extraRepresentative) (n + extraNative)
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
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      Fits (advance seed (cost inputs)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (cost inputs)).1) afterCaller.checked.native.machine.heap ∧
      ∃ finalMarked : Nat → Prop, (∀ uv, marked uv → finalMarked uv) ∧
        ProgramSlots valid literal afterCaller.checked.native.machine.heap after.core finalMarked ∧
        ∀ index child, programIndex index → fragments[index]? = some child →
          FragmentRoles literal finalMarked child := by
  classical
  induction inputs generalizing seed inventory beforeCaller before roots memos marked programIndex with
  | nil =>
      refine ⟨0, 0, 0, 0, 0, [], beforeCaller, before, memos.query, memos, inventory, roots,
        .complete [] beforeCaller memos.query before, ?_, Post.refl initial, rfl, Nat.le_refl _,
        paths, safe.1, realized, counts, flags, .refl _, ?_, ?_, (fun _ valid _ => valid),
        (fun valid => valid), ?_, .inl ⟨rfl, safe, by simp⟩, fits, known, marked, (fun _ known => known), slots, ?_⟩
      · intros; rfl
      · intro held fragment stored
        exact EnumerationDriver.Protected.refl held before.core (enumerated_root before.core safe held fragment stored).2
      · intro held _ root _
        exact EnumerationDriver.Protected.refl held before.core root
      · simp
      · intro index child _position selected
        cases selected
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      obtain ⟨available, closed, bounded, pending⟩ := genuine incoming bucket (by simp)
      obtain ⟨r, n, p, h, k, raw, middleCaller, middle, middleQueries, middleMemos, middleInventory,
        middleRoots, outer, waiting, headRun, headPost, headQueries, growth, middlePaths,
        middleStorage, middleRealized, middleCounts, middleFlags, headOrigin, headProtected,
        headReferences, headPending, shape, middleFits, middleKnown⟩ :=
        SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.complete_with_fragments_resources seed formulas solver inventory beforeCaller before
          checkEmpty bucket incoming roots memos initial safe paths counts flags realized bounded pending available closed fits
          (reserved.prefix (by change bucket.length + 1 ≤ bucket.length + 1 + cost rest; omega)) known
      have headProtects : ∀ held, marked held → EnumerationDriver.Protected held before.core middle.core := by
        intro held known
        exact headProtected held (slots.bounded held known) (slots.roots held known)
          (avoids held known incoming bucket (by simp))
      have headSlots := retained_slots valid marked beforeCaller.checked.native.machine.heap
        middleCaller.checked.native.machine.heap before.core middle.core slots headPost.effects.keeps growth
        headProtects (by
          intro held known
          exact headReferences (fun target => ¬UnionFind.SameClass before.core.representatives held target)
            (slots.incoming held known) (avoids held known incoming bucket (by simp)))
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
          middleFlags, headOrigin, protects, ?_, ?_, headPending, ?_, .inr ⟨outer, waiting, rfl⟩, ?_, ?_, marked, (fun _ known => known), headSlots, ?_⟩
        · intro er en P H ek largeP largeH
          simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run, headRun er en P H ek largeP largeH]
        · intro held inside root avoids
          exact headProtected held inside root (avoids incoming bucket (by simp))
        · intro allowed valid allowedInputs
          exact headReferences allowed valid (allowedInputs incoming bucket (by simp))
        · simp
        · change Fits (advance seed ((bucket.length + 1) + cost rest)).2 middleCaller.checked
          rw [SourcePruningEnumerationSharedIncomingReservation.advance_add]
          exact middleFits.mono
            (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge (advance seed (bucket.length + 1)) (cost rest))
        · change Heap (fun guard => guard ∈ (advance seed ((bucket.length + 1) + cost rest)).1)
            middleCaller.checked.native.machine.heap
          rw [SourcePruningEnumerationSharedIncomingReservation.advance_add]
          intro key edge found
          exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge
            (advance seed (bucket.length + 1)) (cost rest) (middleKnown key edge found)
        · intro index child _position selected
          cases selected
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
        have headMarks : ∃ middleMarked : Nat → Prop,
            (∀ uv, marked uv → middleMarked uv) ∧
            ProgramSlots valid literal middleCaller.checked.native.machine.heap middle.core middleMarked ∧
            (programIndex 0 → FragmentRoles literal middleMarked fragment) ∧
            ∀ value retained, (value, retained) ∈ rest →
              ∀ uv, middleMarked uv → Avoids middle.core.representatives uv retained := by
          by_cases position : programIndex 0
          · obtain ⟨fields, scope⟩ := childFields 0 incoming bucket rfl position
            have actualHead := headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
            simp only [Nat.add_zero, singleton] at actualHead
            obtain ⟨action, prepared, actual⟩ := program_action checkEmpty r n p h k bucket incoming
              beforeCaller middleCaller before middle memos.query middleQueries fragment outer waiting scope actualHead
            obtain ⟨_handle, receipt, _protects, retained⟩ :=
              SourceSynthesisProgramRolesChildRetained.program_child_retained
                beforeCaller.checked.native.machine.heap incoming bucket
                initial.ready.semantic.ready.semantic.1.normal.facts.coherent available closed fields scope
                before.core middle.core marked safe slots bounded
                (fun uv known => avoids uv known incoming bucket (by simp)) action fragment prepared actual
            obtain ⟨_encoded, _decoded, fragmentSame, _shape, _safe, middleSlots⟩ := receipt
            refine ⟨(fun uv => marked uv ∨ uv = before.core.counter), (fun _ known => Or.inl known),
              SourceSynthesisProgramRolesNativeHeap.keeps_program_slots _ _ _ _ headPost.effects.keeps middleSlots, ?_, ?_⟩
            · intro _position
              rw [fragmentSame]
              exact .hole _ (Or.inr rfl)
            · intro value bucket member uv known
              exact (retained bucket (genuine value bucket (List.mem_cons_of_mem _ member)).2.2.1
                (fun old tagged => avoids old tagged value bucket (List.mem_cons_of_mem _ member))).2 uv known
          · refine ⟨marked, (fun _ known => known), headSlots,
              (fun impossible => (position impossible).elim), ?_⟩
            intro value retained member uv known
            exact (headProtects uv known).avoids retained
              (avoids uv known value retained (List.mem_cons_of_mem _ member))
        obtain ⟨middleMarked, markExtension, middleSlots, headRole, tailAvoids⟩ := headMarks
        have tailFields : ∀ index value retained, rest[index]? = some (value, retained) →
            programIndex (index + 1) → ValueFields valid literal value ∧
            ∀ sc ∈ retained, EqualityTrie.Valid sc.trie ∧
              ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail := by
          intro index value retained selected position
          exact childFields (index + 1) value retained (by simpa using selected) position
        have tailReservation : Reserved bits (advance seed (bucket.length + 1)) (cost rest) :=
          reserved.after_prefix
        obtain ⟨tailR, tailN, tailP, tailH, tailK, tailFragments, afterCaller, after, savedQueries,
          final, next, afterRoots, tailResult, tailRun, tailPost, querySame, tailGrowth, afterPaths,
          storage, afterRealized, afterCounts, afterFlags, tailOrigin, tailProtected, tailRootsProtected,
          tailReferences, tailPending, tailBounds, tailShape, tailFits, tailKnown,
          finalMarked, finalExtension, finalSlots, finalRoles⟩ :=
          ih (advance seed (bucket.length + 1)) middleInventory middleCaller middle middleRoots middleMemos headPost.context middleSafe
            middlePaths middleCounts middleFlags middleRealized tailGenuine middleFits tailReservation middleKnown
            middleMarked (fun index => programIndex (index + 1)) middleSlots tailFields
            (fun uv known value retained member => tailAvoids value retained member uv known)
        have finalFits : Fits (advance seed (cost ((incoming, bucket) :: rest))).2 afterCaller.checked := by
          change Fits (advance seed ((bucket.length + 1) + cost rest)).2 afterCaller.checked
          rw [SourcePruningEnumerationSharedIncomingReservation.advance_add]
          exact tailFits
        have finalKnown : Heap (fun guard => guard ∈ (advance seed (cost ((incoming, bucket) :: rest))).1)
            afterCaller.checked.native.machine.heap := by
          change Heap (fun guard => guard ∈ (advance seed ((bucket.length + 1) + cost rest)).1)
            afterCaller.checked.native.machine.heap
          rw [SourcePruningEnumerationSharedIncomingReservation.advance_add]
          exact tailKnown
        let result : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.Result (bits + 2) := match tailResult with
          | .complete fragments caller queries cache => .complete (fragment :: fragments) caller queries cache
          | .stopped fragments observation candidate => .stopped (fragment :: fragments) observation candidate
        refine ⟨r + tailR, n + tailN, max p tailP, max h tailH, k + tailK,
          fragment :: tailFragments, afterCaller, after, savedQueries, final, next, afterRoots, result,
          ?_, headPost.trans tailPost, querySame, Nat.le_trans growth tailGrowth, afterPaths,
          storage, afterRealized, afterCounts, afterFlags, headOrigin.trans tailOrigin, ?_, ?_, ?_,
          (fun valid => tailPending (headPending valid)), ?_, ?_, finalFits, finalKnown,
          finalMarked, (fun uv known => finalExtension uv (markExtension uv known)), finalSlots, ?_⟩
        · intro er en P H ek largeP largeH
          have head := headRun (tailR + er) (tailN + en) P H (tailK + ek)
            (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH)
          have tail := tailRun (r + er) (n + en) P H (k + ek)
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
          have headExact : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty ((r + tailR) + er)
              ((n + tailN) + en) P H ((k + tailK) + ek) bucket incoming beforeCaller before memos.query =
              ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle) := by
            simpa only [Nat.add_assoc, singleton] using head
          have tailExact : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run checkEmpty ((r + tailR) + er)
              ((n + tailN) + en) P H ((k + tailK) + ek) rest middleCaller middle middleQueries = tailResult := by
            simpa only [headQueries, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail
          simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run, headExact, tailExact, result]
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

        · intro index child position selected
          cases index with
          | zero =>
              have same : fragment = child := Option.some.inj selected
              rw [← same]
              exact fragment_mono finalExtension (headRole position)
          | succ index =>
              exact finalRoles index child (by simpa only [Nat.succ_eq_add_one] using position) selected

/-- The same source row traversal retains its full resources, marks and Program children. -/
theorem complete_with_fragments_resources_program_slots
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
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
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (cost inputs))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal beforeCaller.checked.native.machine.heap before.core marked)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (scs : List Suspended) (start : Nat) (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (actualInputs : inputs = SourcePruningEnumerationEdgeInputs.children edge scs start tries)
    (avoids : ∀ uv, marked uv → ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Avoids before.core.representatives uv bucket) :
    ∃ (r n p h k : Nat) (fragments : List Fragment) (afterCaller : Caller (bits + 2))
      (after : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (result : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.Result (bits + 2)),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run checkEmpty (r + extraRepresentative) (n + extraNative)
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
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      Fits (advance seed (cost inputs)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (cost inputs)).1) afterCaller.checked.native.machine.heap ∧
      ∃ finalMarked : Nat → Prop, (∀ uv, marked uv → finalMarked uv) ∧
        ProgramSlots valid literal afterCaller.checked.native.machine.heap after.core finalMarked ∧
        ∀ index child,
          ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
            (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
          fragments[index]? = some child → FragmentRoles literal finalMarked child := by
  apply complete_aux seed formulas solver inventory beforeCaller before checkEmpty inputs roots memos
    initial safe paths counts flags realized genuine fits reserved known valid marked
    (fun index => (edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
      (edge.entry.key.symbol = literal "filter" ∧ index = 1)) slots ?_ avoids
  intro index incoming bucket selected position
  rw [actualInputs] at selected
  obtain ⟨typed, _inheritedEmpty, _ownBucket, scope⟩ :=
    SourceSynthesisProgramChildScope.program_child_scope valid edge fields scs start inherited tries residual
      projected index incoming bucket selected position
  exact ⟨typed, scope⟩

end MicroCFTA.SourceSynthesisProgramRolesChildTraversal
