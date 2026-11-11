import MicroCFTA.SourcePruningEnumerationSharedTraversalResources
import MicroCFTA.SourcePruningEnumerationSharedChildModelResources

/-!
# One original assignment for the actual ordered shared child traversal

Each child supplies the reached caller, cache and extended assignment for the tail.
Every later bucket refers to variables allocated before the original plan started.
Later assignment extension preserves each earlier fragment's completed term.
Compatible current models exclude stopped child results at the returned bounds.
Selected-parent protection remains conditional on the existing avoidance premise.
This shallow traversal does not establish Haskell recursive-child correspondence.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationOrigins
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}

private theorem models_extend
    (holds : Constraint → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment extended : Nat → Language.Term Symbol) (limit : Nat)
    (agree : ∀ uv < limit, extended uv = assignment uv)
    {inputs : List (Node × List Suspended)} {terms : List (Language.Term Symbol)}
    (models : All₂ (fun (input : Node × List Suspended) term => InternedGuardedLanguage.meaning holds ambient input.1 term ∧
      ∀ sc ∈ input.2, Suspended.Holds assignment term sc) inputs terms) :
    (∀ incoming bucket, (incoming, bucket) ∈ inputs → ∀ sc ∈ bucket, sc.var < limit) →
      All₂ (fun (input : Node × List Suspended) term => InternedGuardedLanguage.meaning holds ambient input.1 term ∧
        ∀ sc ∈ input.2, Suspended.Holds extended term sc) inputs terms := by
  induction models with
  | nil => intro _; exact .nil
  | @cons input term inputs terms head _tail ih =>
      intro bounded
      refine .cons ⟨head.1, ?_⟩ (ih ?_)
      · intro sc member path represented
        rw [agree sc.var (bounded input.1 input.2 (by simp) sc member)]
        exact head.2 sc member path represented
      · intro incoming bucket member
        exact bounded incoming bucket (List.mem_cons_of_mem _ member)

/-- Current compatible child terms derive one complete traversal packet and final original assignment. -/
theorem complete_models_origins_resources
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
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Language.Term Symbol → Prop)
    (assignment : Nat → Language.Term Symbol) (whole : Language.Term Symbol)
    (terms : List (Language.Term Symbol))
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment before.core)
    (models : All₂ (fun (input : Node × List Suspended) term =>
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds assignment term sc) inputs terms)
    (old : AssignmentOrigins whole before.core.counter assignment)
    (termOrigins : ∀ term ∈ terms, Origin whole term) :
    ∃ (r n p h k : Nat) (fragments : List Fragment) (afterCaller : Caller (bits + 2))
      (after : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (extended : Nat → Language.Term Symbol),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) inputs beforeCaller before memos.query =
          .complete fragments afterCaller savedQueries after) ∧
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
      Safe after.core ∧
      (∀ fragment ∈ fragments, PendingFragment after.core fragment ∧
        ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
          (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
          FragmentAvoid after.core.representatives held fragment) ∧
      Fits (advance seed (cost inputs)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (cost inputs)).1) afterCaller.checked.native.machine.heap ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning extended before.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap) residualMeaning extended after.core ∧
      fragments.map (Fragments.fill extended) = terms ∧
      AssignmentOrigins whole after.core.counter extended ∧
      All₂ (fun (input : Node × List Suspended) term =>
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds extended term sc) inputs terms := by
  induction inputs generalizing seed inventory beforeCaller before roots memos assignment terms with
  | nil =>
      cases models
      refine ⟨0, 0, 0, 0, 0, [], beforeCaller, before, memos.query, memos, inventory, roots,
        assignment, ?_, Post.refl initial, rfl, Nat.le_refl _, paths, safe.1, realized, counts,
        flags, .refl _, ?_, ?_, (fun _ valid _ => valid), (fun valid => valid), ?_, safe,
        ?_, fits, known, (fun _ _ => rfl), satisfied, satisfied, rfl, old, .nil⟩
      · intros; rfl
      · intro target fragment stored
        exact EnumerationDriver.Protected.refl target before.core
          (enumerated_root before.core safe target fragment stored).2
      · intro target _ root _
        exact EnumerationDriver.Protected.refl target before.core root
      · simp
      · simp
  | cons input rest ih =>
      cases terms with
      | nil => cases models
      | cons chosen laterTerms =>
        cases models with
        | cons headModel tailModels =>
          rcases input with ⟨incoming, bucket⟩
          obtain ⟨accepted, held⟩ := headModel
          obtain ⟨available, closed, bounded, pending⟩ := genuine incoming bucket (by simp)
          obtain ⟨r, n, p, h, k, raw, middleCaller, middle, middleQueries, middleMemos,
            middleInventory, middleRoots, outer, waiting, headResource, middleAssignment,
            modelFragment, headAgree, _headBeforeModel, middleModel, modelSingleton,
            headFilled, middleOrigins, _headHeld⟩ :=
            SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.complete_models_origins_resources
              seed formulas solver inventory beforeCaller before checkEmpty bucket incoming
              roots memos initial safe paths counts flags realized bounded pending available closed
              fits (reserved.prefix (by change bucket.length + 1 ≤ bucket.length + 1 + cost rest; omega))
              known ambient residualMeaning assignment whole chosen satisfied accepted held old
              (termOrigins chosen (by simp))
          rcases headResource with ⟨headRun, headPost, headQueries, growth, middlePaths,
            middleStorage, middleRealized, middleCounts, middleFlags, headOrigin, headProtected,
            headReferences, headPending, shape, middleFits, middleKnown⟩
          have protects : ∀ target fragment, before.core.values[target]? = some (.enumerated fragment) →
              EnumerationDriver.Protected target before.core middle.core := by
            intro target fragment stored
            obtain ⟨inside, root⟩ := enumerated_root before.core safe target fragment stored
            exact headProtected target inside root (pending target fragment stored)
          rcases shape with rejected | ⟨fragment, singleton, middleSafe, fragmentBound,
            fragmentPending, fragmentSeparate⟩
          · rw [modelSingleton] at rejected
            cases rejected
          · have sameFragment : modelFragment = fragment := by
              have pairSame : (modelFragment, middle.core) = (fragment, middle.core) :=
                Except.ok.inj ((List.cons.inj (modelSingleton.symm.trans singleton)).1)
              exact congrArg Prod.fst pairSame
            subst modelFragment
            have tailGenuine : ∀ value retained, (value, retained) ∈ rest →
                Available middleCaller.checked.native.machine.heap value ∧ value.free = [] ∧
                (∀ sc ∈ retained, sc.var < middle.core.counter) ∧ InputsPending middle.core retained := by
              intro value retained member
              obtain ⟨childAvailable, childClosed, childBounded, childPending⟩ :=
                genuine value retained (List.mem_cons_of_mem _ member)
              refine ⟨headPost.effects.keeps.available value childAvailable, childClosed,
                fun sc member => Nat.lt_of_lt_of_le (childBounded sc member) growth, ?_⟩
              exact retained_inputs before.core middle.core retained childPending headOrigin protects
            have tailModelsNow : All₂ (fun (input : Node × List Suspended) term =>
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
                  ambient input.1 term ∧ ∀ sc ∈ input.2, Suspended.Holds middleAssignment term sc)
                rest laterTerms :=
              models_extend (SourceEqualityPCSGuard.holds formulas solver) ambient
                assignment middleAssignment before.core.counter headAgree tailModels
                (fun incoming retained member =>
                  (genuine incoming retained (List.mem_cons_of_mem _ member)).2.2.1)
            have tailReservation : Reserved bits (advance seed (bucket.length + 1)) (cost rest) :=
              reserved.after_prefix
            obtain ⟨tailR, tailN, tailP, tailH, tailK, tailFragments, afterCaller, after,
              savedQueries, final, next, afterRoots, extended, tailRun, tailPost, querySame,
              tailGrowth, afterPaths, storage, afterRealized, afterCounts, afterFlags,
              tailOrigin, tailProtected, tailRootsProtected, tailReferences, tailPending,
              tailBounds, afterSafe, fragmentHistory, tailFits, tailKnown, tailAgree,
              _tailBeforeModel, afterModel, tailFilled, afterOrigins, finalTailModels⟩ :=
              ih (seed := advance seed (bucket.length + 1)) (inventory := middleInventory)
                (beforeCaller := middleCaller) (before := middle) (roots := middleRoots)
                (memos := middleMemos) (assignment := middleAssignment) (terms := laterTerms)
                (initial := headPost.context) (safe := middleSafe) (paths := middlePaths)
                (counts := middleCounts) (flags := middleFlags) (realized := middleRealized)
                (genuine := tailGenuine) (fits := middleFits) (reserved := tailReservation)
                (known := middleKnown) (satisfied := middleModel) (models := tailModelsNow)
                (old := middleOrigins) (termOrigins := fun term member =>
                  termOrigins term (List.mem_cons_of_mem _ member))
            have finalAgree : ∀ uv < before.core.counter, extended uv = assignment uv := by
              intro uv inside
              exact (tailAgree uv (Nat.lt_of_lt_of_le inside growth)).trans (headAgree uv inside)
            have beforeModel : Satisfies
                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                  ambient beforeCaller.checked.native.machine.heap) residualMeaning extended before.core :=
              (state_assignment_congr _ residualMeaning before.core safe.1 extended assignment finalAgree).mpr satisfied
            have finalHeadFill : Fragments.fill extended fragment = chosen :=
              (fill_bounded middle.core.counter extended middleAssignment tailAgree fragment fragmentBound).trans headFilled
            have finalHeld : ∀ sc ∈ bucket, Suspended.Holds extended chosen sc := by
              intro sc member path represented
              rw [finalAgree sc.var (bounded sc member)]
              exact held sc member path represented
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
            refine ⟨r + tailR, n + tailN, max p tailP, max h tailH, k + tailK,
              fragment :: tailFragments, afterCaller, after, savedQueries, final, next,
              afterRoots, extended, ?_, headPost.trans tailPost, querySame,
              Nat.le_trans growth tailGrowth, afterPaths, storage, afterRealized, afterCounts,
              afterFlags, headOrigin.trans tailOrigin, ?_, ?_, ?_,
              (fun valid => tailPending (headPending valid)), ?_, afterSafe, ?_, finalFits,
              finalKnown, finalAgree, beforeModel, afterModel, ?_, afterOrigins,
              .cons ⟨accepted, finalHeld⟩ finalTailModels⟩
            · intro er en P H ek largeP largeH
              have head := headRun (tailR + er) (tailN + en) P H (tailK + ek)
                (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH)
              have tail := tailRun (r + er) (n + en) P H (k + ek)
                (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
              have headExact : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
                  checkEmpty ((r + tailR) + er) ((n + tailN) + en) P H ((k + tailK) + ek)
                  bucket incoming beforeCaller before memos.query =
                  ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle) := by
                simpa only [Nat.add_assoc, singleton] using head
              have tailExact : run checkEmpty ((r + tailR) + er) ((n + tailN) + en) P H ((k + tailK) + ek)
                  rest middleCaller middle middleQueries =
                  .complete tailFragments afterCaller savedQueries after := by
                simpa only [headQueries, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail
              simp only [SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run, headExact, tailExact]
            · intro target storedFragment stored
              have first := protects target storedFragment stored
              have middleStored : middle.core.values[target]? = some (.enumerated storedFragment) :=
                first.value.trans stored
              exact first.trans (tailProtected target storedFragment middleStored)
            · intro target inside root avoids
              have first := headProtected target inside root (avoids incoming bucket (by simp))
              apply first.trans
              apply tailRootsProtected target (Nat.lt_of_lt_of_le inside growth) first.root
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
            · intro child member
              rcases List.mem_cons.mp member with rfl | member
              · refine ⟨pendingFragment_preserved middle.core after.core middleSafe afterSafe tailGrowth
                  child fragmentBound fragmentPending tailOrigin tailProtected, ?_⟩
                intro target inside root avoids
                have first := headProtected target inside root (avoids incoming bucket (by simp))
                have last := tailRootsProtected target (Nat.lt_of_lt_of_le inside growth) first.root (by
                  intro value retained member
                  exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member)))
                exact (fragmentAvoid_classes middle.core.representatives after.core.representatives target child
                  last.classes).mpr (fragmentSeparate target inside root (avoids incoming bucket (by simp)))
              · obtain ⟨childPending, childSeparate⟩ := fragmentHistory child member
                refine ⟨childPending, ?_⟩
                intro target inside root avoids
                have first := headProtected target inside root (avoids incoming bucket (by simp))
                apply childSeparate target (Nat.lt_of_lt_of_le inside growth) first.root
                intro value retained member
                exact first.avoids retained (avoids value retained (List.mem_cons_of_mem _ member))
            · simp only [List.map_cons, finalHeadFill, tailFilled]

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal
