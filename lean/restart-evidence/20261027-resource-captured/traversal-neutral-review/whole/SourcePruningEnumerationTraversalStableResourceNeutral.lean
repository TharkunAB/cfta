import MicroCFTA.SourcePruningEnumerationTraversalResources
import MicroCFTA.SourcePruningEnumerationChildStableNeutral

/-!
# Neutral assignment language from original traversal resources

Each canonical child supplies its actual cache, caller and full memos.
Original resources admit each reached child. Common bounds identify its suffix.
The child language retains the source boundary's effective suspended bucket.
-/
namespace MicroCFTA.SourcePruningEnumerationTraversalCompletion
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem resource_neutral_complete_tail
    (checkEmpty : Bool) {r n p h k : Nat}
    {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
    {caller middleCaller afterCaller : Caller width} {before middle after : Cached}
    {queries middleQueries savedQueries : Queries} {fragment : Fragment} {fragments : List Fragment}
    {outer : EnumerationState.State Symbol Constraint} {waiting : EnumerationWaitingIndex.Waiting}
    (head : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k
      bucket incoming caller before queries =
      ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle))
    (completed : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
      ((incoming, bucket) :: rest) caller before queries =
      .complete fragments afterCaller savedQueries after) :
    ∃ tailFragments, fragments = fragment :: tailFragments ∧
      SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
        rest middleCaller middle middleQueries =
        .complete tailFragments afterCaller savedQueries after := by
  rw [SourcePruningEnumerationChildTraversal.run, head] at completed
  cases suffix : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
      rest middleCaller middle middleQueries with
  | complete tailFragments finalCaller finalQueries final =>
      have fields : fragments = fragment :: tailFragments ∧ afterCaller = finalCaller ∧
          savedQueries = finalQueries ∧ after = final := by
        simpa only [suffix, SourcePruningEnumerationChildTraversal.Result.complete.injEq] using completed.symm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := fields
      exact ⟨tailFragments, rfl, rfl⟩
  | stopped completedPrefix observation candidate =>
      simp only [suffix] at completed
      cases completed

variable {bits : Nat}

/-- Original resources retain the exact completed traversal language with one payload neutralized. -/
theorem stable_complete_neutral_semantics_resources
    (seed : SourcePruningEnumerationIncomingReservation.Seed)
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
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits seed.2 beforeCaller.checked)
    (reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed (cost inputs))
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1)
      beforeCaller.checked.native.machine.heap)
    {r n p h k : Nat} {fragments : List Fragment} {afterCaller : Caller (bits + 2)}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
      SourcePruningEnumerationChildTraversal.run checkEmpty (r + extraRepresentative) (n + extraNative)
        P H (k + extraIndex) inputs beforeCaller before memos.query =
        .complete fragments afterCaller savedQueries after) :
    ∀ (held : Nat), held < before.core.counter → IsRoot before.core.representatives held →
    (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
    ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held after.core) ↔
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient beforeCaller.checked.native.machine.heap) residualMeaning assignment (EnumerationFrame.neutralize held before.core) ∧
      All₂ (fun input fragment =>
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient input.1 (Fragments.fill assignment fragment) ∧
        ∀ sc ∈ (match input.1 with
          | .node _ _ _ _ => input.2
          | _ => if input.2.any (fun sc => EqualityTrie.isTerminal sc.trie) then input.2 else []),
          Suspended.Holds assignment (Fragments.fill assignment fragment) sc) inputs fragments := by
  induction inputs generalizing seed inventory beforeCaller before roots memos
      r n p h k fragments afterCaller after savedQueries with
  | nil =>
      have actual := observed 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
      simp only [SourcePruningEnumerationChildTraversal.run,
        SourcePruningEnumerationChildTraversal.Result.complete.injEq] at actual
      obtain ⟨rfl, rfl, rfl, rfl⟩ := actual
      intro _held _inside _root _avoids ambient residualMeaning assignment
      constructor
      · intro satisfied
        exact ⟨satisfied, .nil⟩
      · rintro ⟨satisfied, _related⟩
        exact satisfied
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      obtain ⟨available, closed, bounded, pending⟩ := genuine incoming bucket (by simp)
      have headReservation : SourcePruningEnumerationIncomingReservation.Reserved bits seed (bucket.length + 1) :=
        reserved.prefix (by change bucket.length + 1 ≤ bucket.length + 1 + cost rest; omega)
      have headRanges := SourcePruningEnumerationChildCompletion.initial_ranges seed formulas solver inventory
        beforeCaller before checkEmpty bucket incoming roots memos initial safe paths counts bounded pending
        realized available closed fits headReservation known
      obtain ⟨headR, headN, headP, headH, headK, raw, middleCaller, middle,
        middleQueries, middleMemos, middleInventory, middleRoots, outer, waiting,
        headRun, headPost, headQueries, growth, middlePaths, _middleStorage,
        middleRealized, middleCounts, middleFlags, headOrigin, headProtected,
        _headReferences, _headPending, shape, middleFits, middleKnown⟩ :=
        SourcePruningEnumerationChildCompletion.complete_with_fragments_resources seed formulas solver inventory
          beforeCaller before checkEmpty bucket incoming roots memos initial safe paths counts flags realized
          bounded pending available closed fits headReservation known
      rcases shape with rejected |
        ⟨fragment, singleton, middleSafe, _fragmentBound, _fragmentPending, _fragmentSeparate⟩
      · subst raw
        have headCommon : SourcePruningEnumerationChildDispatch.run checkEmpty (r + headR) (n + headN)
            (max p headP) (max h headH) (k + headK) bucket incoming beforeCaller before memos.query =
            ((.ok (some []), middleCaller, middleQueries, outer, waiting), some middle) := by
          simpa only [Nat.add_comm] using headRun r n (max p headP) (max h headH) k
            (Nat.le_max_right _ _) (Nat.le_max_right _ _)
        have impossible := observed headR headN (max p headP) (max h headH) headK
          (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        rw [SourcePruningEnumerationChildTraversal.run, headCommon] at impossible
        cases impossible
      · have headCommon : ∀ er en P H ek, max p headP ≤ P → max h headH ≤ H →
            SourcePruningEnumerationChildDispatch.run checkEmpty ((r + headR) + er) ((n + headN) + en)
              P H ((k + headK) + ek) bucket incoming beforeCaller before memos.query =
              ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle) := by
          intro er en P H ek enoughP enoughH
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, singleton] using
            headRun (r + er) (n + en) P H (k + ek)
              (Nat.le_trans (Nat.le_max_right _ _) enoughP)
              (Nat.le_trans (Nat.le_max_right _ _) enoughH)
        have firstHead : SourcePruningEnumerationChildDispatch.run checkEmpty (r + headR) (n + headN)
            (max p headP) (max h headH) (k + headK) bucket incoming beforeCaller before memos.query =
            ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle) := by
          simpa only [Nat.add_zero] using headCommon 0 0 (max p headP) (max h headH) 0
            (Nat.le_refl _) (Nat.le_refl _)
        obtain ⟨tailFragments, fragmentShape, _firstTail⟩ := resource_neutral_complete_tail checkEmpty firstHead
          (observed headR headN (max p headP) (max h headH) headK
            (Nat.le_max_left _ _) (Nat.le_max_left _ _))
        have tailRun : ∀ er en P H ek, max p headP ≤ P → max h headH ≤ H →
            SourcePruningEnumerationChildTraversal.run checkEmpty ((r + headR) + er) ((n + headN) + en)
              P H ((k + headK) + ek) rest middleCaller middle middleMemos.query =
              .complete tailFragments afterCaller savedQueries after := by
          intro er en P H ek enoughP enoughH
          have actual : SourcePruningEnumerationChildTraversal.run checkEmpty
              ((r + headR) + er) ((n + headN) + en) P H ((k + headK) + ek)
              ((incoming, bucket) :: rest) beforeCaller before memos.query =
              .complete fragments afterCaller savedQueries after := by
            simpa only [Nat.add_assoc] using observed (headR + er) (headN + en) P H (headK + ek)
              (Nat.le_trans (Nat.le_max_left _ _) enoughP)
              (Nat.le_trans (Nat.le_max_left _ _) enoughH)
          obtain ⟨otherFragments, otherShape, suffix⟩ :=
            resource_neutral_complete_tail checkEmpty (headCommon er en P H ek enoughP enoughH) actual
          have tailsSame : otherFragments = tailFragments :=
            (List.cons.inj (otherShape.symm.trans fragmentShape)).2
          simpa only [tailsSame, ← headQueries] using suffix
        have protects : ∀ held oldFragment, before.core.values[held]? = some (.enumerated oldFragment) →
            EnumerationDriver.Protected held before.core middle.core := by
          intro held oldFragment stored
          obtain ⟨inside, root⟩ := enumerated_root before.core safe held oldFragment stored
          exact headProtected held inside root (pending held oldFragment stored)
        have tailGenuine : ∀ value retained, (value, retained) ∈ rest →
            Available middleCaller.checked.native.machine.heap value ∧ value.free = [] ∧
            (∀ sc ∈ retained, sc.var < middle.core.counter) ∧ InputsPending middle.core retained := by
          intro value retained member
          obtain ⟨childAvailable, childClosed, childBounded, childPending⟩ :=
            genuine value retained (List.mem_cons_of_mem _ member)
          refine ⟨headPost.effects.keeps.available value childAvailable, childClosed,
            fun sc member => Nat.lt_of_lt_of_le (childBounded sc member) growth, ?_⟩
          intro held oldFragment stored
          have old := headOrigin held oldFragment stored
          exact (protects held oldFragment old).avoids retained (childPending held oldFragment old)
        have tailReservation : SourcePruningEnumerationIncomingReservation.Reserved bits
            (SourcePruningEnumerationIncomingReservation.advance seed (bucket.length + 1)) (cost rest) :=
          reserved.after_prefix
        have tailMeaning := ih (SourcePruningEnumerationIncomingReservation.advance seed (bucket.length + 1))
          middleInventory middleCaller middle middleRoots middleMemos headPost.context middleSafe middlePaths
          middleCounts middleFlags middleRealized tailGenuine middleFits tailReservation middleKnown tailRun
        have headMeaning := SourcePruningEnumerationChildCompletion.stable_neutral_semantics
          formulas solver inventory beforeCaller before checkEmpty bucket incoming roots memos
          initial safe paths counts flags realized bounded pending available closed headRanges headRun
        intro held inside root avoids ambient residualMeaning assignment
        have headAvoids := avoids incoming bucket (List.mem_cons_self)
        have frame := headProtected held inside root headAvoids
        rw [fragmentShape]
        have headIff := headMeaning held inside headAvoids ambient residualMeaning assignment fragment middle.core (by
          rw [singleton]
          exact List.mem_singleton_self _)
        have tailIff := tailMeaning held (Nat.lt_of_lt_of_le inside growth) frame.root
          (fun value bucket member => frame.avoids bucket
            (avoids value bucket (List.mem_cons_of_mem _ member))) ambient residualMeaning assignment
        constructor
        · intro satisfied
          obtain ⟨middleSatisfied, related⟩ := tailIff.mp satisfied
          obtain ⟨beforeSatisfied, incomingAccepted, suspended⟩ := headIff.mp middleSatisfied
          exact ⟨beforeSatisfied, .cons ⟨incomingAccepted, suspended⟩ related⟩
        · rintro ⟨beforeSatisfied, related⟩
          cases related with
          | cons headRelation tailRelation =>
              exact tailIff.mpr ⟨headIff.mpr ⟨beforeSatisfied, headRelation.1, headRelation.2⟩, tailRelation⟩

end MicroCFTA.SourcePruningEnumerationTraversalCompletion
