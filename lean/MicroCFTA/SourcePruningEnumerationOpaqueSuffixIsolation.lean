import MicroCFTA.SourcePruningEnumerationIsolationReads
import MicroCFTA.SourcePruningEnumerationCreatedIsolation
import MicroCFTA.SourcePruningEnumerationTraversalResources
import MicroCFTA.SourcePruningEnumerationFinalize
import MicroCFTA.SourcePruningEnumerationSelectedEdge

/-!
# Fresh opaque isolation through the actual remaining child suffix

Original pre-allocation bounds separate every remaining input from the fresh root.
The actual opaque preparation supplies the suffix's input cache and native indexes.
The resource producer keeps its whole packet and proves isolation at its own endpoint.
Residual recording and an actual different-slot finalizer retain that same root.
-/
namespace MicroCFTA.EnumerationDischargeHistory
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open EnumerationReferences EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Original bounded inputs cannot name the class of a fresh allocated root. -/
theorem allocated_avoids_bounded
    (before : EnumerationState.State Symbol EnumGuard) (handle : Nat) (safe : Safe before)
    (bucket : List Suspended) (bounded : ∀ sc ∈ bucket, sc.var < before.counter) :
    Avoids (allocated (some handle) before).representatives before.counter bucket := by
  intro sc member same
  change UnionFind.SameClass before.representatives before.counter sc.var at same
  have equal := outside_class before.representatives before.counter before.counter sc.var
    safe.1.forest (Nat.le_refl _) same
  have bound := bounded sc member
  omega

/-- An actual finalizer changes only the captured slot and expansion ancestry. -/
private theorem finalized_core
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (fragment : Fragments.Fragment Symbol)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    after.core = {before.core with
      values := before.core.values.set target (.enumerated fragment)
      expansionAncestry := []} := by
  unfold SourcePruningEnumerationFinalize.run at observed
  dsimp only [EnumerationExpandableIndex.frame] at observed
  cases stored : before.core.values[target]? with
  | none =>
      simp only [stored, Option.bind_none] at observed
      cases observed
  | some old =>
      simp only [stored, Option.bind_some] at observed
      unfold SourcePruningEnumerationNativeIndex.write at observed
      simp only [SourcePruningEnumerationNativeIndex.candidate, Option.bind_some] at observed
      cases counted : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives (-1)
          (references old) before.waiting with
      | none =>
          simp only [counted, Option.bind_none] at observed
          cases observed
      | some waiting =>
          simp only [counted, Option.bind_some, SourcePruningEnumerationNativeIndex.count,
            Option.some.injEq] at observed
          subst after
          rfl

/-- An actual finalizer at a different raw slot retains an isolated root. -/
theorem IsolatedPending.through_finalize
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target held handle : Nat) (fragment : Fragments.Fragment Symbol)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (isolated : IsolatedPending held handle before.core) (different : target ≠ held)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    IsolatedPending held handle after.core := by
  have core := finalized_core heap fuel target fragment before after observed
  refine ⟨?_, ?_, ?_⟩
  · simpa only [core] using isolated.root
  · simpa only [core, List.getElem?_set_ne different] using isolated.stored
  · intro value member sc listed same
    rw [core] at member same
    rcases List.mem_or_eq_of_mem_set member with old | replaced
    · exact isolated.incoming value old sc listed same
    · subst value
      simp [references] at listed

section Resources
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing : Type} {bits : Nat}

/-- Residual recording retains isolation before the same actual parent finalizer. -/
theorem IsolatedPending.through_residual_finalize
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (residual : Option Constraint) (fragment : Fragment) (fuel target held handle : Nat)
    (before after : Cached) (isolated : IsolatedPending held handle before.core)
    (different : target ≠ held)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment
      (SourcePruningEnumerationSelectedEdge.finish residual fragment before) = some after) :
    IsolatedPending held handle after.core := by
  have recorded : IsolatedPending held handle
      (SourcePruningEnumerationSelectedEdge.finish residual fragment before).core :=
    ⟨isolated.root, isolated.stored, isolated.incoming⟩
  exact recorded.through_finalize heap fuel target held handle fragment
    (SourcePruningEnumerationSelectedEdge.finish residual fragment before) after different observed

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original resources preserve a freshly created opaque root through its actual child suffix. -/
theorem opaque_suffix_complete_isolated_resources
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (original prepared : Cached) (value : Node) (bucket : List Suspended) (prepareFuel : Nat)
    (packet : Packet formulas solver inventory caller memos metadata original)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (observed : SourcePruningEnumerationCachedPrepare.prepareChild caller.checked.native.machine.heap
      prepareFuel bucket value original = some [(.hole original.core.counter, prepared)])
    (checkEmpty : Bool) (inputs : List (Node × List Suspended))
    (genuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ bucket, sc.var < original.core.counter) ∧ InputsPending original.core bucket)
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationTraversalCompletion.cost inputs))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (handle r n p h k : Nat) (fragments : List Fragment) (afterCaller : Caller (bits + 2))
      (after : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (result : SourcePruningEnumerationChildTraversal.Result (bits + 2)),
      encodeNode value = some handle ∧ lookupNode caller.checked.native.machine.heap handle = some value ∧
      prepared.core = allocated (some handle) original.core ∧
      ((∀ er en P H ek, p ≤ P → h ≤ H →
          SourcePruningEnumerationChildTraversal.run checkEmpty (r + er) (n + en) P H (k + ek)
            inputs caller prepared memos.query = result) ∧
        Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
        prepared.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
        StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
        EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
        (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
          ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
        EnumeratedOrigin prepared.core after.core ∧
        (∀ held fragment, prepared.core.values[held]? = some (.enumerated fragment) →
          EnumerationDriver.Protected held prepared.core after.core) ∧
        (∀ held, held < prepared.core.counter → IsRoot prepared.core.representatives held →
          (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids prepared.core.representatives held bucket) →
          EnumerationDriver.Protected held prepared.core after.core) ∧
        (∀ allowed, ReferencesAllowed allowed prepared.core →
          (∀ incoming bucket, (incoming, bucket) ∈ inputs → InputsAllowed allowed bucket) →
          ReferencesAllowed allowed after.core) ∧
        (PendingReferences prepared.core → PendingReferences after.core) ∧
        (∀ fragment ∈ fragments, FragmentBound after.core.counter fragment) ∧
        ((result = .complete fragments afterCaller savedQueries after ∧ Safe after.core ∧
            ∀ fragment ∈ fragments, PendingFragment after.core fragment ∧
              ∀ held, held < prepared.core.counter → IsRoot prepared.core.representatives held →
                (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids prepared.core.representatives held bucket) →
                FragmentAvoid after.core.representatives held fragment) ∨
          ∃ outer waiting, result = .stopped fragments
            (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
        Fits (advance seed (SourcePruningEnumerationTraversalCompletion.cost inputs)).2 afterCaller.checked ∧
        Heap (fun guard => guard ∈ (advance seed (SourcePruningEnumerationTraversalCompletion.cost inputs)).1)
          afterCaller.checked.native.machine.heap) ∧
      IsolatedPending original.core.counter handle after.core ∧
      (∀ (residual : Option Constraint) (parentFragment : Fragment) (fuel target : Nat) (finished : Cached),
        target ≠ original.core.counter →
        SourcePruningEnumerationFinalize.run afterCaller.checked.native.machine.heap fuel target parentFragment
          (SourcePruningEnumerationSelectedEdge.finish residual parentFragment after) = some finished →
        IsolatedPending original.core.counter handle finished.core) := by
  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨handle, action, canonical, encoded, decoded, _action, running, _raw, core, _stored,
    _growth, _aligned, _forest, preparedPaths, _storage, preparedRealized, preparedCounts,
    _waiting, _sameFlags, preparedFlags, _holeBound⟩ :=
    SourcePruningEnumerationCachedPrepare.boundary_complete caller.checked.native.machine.heap original
      value bucket roots packet.context.ready.semantic.ready.semantic.1.normal.facts.coherent
      available closed boundary nonterminal storage realized paths counts flags
  have sameRows := Option.some.inj ((running prepareFuel).symm.trans observed)
  have sameCache : canonical = prepared := (Prod.mk.inj (List.cons.inj sameRows).1).2
  subst canonical
  have preparedSafe : Safe prepared.core := by
    rw [core]
    exact ⟨allocation_storage (some handle) original.core packet.safe.1,
      allocation_live (some handle) original.core packet.safe.1 packet.safe.2⟩
  have isolated : IsolatedPending original.core.counter handle prepared.core := by
    rw [core]
    exact allocated_isolated original.core handle packet.safe
  have avoids : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Avoids prepared.core.representatives original.core.counter bucket := by
    intro incoming bucket member
    rw [core]
    exact allocated_avoids_bounded original.core handle packet.safe bucket (genuine incoming bucket member).2.2.1
  have preparedGenuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ bucket, sc.var < prepared.core.counter) ∧ InputsPending prepared.core bucket := by
    intro incoming bucket member
    obtain ⟨inputAvailable, inputClosed, inputBounded, inputPending⟩ := genuine incoming bucket member
    refine ⟨inputAvailable, inputClosed, ?_, ?_⟩
    · intro sc listed
      rw [core]
      exact Nat.lt_succ_of_lt (inputBounded sc listed)
    · intro held fragment stored
      have beforeStored := allocation_origin (some handle) original.core held fragment (by simpa only [core] using stored)
      rw [core]
      exact inputPending held fragment beforeStored
  obtain ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next, afterRoots,
    result, full⟩ := SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources seed
      formulas solver inventory caller prepared checkEmpty inputs roots memos packet.context preparedSafe
      preparedPaths preparedCounts preparedFlags preparedRealized preparedGenuine fits reserved known
  have retained := full
  obtain ⟨_run, _post, _query, _counter, _paths, _storage, _realized, _counts, _flags,
    _origin, _expandedProtected, protects, references, _pending, _bounds, _shape, _fits, _known⟩ := full
  have inside : original.core.counter < prepared.core.counter := by
    rw [core]
    exact Nat.lt_succ_self _
  have protectedRoot := protects original.core.counter inside isolated.root avoids
  have incomingAfter : IncomingAvoid original.core.counter after.core := by
    have allowedAfter := references _ isolated.incoming avoids
    intro value member sc listed same
    exact allowedAfter value member sc listed ((protectedRoot.classes sc.var).mp same)
  have afterIsolated : IsolatedPending original.core.counter handle after.core :=
    ⟨protectedRoot.root, protectedRoot.value.trans isolated.stored, incomingAfter⟩
  refine ⟨handle, r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next,
    afterRoots, result, encoded, decoded, core, retained, afterIsolated, ?_⟩
  intro residual parentFragment fuel target finished different finalized
  exact afterIsolated.through_residual_finalize afterCaller.checked.native.machine.heap residual parentFragment
    fuel target original.core.counter handle after finished different finalized

end Resources
end MicroCFTA.EnumerationDischargeHistory

namespace MicroCFTA.EnumerationDischargeHistory

theorem finalize_core_of_run
    {EnumGuard NativeGuard : Type}
    (heap : InternedConstructorTemplates.State SourcePruningTemplates.Symbol NativeGuard)
    (fuel target : Nat) (fragment : Fragments.Fragment SourcePruningTemplates.Symbol)
    (before after : EnumerationExpandableIndex.Cached SourcePruningTemplates.Symbol EnumGuard)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    after.core = {before.core with
      values := before.core.values.set target (.enumerated fragment)
      expansionAncestry := []} :=
  finalized_core heap fuel target fragment before after observed

end MicroCFTA.EnumerationDischargeHistory

namespace MicroCFTA.EnumerationDischargeHistory
open EnumerationState EnumerationSchedule EnumerationDependencies EnumerationDriver EnumerationCompressionFrame
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard : Type}
set_option autoImplicit false

/-- Old expanded slots remain protected. New expanded fragments avoid the held class. -/
structure HeldFragmentHistory (held handle : Nat) (before after : State Symbol Guard) : Prop where
  isolated : IsolatedPending held handle after
  protectedHeld : Protected held before after
  expanded : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
    before.values[slot]? = some (.enumerated fragment) → Protected slot before after
  origin : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
    after.values[slot]? = some (.enumerated fragment) →
      before.values[slot]? = some (.enumerated fragment) ∨
        FragmentAvoid after.representatives held fragment

/-- An unchanged safe core retains its isolated slot and every old expanded value. -/
theorem HeldFragmentHistory.refl
    (held handle : Nat) (state : State Symbol Guard) (safe : Safe state)
    (isolated : IsolatedPending held handle state) :
    HeldFragmentHistory held handle state state := by
  refine ⟨isolated, Protected.refl held state isolated.root, ?_, ?_⟩
  · intro slot fragment stored
    exact Protected.refl slot state (enumerated_root state safe slot fragment stored).2
  · intro slot fragment stored
    exact Or.inl stored

/-- Consecutive receipts retain old expanded values and transport new-fragment avoidance. -/
theorem HeldFragmentHistory.trans
    (held handle : Nat) (before middle after : State Symbol Guard)
    (first : HeldFragmentHistory held handle before middle)
    (second : HeldFragmentHistory held handle middle after) :
    HeldFragmentHistory held handle before after := by
  refine ⟨second.isolated, first.protectedHeld.trans second.protectedHeld, ?_, ?_⟩
  · intro slot fragment stored
    have middleStored : middle.values[slot]? = some (.enumerated fragment) :=
      (first.expanded slot fragment stored).value.trans stored
    exact (first.expanded slot fragment stored).trans (second.expanded slot fragment middleStored)
  · intro slot fragment stored
    rcases second.origin slot fragment stored with middleStored | separate
    · rcases first.origin slot fragment middleStored with originalStored | middleSeparate
      · exact Or.inl originalStored
      · exact Or.inr ((fragmentAvoid_classes middle.representatives after.representatives
          held fragment second.protectedHeld.classes).mpr middleSeparate)
    · exact Or.inr separate

/-- A complete compression frame retains the concrete fragment-history receipt. -/
theorem HeldFragmentHistory.of_frame
    (held handle : Nat) (before after : State Symbol Guard) (safe : Safe before)
    (isolated : IsolatedPending held handle before) (frame : Frame before after) :
    HeldFragmentHistory held handle before after := by
  have protects : ∀ slot, IsRoot before.representatives slot → Protected slot before after := by
    intro slot root
    refine ⟨congrArg (fun values => values[slot]?) frame.values, ?_, ?_⟩
    · obtain ⟨size, path⟩ := root
      exact ⟨size, (frame.reaches slot slot size).mpr path⟩
    · intro other
      exact SourcePruningEnumerationNativeLanguage.frame_sameClass before after frame slot other
  refine ⟨isolated.through_frame frame, protects held isolated.root, ?_, ?_⟩
  · intro slot fragment stored
    exact protects slot (enumerated_root before safe slot fragment stored).2
  · intro slot fragment stored
    rw [frame.values] at stored
    exact Or.inl stored

end MicroCFTA.EnumerationDischargeHistory

namespace MicroCFTA.EnumerationDischargeHistory
open EnumerationState EnumerationSchedule EnumerationDependencies EnumerationDriver
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard : Type}
set_option autoImplicit false

/-- Every final expansion of an original pending target avoids the retained isolated class. -/
theorem HeldFragmentHistory.pending_target_avoids
    (held handle : Nat) (before after : State Symbol Guard) (safe : Safe before)
    (history : HeldFragmentHistory held handle before after) :
    ∀ (target : Nat) (node : Option Nat) (bucket : List Suspended),
      before.values[target]? = some (.unenumerated node bucket) →
      ∀ (representative : Nat) (fragment : Fragments.Fragment Symbol),
        UnionFind.SameClass after.representatives target representative →
        after.values[representative]? = some (.enumerated fragment) →
        FragmentAvoid after.representatives held fragment := by
  intro target node bucket stored representative fragment aliases expanded
  rcases history.origin representative fragment expanded with original | avoiding
  · have representativeRoot : IsRoot before.representatives representative :=
      (enumerated_root before safe representative fragment original).2
    have targetRoot : IsRoot before.representatives target :=
      (safe.2 target (.unenumerated node bucket) stored).mp (by intro impossible; cases impossible)
    have retained := history.expanded representative fragment original
    have originalAliases : UnionFind.SameClass before.representatives representative target :=
      (retained.classes target).mp (UnionFind.sameClass_symm aliases)
    have same : representative = target :=
      (UnionFind.sameClass_iff_roots representativeRoot.choose_spec targetRoot.choose_spec).mp originalAliases
    rw [same] at original
    cases Option.some.inj (original.symm.trans stored)
  · exact avoiding

end MicroCFTA.EnumerationDischargeHistory

namespace MicroCFTA.SourcePruningEnumerationFinalize
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {NativeGuard : Type}

/-- Residual recording commutes with the same actual raw-slot finalizer. -/
theorem run_after_residual
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (fragment : Fragments.Fragment Symbol)
    (residual : Option Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    run heap fuel target fragment
        (SourcePruningEnumerationSelectedEdge.finish residual fragment before) =
      (run heap fuel target fragment before).map
        (SourcePruningEnumerationSelectedEdge.finish residual fragment)
 := by
  unfold run
  dsimp only [SourcePruningEnumerationSelectedEdge.finish, EnumerationExpandableIndex.frame]
  cases stored : before.core.values[target]? with
  | none => simp only [Option.bind_none, Option.map_none]
  | some old =>
    simp only [Option.bind_some]
    unfold SourcePruningEnumerationNativeIndex.write
    simp only [SourcePruningEnumerationNativeIndex.candidate, Option.bind_some]
    cases counted : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives
        (-1) (EnumerationSchedule.references old) before.waiting with
    | none => simp only [Option.bind_none, Option.map_none]
    | some waiting =>
      cases residual <;>
        simp only [Option.bind_some, SourcePruningEnumerationNativeIndex.count,
          Option.map_some, SourcePruningEnumerationSelectedEdge.finish,
          EnumerationExpandableIndex.frame]

end MicroCFTA.SourcePruningEnumerationFinalize

namespace MicroCFTA.EnumerationDischargeHistory
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Recording a residual retains the structural receipt for the same core values. -/
theorem HeldFragmentHistory.after_residual
    (held handle : Nat) (before : EnumerationState.State Symbol Constraint)
    (middle : EnumerationExpandableIndex.Cached Symbol Constraint)
    (residual : Option Constraint) (fragment : Fragments.Fragment Symbol)
    (history : HeldFragmentHistory held handle before middle.core) :
    HeldFragmentHistory held handle before
      (SourcePruningEnumerationSelectedEdge.finish residual fragment middle).core
 := by
  refine ⟨⟨history.isolated.root, history.isolated.stored, history.isolated.incoming⟩,
    ⟨history.protectedHeld.value, history.protectedHeld.root, history.protectedHeld.classes⟩,
    ?_, ?_⟩
  · intro slot old stored
    have protection :=  history.expanded slot old stored
    exact ⟨protection.value, protection.root, protection.classes⟩
  · intro slot old stored
    exact history.origin slot old stored

end MicroCFTA.EnumerationDischargeHistory

namespace MicroCFTA.EnumerationDischargeHistory
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies EnumerationDriver
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard : Type}
set_option autoImplicit false

/-- A stable read retains old expanded slots and their exact stored fragments. -/
theorem HeldFragmentHistory.of_renderStable
    (held handle : Nat) (before after : State Symbol Guard)
    (isolated : IsolatedPending held handle before)
    (stable : RenderStable before after) :
    HeldFragmentHistory held handle before after
 := by
  have isolatedAfter := isolated.through_renderStable stable
  refine ⟨isolatedAfter, ⟨?_, isolatedAfter.root, stable.classes held⟩, ?_, ?_⟩
  · exact congrArg (fun values => values[held]?) stable.values
  · intro slot fragment stored
    have afterStored : after.values[slot]? = some (.enumerated fragment) := by
      rw [stable.values]
      exact stored
    exact ⟨congrArg (fun values => values[slot]?) stable.values,
      (enumerated_root after stable.safe slot fragment afterStored).2, stable.classes slot⟩
  · intro slot fragment stored
    exact Or.inl (by simpa only [stable.values] using stored)

end MicroCFTA.EnumerationDischargeHistory
