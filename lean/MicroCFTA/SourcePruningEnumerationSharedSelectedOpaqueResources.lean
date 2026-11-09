import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationSharedChildResources
import MicroCFTA.SourcePruningEnumerationSharedChildScalarBounds
import MicroCFTA.SourcePruningEnumerationSharedHookCertificates
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage
import MicroCFTA.SourcePruningEnumerationEdgeScalarBounds

/-!
# Resources through actual shared opaque and terminal dispatch

The stored original handle is separate from the prepared value. The actual
shared child producer covers terminal buckets. No ProperState premise is
used. Finalization writes the original target and retains its exact
assignment equation at the same child cache.

The resource theorem derives adequate bounds from current inputs. The
executable still retains failed finalization at smaller bounds. The final
assignment equation does not restore a removed pending native restriction
or assert backward meaning for the whole shared child.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "receiptAdvance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A completed opaque receipt retains its actual child and captured-slot assignment equation. -/
def FinalizationAt (checkEmpty : Bool) (bound target : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries) : Receipt (bits + 2) → Prop
  | .complete fragment reached saved after =>
      ∃ (middle : Cached) (outer : EnumerationState.State Symbol Constraint)
        (waiting : EnumerationWaitingIndex.Waiting),
        (∀ extra, SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          scs value caller before queries =
          ((.ok (some [.ok (fragment, middle.core)]), reached, saved, outer, waiting), some middle)) ∧
        (∀ extra, SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
          (bound + extra) target fragment middle = some after) ∧
        ∀ (language : NodeLanguage Symbol)
          (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
          Satisfies language meaning assignment after.core ↔
            Satisfies language meaning assignment (EnumerationFrame.neutralize target middle.core) ∧
              Fragments.fill assignment fragment = assignment target
  | _ => True

/-- Current resources derive the actual shared receipt and its captured finalization meaning. -/
theorem opaque_complete_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (target handle : Nat) (scs : List Suspended)
    (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid target before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false)
    (bounded : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (scs.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (bound : Nat) (receipt : Receipt (bits + 2)) (reached : Caller (bits + 2))
      (saved : Queries) (final : Memos) (next : Inventory),
      (∀ extra, run checkEmpty
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        target scs value caller before memos.query = some receipt) ∧
      Post formulas solver next caller reached final ∧ final.query = saved ∧
      receiptAdvance receipt = some (reached, saved) ∧
      Admitted target receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
      Fits (advance seed (scs.length + 1)).2 reached.checked ∧
      Heap (fun guard => guard ∈ (advance seed (scs.length + 1)).1) reached.checked.native.machine.heap ∧
      ((∃ fragment after, receipt = .complete fragment reached saved after ∧
          Packet formulas solver next reached final metadata after ∧
          after.core.counter ≤ before.core.counter + 1 ∧
          suspendedBound after.core ≤ suspendedBound before.core + scs.length) ∨
        (∃ after outer waiting, receipt = .stopped []
          (.ok (some []), reached, saved, outer, waiting) (some after) ∧
          after.core.counter ≤ before.core.counter + 1 ∧
          suspendedBound after.core ≤ suspendedBound before.core + scs.length) ∨
        receipt = .rejected caller memos.query before) ∧
      FinalizationAt checkEmpty bound target scs value caller before memos.query receipt := by
  by_cases empty : value = .empty
  · subst value
    refine ⟨0, .rejected caller memos.query before, caller, memos.query, memos, inventory,
      ?_, Post.refl packet.context, rfl, rfl, packet.valid, packet.pending, trivial,
      bounded.mono (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge seed _),
      ?_, Or.inr (Or.inr rfl), trivial⟩
    · intro extra
      simp only [run, ↓reduceIte]
    · intro key edge found
      exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge seed _ (known key edge found)
  · obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
    have bucketBound : ∀ sc ∈ scs, sc.var < before.core.counter :=
      ready.safe.1.values _ (List.mem_of_getElem? stored)
    have avoids := ready.avoids handle scs stored
    have pendingInputs := EnumerationReferences.pending_inputs before.core packet.pending
      target (some handle) scs stored
    obtain ⟨r, n, p, h, k, raw, reached, middle, saved, final, next, afterRoots, outer, waiting,
      childRun, post, query, growth, middlePaths, middleStorage, middleRealized, middleCounts,
      middleFlags, origin, protects, references, pendingHistory, shape, afterFits, afterKnown⟩ :=
      SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.complete_with_fragments_resources seed formulas solver inventory
        caller before checkEmpty scs value roots memos packet.context packet.safe paths counts flags
        realized bucketBound pendingInputs available closed bounded reserved known
    have actualChild := childRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
    simp only [Nat.add_zero] at actualChild
    obtain ⟨counterBound, massBound⟩ :=
      SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observed_scalar_bounds
        checkEmpty r n p h k scs value caller before memos.query middle (congrArg Prod.snd actualChild)
    let childBound := r + n + p + h + k
    have childAt (w : Nat) (large : childBound ≤ w) :
        SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty w w w w w scs value caller before memos.query =
          ((.ok (some raw), reached, saved, outer, waiting), some middle) := by
      have rl : r ≤ w := by dsimp [childBound] at large; omega
      have nl : n ≤ w := by dsimp [childBound] at large; omega
      have pl : p ≤ w := by dsimp [childBound] at large; omega
      have hl : h ≤ w := by dsimp [childBound] at large; omega
      have kl : k ≤ w := by dsimp [childBound] at large; omega
      have actual := childRun (w - r) (w - n) w w (w - k) pl hl
      simpa only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] using actual
    rcases shape with rejected | ⟨fragment, singleton, middleSafe, fragmentBound, fragmentPending, fragmentSeparate⟩
    · subst raw
      refine ⟨childBound, .stopped [] (.ok (some []), reached, saved, outer, waiting) (some middle),
        reached, saved, final, next, ?_, post, query, rfl,
        ⟨afterRoots, middlePaths, middleStorage, middleRealized, middleCounts, middleFlags⟩,
        pendingHistory packet.pending, trivial, afterFits, afterKnown,
        Or.inr (Or.inl ⟨middle, outer, waiting, rfl, counterBound, massBound⟩), trivial⟩
      intro extra
      simp only [run, ite_eq_right empty, childAt (childBound + extra) (by omega)]
      cases value <;> simp_all
    · subst raw
      have frame := protects target ready.inside ready.root avoids
      have middleStored : middle.core.values[target]? = some (.unenumerated (some handle) scs) :=
        frame.value.trans stored
      obtain ⟨finalFuel, after, finalRun, _finalRaw, core, finalStored, _flag, _waiting,
        afterPaths, afterCounts, afterFlags, afterStorage, afterRealized, safeFinish, finalMeaning⟩ :=
        SourcePruningEnumerationFinalize.complete_semantics reached.checked.native.machine.heap middle target fragment
          (.unenumerated (some handle) scs) middleStored afterRoots middlePaths middleCounts middleFlags
          middleStorage fragmentBound middleRealized
      have afterSafe := safeFinish middleSafe frame.root
      have separate := fragmentSeparate target ready.inside ready.root avoids
      have finalPending : PendingFragment after.core fragment := by
        rw [core]
        exact pendingFragment_write middle.core target fragment fragmentPending separate
      have incomingMiddle := SourcePruningEnumerationNativeReferences.incoming_preserved
        before.core middle.core target scs incoming avoids frame.classes references
      have afterPending : EnumerationReferences.PendingReferences after.core := by
        have written := EnumerationReferences.setValue_pending target fragment middle.core
          {middle.core with values := middle.core.values.set target (.enumerated fragment)}
          (pendingHistory packet.pending) incomingMiddle ((EnumerationDriver.modify_success _ _ _).mpr rfl)
        rw [core]
        exact written
      have orders : ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
          ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1) := by
        intro level frontier ordered
        have enumProtects : ∀ held old, before.core.values[held]? = some (.enumerated old) →
            EnumerationDriver.Protected held before.core middle.core := by
          intro held old oldStored
          obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held old oldStored
          exact protects held inside root (pendingInputs held old oldStored)
        obtain ⟨middleLevel, middleOrder⟩ := EnumerationOrder.stratified_preserved before.core middle.core
          middleSafe level frontier ordered origin enumProtects
        obtain ⟨nextLevel, nextOrder⟩ := EnumerationOrder.write_stratified middle.core middleSafe middleLevel
          frontier target middleOrder (some handle) scs middleStored fragment fragmentPending separate
        refine ⟨nextLevel, ?_⟩
        rw [core]
        exact EnumerationOrder.stratified_ancestry _ [] nextLevel (frontier + 1) nextOrder
      have finalGrowth : before.core.counter ≤ after.core.counter := by rw [core]; exact growth
      have afterPacket : Packet formulas solver next reached final metadata after := by
        obtain ⟨level, frontier, ordered⟩ := packet.ordered
        obtain ⟨nextLevel, nextOrder⟩ := orders level frontier ordered
        refine ⟨post.context, afterSafe, afterPending,
          ⟨afterRoots, afterPaths, afterStorage, afterRealized, afterCounts, afterFlags⟩,
          ⟨nextLevel, frontier + 1, nextOrder⟩, ?_⟩
        intro group member entry listed
        exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) finalGrowth
      have finalFragmentBound : FragmentBound after.core.counter fragment := by rw [core]; exact fragmentBound
      have finalRoot : IsRoot after.core.representatives target := by rw [core]; exact frame.root
      have ancestry : after.core.expansionAncestry = [] := by rw [core]
      have finalCounter : after.core.counter ≤ before.core.counter + 1 := by rw [core]; exact counterBound
      have finalMass : suspendedBound after.core ≤ suspendedBound before.core + scs.length := by
        have scalars := SourcePruningEnumerationFinalize.run_scalars reached.checked.native.machine.heap
          finalFuel target fragment middle after (by simpa only [Nat.add_zero] using finalRun 0)
        exact Nat.le_trans scalars.2 massBound
      refine ⟨childBound + finalFuel, .complete fragment reached saved after, reached, saved, final, next,
        ?_, post, query, rfl,
        ⟨afterPacket.valid, afterSafe, finalFragmentBound, finalStored, ancestry, finalRoot⟩,
        afterPending, ⟨finalGrowth, finalPending, orders⟩, afterFits, afterKnown,
        Or.inl ⟨fragment, after, rfl, afterPacket, finalCounter, finalMass⟩, ?_⟩
      · intro extra
        have finished := finalRun (childBound + extra)
        have common : finalFuel + (childBound + extra) = childBound + finalFuel + extra := by omega
        rw [common] at finished
        exact finalized checkEmpty (childBound + finalFuel + extra) (childBound + finalFuel + extra)
          (childBound + finalFuel + extra) (childBound + finalFuel + extra) (childBound + finalFuel + extra)
          target scs value caller reached before middle after memos.query saved fragment middle.core outer waiting
          empty dispatch (childAt _ (by omega)) finished
      · refine ⟨middle, outer, waiting, ?_, ?_, finalMeaning⟩
        · intro extra
          exact childAt _ (by omega)
        · intro extra
          have finished := finalRun (childBound + extra)
          have common : finalFuel + (childBound + extra) = childBound + finalFuel + extra := by omega
          rw [common] at finished
          exact finished

end MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueDispatch
