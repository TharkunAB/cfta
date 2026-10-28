import MicroCFTA.SourcePruningEnumerationPreparedOpaqueResources
import MicroCFTA.SourcePruningEnumerationChildStableNeutral
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage

/-!
# Backward meaning of actual prepared opaque and terminal receipts

Original resources derive the child request ranges. A completed actual
receipt identifies the child cache and captured-slot finalizer. The exact
meaning retains the bucket stored by that actual child branch. Terminal
branches retain the full bucket. Nonterminal boundaries retain no bucket.
The restoration theorem states this retention condition explicitly.
The original stored value remains separate from the prepared value.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
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
private theorem finalized_core_of_run
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel target : Nat)
    (fragment : Fragment) (before after : Cached)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    after.core = {before.core with
      values := before.core.values.set target (.enumerated fragment)
      expansionAncestry := []} := by
  simp only [SourcePruningEnumerationFinalize.run, Option.bind_eq_some_iff] at observed
  obtain ⟨_old, _stored, written⟩ := observed
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff, Option.some.injEq] at written
  obtain ⟨_flag, _classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := written
  subst after
  rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original resources derive the exact backward restrictions of a completed actual diagonal receipt. -/
theorem stable_complete_neutral_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (target handle : Nat) (scs : List Suspended)
    (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false)
    (bounded : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (scs.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    {bound : Nat} {fragment : Fragment} {afterCaller : Caller (bits + 2)}
    {saved : Queries} {after : Cached}
    (observed : ∀ extra, run checkEmpty
      (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
      target scs value caller before memos.query = some (.complete fragment afterCaller saved after)) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
      Satisfies (SourcePruningEnumerationNativeLanguage.handles
        (SourceEqualityPCSGuard.holds formulas solver) ambient afterCaller.checked.native.machine.heap)
        residualMeaning assignment after.core →
      Satisfies (SourcePruningEnumerationNativeLanguage.handles
        (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        residualMeaning assignment (EnumerationFrame.neutralize target before.core) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient value (Fragments.fill assignment fragment) ∧
      (∀ sc ∈ (match (generalizing := false) value with
        | .node _ _ _ _ => scs
        | _ => if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then scs else []),
        Suspended.Holds assignment (Fragments.fill assignment fragment) sc) ∧
      Fragments.fill assignment fragment = assignment target := by
  have nonempty : value ≠ .empty := by
    intro empty
    have actual := observed 0
    simp only [run, empty, ↓reduceIte, Option.some.injEq, reduceCtorEq] at actual
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  have bucketBound : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have avoids := ready.avoids handle scs stored
  have pending := EnumerationReferences.pending_inputs before.core packet.pending
    target (some handle) scs stored
  have ranges := SourcePruningEnumerationChildCompletion.initial_ranges seed formulas solver inventory
    caller before checkEmpty scs value roots memos packet.context packet.safe paths counts bucketBound
    pending realized available closed bounded reserved known
  obtain ⟨r, n, p, h, k, raw, reached, middle, queries, _final, _next, _afterRoots, outer, waiting,
    childRun, _post, _query, _growth, _middlePaths, _middleStorage, _middleRealized, _middleCounts,
    _middleFlags, _origin, protects, _references, _pendingHistory, shape, _afterFits, _afterKnown,
    _counterBound, _massBound⟩ :=
    SourcePruningEnumerationChildCompletion.complete_with_fragments_cache_bounds seed formulas solver inventory
      caller before checkEmpty scs value roots memos packet.context packet.safe paths counts flags
      realized bucketBound pending available closed bounded reserved known
  let childBound := r + n + p + h + k
  have childAt (w : Nat) (large : childBound ≤ w) :
      SourcePruningEnumerationChildDispatch.run checkEmpty w w w w w scs value caller before memos.query =
        ((.ok (some raw), reached, queries, outer, waiting), some middle) := by
    have rl : r ≤ w := by dsimp [childBound] at large; omega
    have nl : n ≤ w := by dsimp [childBound] at large; omega
    have pl : p ≤ w := by dsimp [childBound] at large; omega
    have hl : h ≤ w := by dsimp [childBound] at large; omega
    have kl : k ≤ w := by dsimp [childBound] at large; omega
    have actual := childRun (w - r) (w - n) w w (w - k) pl hl
    simpa only [Nat.add_sub_of_le rl, Nat.add_sub_of_le nl, Nat.add_sub_of_le kl] using actual
  rcases shape with rejected | ⟨produced, singleton, _middleSafe, _fragmentBound,
    _fragmentPending, _fragmentSeparate⟩
  · subst raw
    have actual := observed childBound
    have child := childAt (bound + childBound) (by omega)
    cases value <;> simp_all [run]
  · subst raw
    have actual := observed childBound
    have child := childAt (bound + childBound) (by omega)
    have finishingObserved :
        (SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
          (bound + childBound) target produced middle).map
          (fun finished => SourcePruningEnumerationSelectedEdge.Result.complete produced reached queries finished) =
          some (.complete fragment afterCaller saved after) := by
      cases value with
      | empty => exact (nonempty rfl).elim
      | reference name | union entry members depth free | mu entry members depth free =>
          simpa only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte, child] using actual
      | node entry edges depth free =>
          have terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
            change (!(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))) = false at dispatch
            cases decision : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
            | false => rw [decision] at dispatch; cases dispatch
            | true => rfl
          simpa only [run, reduceCtorEq, terminal, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, child] using actual
    obtain ⟨finished, finishing, same⟩ := Option.map_eq_some_iff.mp finishingObserved
    obtain ⟨fragmentSame, callerSame, querySame, afterSame⟩ :=
      SourcePruningEnumerationSelectedEdge.Result.complete.inj same
    subst fragment afterCaller saved after
    have frame := protects target ready.inside ready.root avoids
    have currentStored : middle.core.values[target]? = some (.unenumerated (some handle) scs) :=
      frame.value.trans stored
    have written := finalized_core_of_run reached.checked.native.machine.heap
      (bound + childBound) target produced middle finished finishing
    intro ambient residualMeaning assignment satisfied
    obtain ⟨neutralMiddle, equation⟩ :=
      (SourcePruningEnumerationFinalize.written_semantics middle.core finished.core target produced
        (List.getElem?_eq_some_iff.mp currentStored).1 written
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient reached.checked.native.machine.heap) residualMeaning assignment).mp satisfied
    have childMeaning := SourcePruningEnumerationChildCompletion.stable_neutral_semantics
      formulas solver inventory caller before checkEmpty scs value roots memos packet.context packet.safe paths
      counts flags realized bucketBound pending available closed ranges childRun target ready.inside avoids
      ambient residualMeaning assignment produced middle.core (by simp)
    obtain ⟨neutralBefore, accepted, suspended⟩ := childMeaning.mp neutralMiddle
    exact ⟨neutralBefore, accepted, suspended, equation⟩

/-- A retained actual bucket restores its original source value without an output-model admission premise. -/
theorem stable_complete_sound_retained_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (target handle : Nat) (scs : List Suspended)
    (sourceValue value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some sourceValue)
    (preparedMeaning : ∀ ambient term,
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient value term ↔
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient sourceValue term)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
      | _ => false) = false)
    (bounded : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (scs.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (retained : (match (generalizing := false) value with | .node _ _ _ _ => True | _ => False) ∨
      scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ scs = [])
    {bound : Nat} {fragment : Fragment} {afterCaller : Caller (bits + 2)}
    {saved : Queries} {after : Cached}
    (observed : ∀ extra, run checkEmpty
      (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
      target scs value caller before memos.query = some (.complete fragment afterCaller saved after)) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
      Satisfies (SourcePruningEnumerationNativeLanguage.handles
        (SourceEqualityPCSGuard.holds formulas solver) ambient afterCaller.checked.native.machine.heap)
        residualMeaning assignment after.core →
      Satisfies (SourcePruningEnumerationNativeLanguage.handles
        (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        residualMeaning assignment before.core ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient value (assignment target) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient sourceValue (assignment target) ∧
      (∀ sc ∈ scs, Suspended.Holds assignment (assignment target) sc) ∧
      Fragments.fill assignment fragment = assignment target := by
  have semantic := stable_complete_neutral_resources seed formulas solver inventory caller memos metadata
    before checkEmpty target handle scs value packet ready stored available closed dispatch bounded reserved known observed
  have effectiveSame : (match (generalizing := false) value with
      | .node _ _ _ _ => scs
      | _ => if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then scs else []) = scs := by
    rcases retained with ordinary | terminal | emptyBucket
    · cases value with
      | empty => exact ordinary.elim
      | reference name => exact ordinary.elim
      | node entry edges depth free => rfl
      | union entry members depth free => exact ordinary.elim
      | mu entry members depth free => exact ordinary.elim
    · cases value <;> simp only [terminal, ↓reduceIte]
    · subst scs
      cases value <;> rfl
  intro ambient residualMeaning assignment satisfied
  obtain ⟨neutralBefore, accepted, suspended, equation⟩ := semantic ambient residualMeaning assignment satisfied
  rw [effectiveSame] at suspended
  have sourceAccepted := (preparedMeaning ambient (Fragments.fill assignment fragment)).mp accepted
  have oldSlot : Fragments.slotSatisfies assignment target
      (heap (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap) before.core.values target) := by
    simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies, List.forall_mem_map]
    constructor
    · rw [← equation]
      exact (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mpr sourceAccepted
    · intro sc member
      rw [← equation]
      exact suspended sc member
  have original := EnumerationFrame.neutralize_restore
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap) residualMeaning assignment target before.core neutralBefore oldSlot
  exact ⟨original, by simpa only [equation] using accepted,
    by simpa only [equation] using sourceAccepted,
    by simpa only [equation] using suspended, equation⟩

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
