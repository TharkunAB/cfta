import MicroCFTA.SourcePruningEnumerationNativeBranchResources
import MicroCFTA.SourcePruningEnumerationCapturedEdgeCoverage
import MicroCFTA.SourcePruningEnumerationSelectedEdgeAdmission

/-!
# Constructive coverage of one actual native alternative

The original stored model supplies each inherited restriction.
Selected-edge acceptance excludes unsupported projection and arity rejection.
The supported branch constructs the actual captured completion.
The full original head resource packet remains available.
Operational bounds precede the universal semantic observer.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationNativeBranches (advance)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Result" => SourcePruningEnumerationNativeBranches.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
variable {bits : Nat}

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An accepted captured assignment value constructs this actual native head receipt. -/
theorem head_complete_resources_accepting
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core) (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (edgeCost scs before.core.counter edge))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (r n p h k : Nat) (receipt : Receipt (bits + 2)) (afterCaller : Caller (bits + 2)) (saved : Queries)
      (final : Memos) (next : Inventory),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationCapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs edge caller before memos.query = some receipt) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧ Admitted uv receipt ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        Pending receipt) ∧
      FragmentHistory before.core receipt ∧
      (advance receipt = some (afterCaller, saved) ∨
        receipt = .unhandled ∧ arityAllows edge.children.length scs = true ∧
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = none) ∧
      Fits (reservationAdvance seed (edgeCost scs before.core.counter edge)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (reservationAdvance seed (edgeCost scs before.core.counter edge)).1)
        afterCaller.checked.native.machine.heap ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment uv) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragments.Fragment Symbol) (afterCache : Cached),
          (∀ old < before.core.counter, extended old = assignment old) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          receipt = .complete fragment afterCaller saved afterCache ∧
          Fragments.fill extended fragment = assignment uv ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended afterCache.core := by
  have acceptedChecks : ∀ (ambient : InternedGuardedLanguage.Env Symbol)
      (assignment : Nat → Language.Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core →
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (assignment uv) →
      arityAllows edge.children.length scs = true ∧
        ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) := by
    intro ambient assignment satisfied accepted
    obtain ⟨value, lookup, available, _closed⟩ := realized uv handle scs stored
    have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
    subst value
    have slotModel := satisfied.1.2 uv
    simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
      List.forall_mem_map] at slotModel
    obtain ⟨tries, residual, _terms, projected, _valid, _termShape, _children,
      _length, allowed, _ownEqualities, _residualHolds⟩ :=
      SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory caller memos
        parentEntry edges depth free edge scs initial available selected ambient assignment
        (assignment uv) accepted slotModel.2
    exact ⟨allowed, tries, residual, projected⟩
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        have noCost : edgeCost scs before.core.counter edge = 0 := by
          simp only [edgeCost, allowed, ↓reduceIte, projected]
        refine ⟨0, 0, 0, 0, 0, .unhandled, caller, memos.query, memos, inventory,
          ?_, Post.refl initial, rfl, trivial, (fun _ _ => trivial), trivial, .inr ⟨rfl, allowed, rfl⟩,
          ?_, ?_, ?_⟩
        · intro er en P H ek _largeP _largeH
          rw [SourcePruningEnumerationCapturedEdge.run,
            SourcePruningEnumerationSelectedEdge.unsupported checkEmpty _ _ _ _ _ scs edge caller before memos.query
              allowed projected]
        · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using fits
        · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using known
        · intro ambient assignment satisfied accepted
          obtain ⟨_allowed, tries, residual, actualProjected⟩ :=
            acceptedChecks ambient assignment satisfied accepted
          rw [projected] at actualProjected
          cases actualProjected
    | some pair =>
        rcases pair with ⟨tries, residual⟩
        have actualCost : edgeCost scs before.core.counter edge =
            SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries := by
          simp only [edgeCost, allowed, ↓reduceIte, projected]
        have actualReserved : Reserved bits seed
            (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
          simpa only [actualCost] using reserved
        obtain ⟨r, n, p, h, k, afterCaller, after, saved, final, next, afterRoots, result,
          stable, post, querySame, growth, afterPaths, storage, afterRealized, afterCounts,
          afterFlags, _origin, _retained, _protects, pendingHistory, shape, returnedFits, returnedKnown, accepting⟩ :=
          SourcePruningEnumerationCapturedEdge.complete_with_history_resources_accepting seed formulas solver inventory caller before checkEmpty
            uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized
            selected paths counts flags pending allowed tries residual projected fits actualReserved known
        have valid : CacheValid afterCaller after :=
          ⟨afterRoots, afterPaths, storage, afterRealized, afterCounts, afterFlags⟩
        have headFits : Fits (reservationAdvance seed (edgeCost scs before.core.counter edge)).2 afterCaller.checked := by
          simpa only [actualCost] using returnedFits
        have headKnown : Heap (fun guard => guard ∈
            (reservationAdvance seed (edgeCost scs before.core.counter edge)).1)
            afterCaller.checked.native.machine.heap := by
          simpa only [actualCost] using returnedKnown
        rcases shape with ⟨fragment, completed, safe, bounded, written, ancestry, root, fragmentPending, ordered⟩ |
          ⟨fragments, outer, waiting, stopped⟩
        · subst result
          refine ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            ⟨valid, safe, bounded, written, ancestry, root⟩, pendingHistory, ⟨growth, fragmentPending, ordered⟩,
            .inl rfl, headFits, headKnown, ?_⟩
          intro ambient assignment satisfied accepted
          obtain ⟨extended, produced, agree, originalSatisfied, completed, filled, afterSatisfied⟩ :=
            accepting ambient assignment satisfied accepted
          exact ⟨extended, produced, after, agree, originalSatisfied, completed, filled, afterSatisfied⟩
        · subst result
          refine ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            valid, pendingHistory, trivial, .inl rfl, headFits, headKnown, ?_⟩
          intro ambient assignment satisfied accepted
          obtain ⟨extended, produced, _agree, _originalSatisfied, impossible, _filled, _afterSatisfied⟩ :=
            accepting ambient assignment satisfied accepted
          cases impossible
  · have rejected : arityAllows edge.children.length scs = false := by
      cases value : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed value).elim
    have noCost : edgeCost scs before.core.counter edge = 0 := by
      simp only [edgeCost, rejected, Bool.false_eq_true, ↓reduceIte]
    refine ⟨0, 0, 0, 0, 0, .rejected caller memos.query before, caller, memos.query, memos, inventory,
      ?_, Post.refl initial, rfl, ⟨roots, paths, ready.safe.1, realized, counts, flags⟩,
      (fun history _ => history), trivial, .inl rfl, ?_, ?_, ?_⟩
    · intro er en P H ek _largeP _largeH
      rw [SourcePruningEnumerationCapturedEdge.run,
        SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty _ _ _ _ _ scs edge caller before memos.query rejected]
    · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using fits
    · simpa only [noCost, SourcePruningEnumerationIncomingReservation.advance] using known
    · intro ambient assignment satisfied accepted
      obtain ⟨actualAllowed, _tries, _residual, _projected⟩ :=
        acceptedChecks ambient assignment satisfied accepted
      exact (allowed actualAllowed).elim

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
