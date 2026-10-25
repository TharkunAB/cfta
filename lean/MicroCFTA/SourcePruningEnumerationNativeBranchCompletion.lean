import MicroCFTA.SourcePruningEnumerationNativeBranches
import MicroCFTA.SourcePruningEnumerationNativeGrowth

namespace MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationNativeBranches (advance)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Result" => SourcePruningEnumerationNativeBranches.Result
variable {width : Nat}

/-- Each branch retains its own native cache invariants at its reached caller. -/
def CacheValid (caller : Caller width) (after : Cached) : Prop :=
  ∃ roots, Roots after.core.representatives roots ∧ StorageValid after.core ∧
    PendingRealized caller.checked.native.machine.heap after.core ∧
    EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
    ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)

/-- Successful receipts retain safe finalization; valid rejection retains its actual indexed cache. -/
def Admitted (target : Nat) : Receipt width → Prop
  | .complete fragment caller _ after =>
      CacheValid caller after ∧ Safe after.core ∧ FragmentBound after.core.counter fragment ∧
      after.core.values[target]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
      IsRoot after.core.representatives target
  | .rejected caller _ after => CacheValid caller after
  | .stopped _ (.ok (some []), caller, _, _outer, _waiting) (some after) => CacheValid caller after
  | .unhandled => True
  | _ => False

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Numeric suffix admission follows actual continuations with the original enumeration cache. -/
def Ranges (checkEmpty : Bool) (target : Nat) (scs : List Suspended) (before : Cached) :
    List (EdgeValue Symbol Constraint) → Caller width → Queries → Prop
  | [], _, _ => True
  | edge :: rest, caller, queries =>
      SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before queries ∧
      ∀ r n p h k receipt afterCaller saved,
        SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
          some receipt →
        advance receipt = some (afterCaller, saved) → Ranges checkEmpty target scs before rest afterCaller saved

private theorem head_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
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
    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query) :
    ∃ (r n p h k : Nat) (receipt : Receipt width) (afterCaller : Caller width) (saved : Queries)
      (final : Memos) (next : Inventory),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationCapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs edge caller before memos.query = some receipt) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧ Admitted uv receipt ∧
      (advance receipt = some (afterCaller, saved) ∨
        receipt = .unhandled ∧ arityAllows edge.children.length scs = true ∧
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = none) := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        refine ⟨0, 0, 0, 0, 0, .unhandled, caller, memos.query, memos, inventory,
          ?_, Post.refl initial, rfl, trivial, .inr ⟨rfl, allowed, rfl⟩⟩
        intro er en P H ek _largeP _largeH
        rw [SourcePruningEnumerationCapturedEdge.run,
          SourcePruningEnumerationSelectedEdge.unsupported checkEmpty _ _ _ _ _ scs edge caller before memos.query
            allowed projected]
    | some pair =>
        rcases pair with ⟨tries, residual⟩
        obtain ⟨r, n, p, h, k, afterCaller, after, saved, final, next, afterRoots, result,
          stable, post, querySame, _growth, afterPaths, storage, afterRealized, afterCounts,
          afterFlags, _origin, _retained, _protects, shape⟩ :=
          SourcePruningEnumerationCapturedEdge.complete formulas solver inventory caller before checkEmpty
            uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded realized
            selected paths counts flags pending allowed tries residual projected ranges
        have valid : CacheValid afterCaller after :=
          ⟨afterRoots, afterPaths, storage, afterRealized, afterCounts, afterFlags⟩
        rcases shape with ⟨fragment, completed, safe, bounded, written, ancestry, root⟩ |
          ⟨fragments, outer, waiting, stopped⟩
        · subst result
          exact ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame,
            ⟨valid, safe, bounded, written, ancestry, root⟩, .inl rfl⟩
        · subst result
          exact ⟨r, n, p, h, k, _, afterCaller, saved, final, next, stable, post, querySame, valid, .inl rfl⟩
  · have rejected : arityAllows edge.children.length scs = false := by
      cases value : arityAllows edge.children.length scs with
      | false => rfl
      | true => exact (allowed value).elim
    refine ⟨0, 0, 0, 0, 0, .rejected caller memos.query before, caller, memos.query, memos, inventory,
      ?_, Post.refl initial, rfl, ⟨roots, paths, ready.safe.1, realized, counts, flags⟩, .inl rfl⟩
    intro er en P H ek _largeP _largeH
    rw [SourcePruningEnumerationCapturedEdge.run,
      SourcePruningEnumerationSelectedEdge.arity_rejected checkEmpty _ _ _ _ _ scs edge caller before memos.query rejected]

/-- Genuine alternatives derive one serial scan, stopping only at unsupported preparation. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (ranges : Ranges checkEmpty uv scs before selectedEdges caller memos.query) :
    ∃ (r n p h k : Nat) (processed : List (Receipt width)) (afterCaller : Caller width) (saved : Queries)
      (final : Memos) (next : Inventory) (result : Result width),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationNativeBranches.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧
      (∀ receipt ∈ processed, Admitted uv receipt) ∧
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) := by
  induction selectedEdges generalizing inventory caller memos with
  | nil =>
      exact ⟨0, 0, 0, 0, 0, [], caller, memos.query, memos, inventory, .complete [] caller memos.query,
        fun _ _ _ _ _ _ _ => rfl, Post.refl initial, rfl, by simp, .inl rfl, fun _ => rfl⟩
  | cons edge rest ih =>
      obtain ⟨r, n, p, h, k, receipt, middleCaller, middleQueries, middleMemos, middleInventory,
        headRun, headPost, headQueries, admitted, shape⟩ :=
        head_complete formulas solver inventory caller before checkEmpty uv handle scs parentEntry storedEdges depth free
          edge roots memos initial ready stored decoded realized (selected edge (by simp)) paths counts flags pending ranges.1
      rcases shape with continued | ⟨unhandled, allowed, projected⟩
      · have kept := headPost.effects.keeps
        have middleRealized : PendingRealized middleCaller.checked.native.machine.heap before.core :=
          realized_preserved _ _ before.core before.core realized (EnumerationCompressionFrame.Frame.refl _) kept
        have middleFlags := SourcePruningEnumerationNativeGrowth.flags _ _ kept before flags
        have tailRanges : Ranges checkEmpty uv scs before rest middleCaller middleMemos.query := by
          rw [headQueries]
          apply ranges.2 r n p h k receipt middleCaller middleQueries
          · simpa only [Nat.add_zero] using headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
          · exact continued
        obtain ⟨tr, tn, tp, th, tk, processed, afterCaller, saved, final, next, tailResult,
          tailRun, tailPost, querySame, admittedTail, tailShape, tailSupported⟩ :=
          ih middleInventory middleCaller middleMemos headPost.context
            (lookupNode_keeps _ _ kept handle _ decoded) middleRealized
            (fun chosen member => selected chosen (List.mem_cons_of_mem _ member)) middleFlags tailRanges
        let result : Result width := match (generalizing := false) tailResult with
          | .complete receipts afterCaller saved => .complete (receipt :: receipts) afterCaller saved
          | .stopped receipts current => .stopped (receipt :: receipts) current
        refine ⟨r + tr, n + tn, max p tp, max h th, k + tk, receipt :: processed,
          afterCaller, saved, final, next, result, ?_, headPost.trans tailPost, querySame, ?_, ?_, ?_⟩
        · intro er en P H ek largeP largeH
          have first := headRun (tr + er) (tn + en) P H (tk + ek)
            (Nat.le_trans (Nat.le_max_left _ _) largeP) (Nat.le_trans (Nat.le_max_left _ _) largeH)
          have last := tailRun (r + er) (n + en) P H (k + ek)
            (Nat.le_trans (Nat.le_max_right _ _) largeP) (Nat.le_trans (Nat.le_max_right _ _) largeH)
          have later : SourcePruningEnumerationNativeBranches.run checkEmpty (r + tr + er) (n + tn + en) P H
              (k + tk + ek) uv scs before rest middleCaller middleMemos.query = tailResult := by
            simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using last
          rw [headQueries] at later
          simp only [Nat.add_assoc] at later
          simp only [SourcePruningEnumerationNativeBranches.run, Nat.add_assoc, first, continued, later]
          rfl
        · intro current member
          rcases List.mem_cons.mp member with same | member
          · simpa only [same] using admitted
          · exact admittedTail current member
        · rcases tailShape with completed | stopped
          · exact .inl (by simp only [result, completed])
          · exact .inr (by simp only [result, stopped])
        · intro supported
          have finished := tailSupported (fun chosen member fits =>
            supported chosen (List.mem_cons_of_mem _ member) fits)
          simp only [result, finished]
      · subst receipt
        refine ⟨r, n, p, h, k, [], middleCaller, middleQueries, middleMemos, middleInventory,
          .stopped [] (some .unhandled), ?_, headPost, headQueries, by simp, .inr rfl, ?_⟩
        · intro er en P H ek largeP largeH
          simp only [SourcePruningEnumerationNativeBranches.run, headRun er en P H ek largeP largeH, advance]
        · intro supported
          exact (supported edge (by simp) allowed projected).elim

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
