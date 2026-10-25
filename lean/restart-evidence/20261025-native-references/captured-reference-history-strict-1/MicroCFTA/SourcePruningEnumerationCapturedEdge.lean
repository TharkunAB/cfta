import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.SourcePruningEnumerationSelectedEntry
import MicroCFTA.SourcePruningEnumerationFinalize

namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
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
local notation "Result" => SourcePruningEnumerationSelectedEdge.Result
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Finalize each successful selected edge at the original captured raw slot. -/
noncomputable def run (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries) : Option (Result width) :=
  match SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries with
  | .complete fragment afterCaller saved after =>
      (SourcePruningEnumerationFinalize.run afterCaller.checked.native.machine.heap k target fragment after).map
        (fun finished => .complete fragment afterCaller saved finished)
  | result => some result

/-- A stopped child does not reset ancestry or write the captured slot. -/
theorem children_stopped (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (fragments : List Fragment) (observation : SourcePruningEnumerationChildDispatch.Observation width)
    (candidate : Option Cached)
    (stopped : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries =
      .stopped fragments observation candidate) :
    run checkEmpty r n p h k target scs edge caller before queries =
      some (.stopped fragments observation candidate) := by
  rw [run, stopped]

/-- A ready stored ordinary parent derives its exact captured-slot write or child rejection. -/
theorem complete
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
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query) :
    ∃ (r n p h k : Nat) (afterCaller : Caller width) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result width),
      (∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) uv scs edge caller before memos.query = some result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (∀ held fragment, held ≠ uv → after.core.values[held]? = some (.enumerated fragment) →
        before.core.values[held]? = some (.enumerated fragment)) ∧
      InputsPending after.core scs ∧
      (∀ held, held ≠ uv → held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        EnumerationReferences.PendingReferences after.core) ∧
      ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
          Safe after.core ∧ FragmentBound after.core.counter fragment ∧
          after.core.values[uv]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
          IsRoot after.core.representatives uv) ∨
        ∃ fragments outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) := by
  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have avoids := ready.avoids handle scs stored
  obtain ⟨r, n, p, h, k, afterCaller, middle, savedQueries, final, next, afterRoots, edgeResult,
    edgeRun, post, querySame, growth, middlePaths, storage, middleRealized, middleCounts,
    middleFlags, origin, retained, protects, pendingHistory, incomingHistory, shape⟩ :=
    SourcePruningEnumerationSelectedEdge.complete formulas solver inventory caller before checkEmpty
      parentEntry edges depth free edge scs roots memos initial available closed selected ready.safe realized
      paths counts flags bounded pending allowed tries residual projected ranges
  rcases shape with ⟨fragment, completed, middleSafe, fragmentBound⟩ | ⟨fragments, outer, waiting, stopped⟩
  · subst edgeResult
    have frame := protects uv ready.inside ready.root avoids
    have currentStored : middle.core.values[uv]? = some (.unenumerated (some handle) scs) :=
      frame.value.trans stored
    obtain ⟨fuel, after, finishRun, _raw, core, finalStored, _finalFlag, _finalWaiting,
      afterPaths, afterCounts, afterFlags, afterStorage, afterRealized, safeFinish⟩ :=
      SourcePruningEnumerationFinalize.complete afterCaller.checked.native.machine.heap middle uv fragment
        (.unenumerated (some handle) scs) currentStored afterRoots middlePaths middleCounts middleFlags
        storage fragmentBound middleRealized
    have afterSafe := safeFinish middleSafe frame.root
    have afterPending : InputsPending after.core scs := by
      intro held old expanded
      by_cases same : held = uv
      · subst held
        rw [core]
        exact frame.avoids scs avoids
      · rw [core]
        apply retained held old
        rw [core] at expanded
        simpa only [List.getElem?_set_ne (Ne.symm same)] using expanded
    refine ⟨r, n, p, h, k + fuel, afterCaller, after, savedQueries, final, next, afterRoots,
      .complete fragment afterCaller savedQueries after, ?_, post, querySame, ?_, afterPaths,
      afterStorage, afterRealized, afterCounts, afterFlags, ?_, afterPending, ?_, ?_,
      .inl ⟨fragment, rfl, afterSafe, ?_, finalStored, ?_, ?_⟩⟩
    · intro er en P H ek largeP largeH
      have selectedRun := edgeRun er en P H (fuel + ek) largeP largeH
      rw [← Nat.add_assoc] at selectedRun
      simp only [run, selectedRun]
      have finalRun := finishRun (k + ek)
      rw [show fuel + (k + ek) = k + fuel + ek by omega] at finalRun
      rw [finalRun]
      rfl
    · rw [core]
      exact growth
    · intro held old different expanded
      apply origin held old
      rw [core] at expanded
      simpa only [List.getElem?_set_ne (Ne.symm different)] using expanded
    · intro held different inside root separate
      have oldFrame := protects held inside root separate
      apply oldFrame.trans
      refine ⟨?_, ?_, ?_⟩
      · rw [core]
        exact List.getElem?_set_ne (Ne.symm different)
      · rw [core]
        exact oldFrame.root
      · rw [core]
        exact fun _ => Iff.rfl
    · intro history incoming
      have written := EnumerationReferences.setValue_pending uv fragment middle.core
        {middle.core with values := middle.core.values.set uv (.enumerated fragment)}
        (pendingHistory history) (incomingHistory uv ready.inside ready.root avoids incoming)
        ((EnumerationDriver.modify_success _ _ _).mpr rfl)
      rw [core]
      exact written
    · rw [core]
      exact fragmentBound
    · rw [core]
    · rw [core]
      exact frame.root
  · subst edgeResult
    refine ⟨r, n, p, h, k, afterCaller, middle, savedQueries, final, next, afterRoots,
      .stopped fragments (.ok (some []), afterCaller, savedQueries, outer, waiting) (some middle),
      ?_, post, querySame, growth, middlePaths, storage, middleRealized, middleCounts, middleFlags,
      fun held old _ expanded => origin held old expanded, retained,
      fun held _ inside root separate => protects held inside root separate,
      (fun history _ => pendingHistory history),
      .inr ⟨fragments, outer, waiting, rfl⟩⟩
    intro er en P H ek largeP largeH
    rw [run, edgeRun er en P H ek largeP largeH]

end MicroCFTA.SourcePruningEnumerationCapturedEdge
