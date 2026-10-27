import MicroCFTA.SourcePruningEnumerationCapturedEdge
import MicroCFTA.SourcePruningEnumerationSelectedEdge
import MicroCFTA.SourcePruningEnumerationSelectedEntry
import MicroCFTA.SourcePruningEnumerationFinalize
import MicroCFTA.EnumerationStratifiedTransport
import MicroCFTA.SourcePruningEnumerationSelectedEdgeNeutralSoundness
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage
import MicroCFTA.SourcePruningEnumerationEntryCanonical

/-!
# Native soundness after actual captured-slot finalization

The actual expansion transports the neutral captured payload.
The final fragment equation restores the original pending restriction.
-/
namespace MicroCFTA.SourcePruningEnumerationCapturedEdge
open EnumerationValidity EnumerationSemantics EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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

/-- Every satisfying actual completed cache restores its original pending language and accepts the captured term. -/
theorem stable_complete_sound_current
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
    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query)
    (canonical : Canonical before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : arityAllows edge.children.length (suspendedVars before.core.counter tries) = true)
    (retained : ∀ incoming bucket,
      (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      (match incoming with | .node _ _ _ _ => True | _ => False) ∨
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [])
    {r n p h k : Nat} {fragment : Fragment} {afterCaller : Caller width}
    {after : Cached} {savedQueries : Queries}
    (observed : ∀ er en P H ek, p ≤ P → h ≤ H →
      run checkEmpty (r + er) (n + en) P H (k + ek) uv scs edge caller before memos.query =
        some (.complete fragment afterCaller savedQueries after)) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment after.core →
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (assignment uv) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry edges depth free) (assignment uv) ∧
      (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
      Fragments.fill assignment fragment = assignment uv := by
  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have inherited : EnumerationSemantics.ValidSuspended scs := canonical _ (List.mem_of_getElem? stored)
  have avoids := ready.avoids handle scs stored
  obtain ⟨r0, n0, p0, h0, k0, reachedCaller, middle, queries0, _final, _next, middleRoots, result,
    edgeRun, _post, _querySame, _growth, middlePaths, middleStorage, middleRealized, middleCounts,
    middleFlags, _origin, _retained, protects, _pendingHistory, _incomingHistory, shape⟩ :=
    SourcePruningEnumerationSelectedEdge.complete_with_fragments formulas solver inventory caller before checkEmpty
      parentEntry edges depth free edge scs roots memos initial available closed selected ready.safe realized
      paths counts flags bounded pending allowed tries residual projected ranges
  rcases shape with ⟨produced, completed, middleSafe, fragmentBound, _fragmentPending, _fragmentSeparate⟩ |
    ⟨fragments, outer, waiting, stopped⟩
  · subst result
    have frame := protects uv ready.inside ready.root avoids
    have currentStored : middle.core.values[uv]? = some (.unenumerated (some handle) scs) :=
      frame.value.trans stored
    obtain ⟨finishFuel, finished, finishRun, _raw, written, _finalStored, _finalFlag, _finalWaiting,
      _afterPaths, _afterCounts, _afterFlags, _afterStorage, _afterRealized, _safeFinish⟩ :=
      SourcePruningEnumerationFinalize.complete reachedCaller.checked.native.machine.heap middle uv produced
        (.unenumerated (some handle) scs) currentStored middleRoots middlePaths middleCounts middleFlags
        middleStorage fragmentBound middleRealized
    have canonicalRun : run checkEmpty (r + r0) (n + n0) (max p p0) (max h h0)
        (k + (k0 + finishFuel)) uv scs edge caller before memos.query =
        some (.complete produced reachedCaller queries0 finished) := by
      have selectedRun : SourcePruningEnumerationSelectedEdge.run checkEmpty
          (r + r0) (n + n0) (max p p0) (max h h0) (k + (k0 + finishFuel))
          scs edge caller before memos.query = .complete produced reachedCaller queries0 middle := by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          edgeRun r n (max p p0) (max h h0) (k + finishFuel)
            (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      rw [run, selectedRun]
      have finishing : SourcePruningEnumerationFinalize.run reachedCaller.checked.native.machine.heap
          (k + (k0 + finishFuel)) uv produced middle = some finished := by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using finishRun (k + k0)
      dsimp only
      rw [finishing]
      rfl
    have actual := observed r0 n0 (max p p0) (max h h0) (k0 + finishFuel)
      (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have fields : fragment = produced ∧ afterCaller = reachedCaller ∧ savedQueries = queries0 ∧ after = finished := by
      simpa only [Option.some.injEq, SourcePruningEnumerationSelectedEdge.Result.complete.injEq] using
        actual.symm.trans canonicalRun
    obtain ⟨rfl, rfl, rfl, rfl⟩ := fields
    have sound := SourcePruningEnumerationSelectedEdge.stable_complete_neutral_sound_current
      formulas solver inventory caller before checkEmpty parentEntry edges depth free edge scs roots memos
      initial available closed selected ready.safe realized paths counts flags bounded pending allowed tries residual
      projected ranges inherited nonterminal freshArity retained edgeRun uv ready.inside ready.root avoids
    intro ambient assignment satisfied
    obtain ⟨neutralMiddle, equation⟩ :=
      (SourcePruningEnumerationFinalize.written_semantics middle.core after.core uv fragment
        (List.getElem?_eq_some_iff.mp currentStored).1 written
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment).mp satisfied
    obtain ⟨neutralBefore, edgeAccepted, parentAccepted, suspended⟩ := sound ambient assignment neutralMiddle
    have oldSlot : Fragments.slotSatisfies assignment uv
        (heap (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap) before.core.values uv) := by
      simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies, List.forall_mem_map]
      constructor
      · rw [← equation]
        exact (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mpr parentAccepted
      · intro sc member
        rw [← equation]
        exact suspended sc member
    have original := EnumerationFrame.neutralize_restore
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
      assignment uv before.core neutralBefore oldSlot
    exact ⟨original, by simpa only [equation] using edgeAccepted,
      by simpa only [equation] using parentAccepted,
      by simpa only [equation] using suspended, equation⟩
  · subst result
    have selectedRun := edgeRun r n (max p p0) (max h h0) k
      (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    have actual := observed r0 n0 (max p p0) (max h h0) k0
      (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have common : run checkEmpty (r + r0) (n + n0) (max p p0) (max h h0)
        (k + k0) uv scs edge caller before memos.query =
        some (.stopped fragments (.ok (some []), reachedCaller, queries0, outer, waiting) (some middle)) := by
      rw [run]
      have exactSelected : SourcePruningEnumerationSelectedEdge.run checkEmpty (r + r0) (n + n0)
          (max p p0) (max h h0) (k + k0) scs edge caller before memos.query =
          .stopped fragments (.ok (some []), reachedCaller, queries0, outer, waiting) (some middle) := by
        simpa only [Nat.add_comm] using selectedRun
      rw [exactSelected]
    rw [common] at actual
    cases actual

end MicroCFTA.SourcePruningEnumerationCapturedEdge
