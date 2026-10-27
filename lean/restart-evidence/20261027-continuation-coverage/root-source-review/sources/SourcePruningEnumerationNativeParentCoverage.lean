import MicroCFTA.SourcePruningEnumerationNativeBranchCoverage
import MicroCFTA.SourcePruningEnumerationSelectorLanguage

/-!
# A supported native scan constructs the original parent value

The original satisfying stored model supplies an accepting selected edge.
A permutation selector retains that edge at an actual list index.
Original support for the full selected list excludes unsupported prefixes.
The same complete native scan contains the actual completed chosen receipt.
The chosen branch keeps its own caller, full memo states and final cache.
The complete primary resource packet and its uniform observer remain.
This theorem does not cover earlier recursive continuation stops.
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

/-- An original parent model constructs a completed indexed receipt in the same supported scan. -/
theorem parent_complete_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selectedRows : selectedEdges.Perm storedEdges)
    (supported : ∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (cost scs before.core.counter selectedEdges))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment : Nat → Language.Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
      assignment before.core) :
    ∃ (r n p h k : Nat) (processed : List (Receipt (bits + 2))) (afterCaller : Caller (bits + 2)) (saved : Queries)
      (final : Memos) (next : Inventory) (result : Result (bits + 2)),
      ((∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationNativeBranches.run checkEmpty (r + er) (n + en) P H (k + ek)
          uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = saved ∧
      (∀ receipt ∈ processed, Admitted uv receipt) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        ∀ receipt ∈ processed, Pending receipt) ∧
      (∀ receipt ∈ processed,
        ∃ (reached : Caller (bits + 2)) (savedQueries : Queries) (receiptInventory : Inventory) (receiptMemos : Memos),
          advance receipt = some (reached, savedQueries) ∧
          Post formulas solver receiptInventory caller reached receiptMemos ∧ receiptMemos.query = savedQueries) ∧
      (∀ receipt ∈ processed, FragmentHistory before.core receipt) ∧
      (result = .complete processed afterCaller saved ∨ result = .stopped processed (some .unhandled)) ∧
      ((∀ edge ∈ selectedEdges, arityAllows edge.children.length scs = true →
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none) →
        result = .complete processed afterCaller saved) ∧
      Fits (reservationAdvance seed (cost scs before.core.counter selectedEdges)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (reservationAdvance seed (cost scs before.core.counter selectedEdges)).1)
        afterCaller.checked.native.machine.heap ∧
      (∀ (index : Nat) (receipt : Receipt (bits + 2)), processed[index]? = some receipt →
        ∃ (reached : Caller (bits + 2)) (savedQueries : Queries),
          advance receipt = some (reached, savedQueries) ∧
          Fits (reservationAdvance seed (cost scs before.core.counter (selectedEdges.take (index + 1)))).2
            reached.checked ∧
          Heap (fun guard => guard ∈
            (reservationAdvance seed (cost scs before.core.counter (selectedEdges.take (index + 1)))).1)
            reached.checked.native.machine.heap) ∧
      ∀ (index : Nat) (chosen : EdgeValue Symbol Constraint),
        selectedEdges[index]? = some chosen →
        (∀ earlier ∈ selectedEdges.take index, arityAllows earlier.children.length scs = true →
          SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none) →
        ∀ (ambient : InternedGuardedLanguage.Env Symbol)
          (assignment : Nat → Language.Term Symbol),
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            assignment before.core →
          InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient chosen (assignment uv) →
          ∃ (headCaller : Caller (bits + 2)) (headInventory : Inventory) (headMemos : Memos)
            (branchCaller : Caller (bits + 2)) (branchQueries : Queries) (branchMemos : Memos)
            (branchInventory : Inventory) (afterCache : Cached)
            (extended : Nat → Language.Term Symbol) (fragment : Fragments.Fragment Symbol),
            Post formulas solver headInventory caller headCaller headMemos ∧
            Post formulas solver branchInventory headCaller branchCaller branchMemos ∧
            branchMemos.query = branchQueries ∧
            processed[index]? = some (.complete fragment branchCaller branchQueries afterCache) ∧
            (∀ er en P H ek, p ≤ P → h ≤ H →
              SourcePruningEnumerationCapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
                uv scs chosen headCaller before headMemos.query =
                  some (.complete fragment branchCaller branchQueries afterCache)) ∧
            (∀ old < before.core.counter, extended old = assignment old) ∧
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              extended before.core ∧
            Fragments.fill extended fragment = assignment uv ∧
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient branchCaller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              extended afterCache.core) ∧
      result = .complete processed afterCaller saved ∧
      ∃ (index : Nat) (chosen : EdgeValue Symbol Constraint),
        selectedEdges[index]? = some chosen ∧
          ∃ (headCaller : Caller (bits + 2)) (headInventory : Inventory) (headMemos : Memos)
            (branchCaller : Caller (bits + 2)) (branchQueries : Queries) (branchMemos : Memos)
            (branchInventory : Inventory) (afterCache : Cached)
            (extended : Nat → Language.Term Symbol) (fragment : Fragments.Fragment Symbol),
            Post formulas solver headInventory caller headCaller headMemos ∧
            Post formulas solver branchInventory headCaller branchCaller branchMemos ∧
            branchMemos.query = branchQueries ∧
            processed[index]? = some (.complete fragment branchCaller branchQueries afterCache) ∧
            (∀ er en P H ek, p ≤ P → h ≤ H →
              SourcePruningEnumerationCapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
                uv scs chosen headCaller before headMemos.query =
                  some (.complete fragment branchCaller branchQueries afterCache)) ∧
            (∀ old < before.core.counter, extended old = assignment old) ∧
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              extended before.core ∧
            Fragments.fill extended fragment = assignment uv ∧
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient branchCaller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              extended afterCache.core := by
  obtain ⟨value, lookup, available, _closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry storedEdges depth free :=
    Option.some.inj (lookup.symm.trans decoded)
  subst value
  have model := satisfied.1.2 uv
  simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
    List.forall_mem_map] at model
  have parentAccepted : InternedGuardedLanguage.meaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient
      (.node parentEntry storedEdges depth free) (assignment uv) :=
    (SourcePruningEnumerationNativeLanguage.handles_lookup _ _ _ _ _ _ decoded).mp model.1
  obtain ⟨chosen, offered, _member, _resident, accepted⟩ :=
    SourcePruningEnumerationSelectorLanguage.selected_accepting_of_perm
      caller.checked.native.machine.heap initial.ready.semantic.ready parentEntry storedEdges
      selectedEdges depth free available selectedRows (SourceEqualityPCSGuard.holds formulas solver)
      ambient (assignment uv) parentAccepted
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp offered
  obtain ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result,
    running, post, querySame, admitted, pendingHistory, receiptPosts, fragmentHistory,
    shape, allSupported, returnedFits, returnedKnown, indexedResources, accepting⟩ :=
    complete_with_history_resources_accepting seed formulas solver inventory caller before checkEmpty
      uv handle scs parentEntry storedEdges selectedEdges depth free roots memos initial ready stored
      decoded realized (fun edge member => selectedRows.mem_iff.mp member) paths counts flags pending
      fits reserved known
  have prefixSupported : ∀ earlier ∈ selectedEdges.take index,
      arityAllows earlier.children.length scs = true →
      SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none := by
    intro earlier member allowed
    exact supported earlier (List.mem_of_mem_take member) allowed
  obtain ⟨headCaller, headInventory, headMemos, branchCaller, branchQueries, branchMemos,
    branchInventory, afterCache, extended, fragment, inputPost, branchPost, branchQuery,
    selectedReceipt, selectedRun, agree, oldSatisfied, filled, afterSatisfied⟩ :=
    accepting index chosen found prefixSupported ambient assignment satisfied accepted
  refine ⟨r, n, p, h, k, processed, afterCaller, saved, final, next, result, ?_,
    allSupported supported, index, chosen, found, headCaller, headInventory, headMemos,
    branchCaller, branchQueries, branchMemos, branchInventory, afterCache, extended, fragment,
    inputPost, branchPost, branchQuery, selectedReceipt, selectedRun, agree, oldSatisfied,
    filled, afterSatisfied⟩
  exact ⟨running, post, querySame, admitted, pendingHistory, receiptPosts, fragmentHistory,
    shape, allSupported, returnedFits, returnedKnown, indexedResources, accepting⟩

end MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
