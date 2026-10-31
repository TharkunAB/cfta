import MicroCFTA.SourceCurrentIncomingPost
import MicroCFTA.SourceCurrentAllocatedNativeFoldIncomingEntry
import MicroCFTA.SourcePruningEnumerationTerminalPrefixBounds

/-! A literal terminal return that permits the next field derives caller Post. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentTerminalPost
open EnumerationState EnumerationCorrectness EnumerationCompleteness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
attribute [local instance] FormulaExecutable.formulaDecidableEq
attribute [local instance] SourcePruningEnumerationTerminal.terminalMonadList
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {bits : Nat} [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- An actual singleton success derives Post and the exact saved query memo. -/
theorem terminal_continue_post (bound : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (incoming : Node) (incomingScs : List Suspended) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter)
    (pending : InputsPending before.core (first :: rest))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits seed.2 caller.checked) (reserved : Reserved bits seed ((first :: rest).length + 1))
    (annotated : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (stored : Stored caller.checked.native)
    (known : KnownOrdinary bound caller.checked.native.machine.heap before) :
    let actual := SourcePruningEnumerationTerminal.run checkEmpty r n p h first rest
      before.waiting caller before.core incoming incomingScs memos.query
    match actual.1 with
    | .ok (some [.ok _]) => ∃ next final,
        Post formulas solver next caller actual.2.1 final ∧ final.query = actual.2.2.1
    | _ => True := by
  letI : DecidableEq Node := fun a b => Classical.propDecidable (a = b)
  rw [SourcePruningEnumerationTerminal.run]
  by_cases empty : incoming = .empty
  · simp only [ite_eq_left empty]
  · simp only [ite_eq_right empty]
    cases prefixObserved : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting before.core) with
    | nil => trivial
    | cons prefixEntry prefixTail =>
        cases prefixEntry with
        | error fault => trivial
        | ok prefixResult =>
            rcases prefixResult with ⟨⟨recorded, winner, moved⟩, joined⟩
            cases prefixTail with
            | cons second remaining => trivial
            | nil =>
                simp only
                obtain ⟨recordedSame, joinedRealized, winnerPending, recordedPending⟩ :=
                  SourcePruningEnumerationCachedTerminalAdapter.observed_prefix
                    caller.checked.native.machine.heap before.core first rest before.waiting roots
                    paths counts safe bounded pending realized prefixObserved
                have prefixFrame := SourcePruningEnumerationTerminalPrefix.success_frame r first rest
                  before.waiting before.core joined (recorded, winner, moved) (by
                    change Except.ok ((recorded, winner, moved), joined) ∈
                      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting before.core)
                    rw [prefixObserved]
                    exact List.mem_singleton.mpr rfl)
                have valuesSame : joined.values = before.core.values := by
                  simpa only using congrArg (fun state : Core => state.values) prefixFrame
                have joinedKnown : KnownOrdinary bound caller.checked.native.machine.heap
                    ⟨joined, before.expandable, moved⟩ := by
                  simpa only [KnownOrdinary, valuesSame] using known
                have countSame : recorded.length = (first :: rest).length := by
                  rw [recordedSame, List.length_map]
                have reservation : Reserved bits seed (recorded.length + 1) := by
                  simpa only [countSame] using reserved
                have selected : ∀ source ∈ recorded, PendingOrEliminated joined source :=
                  fun source member => .inl (recordedPending source member)
                have entry := SourceCurrentAllocatedNativeFoldIncomingEntry.fold_incoming_entry bits bound seed
                  formulas solver inventory caller ⟨joined, before.expandable, moved⟩ recorded checkEmpty n p h
                  winner memos incoming initial joinedRealized winnerPending selected fits reservation annotated stored joinedKnown available
                rcases foldObserved : SourcePruningEnumerationFold.run checkEmpty n p h recorded
                    caller joined winner memos.query with ⟨foldOutcome, foldCaller, foldQueries, foldOuter⟩
                rw [foldObserved] at entry
                cases foldOutcome with
                | error fault => trivial
                | ok possible =>
                    cases possible with
                    | none => trivial
                    | some foldRaw =>
                        cases foldRaw with
                        | nil => trivial
                        | cons firstRow tail =>
                            cases firstRow with
                            | error fault => trivial
                            | ok row =>
                                rcases row with ⟨valueUnit, folded⟩
                                cases valueUnit
                                cases tail with
                                | cons second remaining => trivial
                                | nil =>
                                    obtain ⟨next, final, post, querySame, foldRealized, _foldPending,
                                      foldFits, foldRoom, _foldAnnotated, _foldStored, _foldKnown, foldAvailable⟩ := entry
                                    have incomingPost := SourceCurrentIncomingPost.incoming_ok_post _
                                      formulas solver next foldCaller folded checkEmpty r n p h winner incoming incomingScs
                                      final post.context foldRealized foldAvailable closed foldFits foldRoom
                                    rw [querySame] at incomingPost
                                    rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                                        foldCaller folded winner incoming incomingScs foldQueries with
                                      ⟨incomingResult, afterCaller, savedQueries, read⟩
                                    rw [incomingObserved] at incomingPost
                                    simp only [incomingObserved]
                                    cases incomingResult with
                                    | error fault => trivial
                                    | ok possible =>
                                        obtain ⟨later, saved, incomingPost, savedSame⟩ := incomingPost
                                        cases possible with
                                        | none => trivial
                                        | some incomingRaw =>
                                            simp only
                                            split <;> first
                                            | exact ⟨later, saved, post.trans incomingPost, savedSame⟩
                                            | trivial

end MicroCFTA.SourceCurrentTerminalPost
