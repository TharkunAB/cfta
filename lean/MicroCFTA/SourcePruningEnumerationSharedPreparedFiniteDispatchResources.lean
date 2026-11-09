import MicroCFTA.SourcePruningEnumerationSelectedPreparationCurrent
import MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteOrdinaryResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteOpaqueResources

/-!
# One actual preparation and its finite shared branch

The common preparation supplies one current packet and native endpoint.
Ordinary rows use that prepared parent. Opaque and terminal values use
the actual shared child receipt. Each branch runs its Left callback and
smaller recursive continuation. Finalization keeps the original target.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Preparation" => SourcePruningEnumerationSharedPreparedContinuations.Preparation
local notation "Fold" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "Forecast" => SourcePruningEnumerationSharedPreparedReservation.final
attribute [local irreducible] SourcePruningEnumerationSharedPreparedReservation.step
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The same preparation and current reservations derive its literal finite shared dispatch. -/
theorem prepared_dispatch_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (recursiveFuel : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : ResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (ceiling : Nat) (initialMass : mass before.core ≤ ceiling) (inheritedLength : scs.length ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits (recursiveFuel + 1) seed ceiling) :
    ∃ (bound : Nat) (observation : Preparation)
      (folded : Fold (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationSharedPreparedContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          (bound + extra) (bound + extra) (bound + extra) uv edgesOf caller before memos.query =
        (observation, some folded)) ∧
      OutcomeResources formulas solver caller (Forecast (recursiveFuel + 1) seed ceiling) (finish uv folded) := by
  let start := SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed
  obtain ⟨preparationFuel, decoded, value, heap, entered, retained,
    preparedFits, _valueMass, preparedKnown, frame, enteredIncoming, sameMass⟩ :=
    SourcePruningEnumerationSelectedPreparation.complete_resources_current
      formulas solver inventory caller memos metadata before uv handle scs packet ready stored
      (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 bounded incoming
      (fun guard => guard ∈ seed.1) known
  obtain ⟨preparationRun, _decodedLookup, preparationPost, enteredPacket, _stable, enteredReady,
    enteredStored, _counter, _values, _flags, _waiting, available, closed, _meaning, _satisfaction⟩ := retained
  let preparedCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
  have currentFits : Fits start.2 preparedCaller.checked := preparedFits
  have currentKnown : Heap (fun guard => guard ∈ start.1)
      preparedCaller.checked.native.machine.heap := preparedKnown
  have currentMass : mass entered.core ≤ ceiling := by
    rw [sameMass]
    exact initialMass
  by_cases ordinary : ∃ entry rows depth free,
      value = .node entry rows depth free ∧ scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false
  · obtain ⟨entry, rows, depth, free, same, nonterminal⟩ := ordinary
    subst value
    have rowWidth := SourceCurrentConstrainedCapRequiredResources.node_width
      (SourceCurrentConstrainedCapRequiredResources.of_checked currentFits) available
    have countBound : (edgesOf (.node entry rows depth free)).length ≤
        SourcePruningEnumerationSharedPreparedReservation.rows seed :=
      Nat.le_trans (selectionLength entry rows depth free) (Nat.le_trans rowWidth (Nat.le_succ _))
    obtain ⟨branchFuel, folded, branchRun, certificate⟩ := ordinary_finite_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel start
      formulas solver recursive inventory preparedCaller memos entered uv handle scs entry rows depth free
      enteredPacket enteredReady enteredStored available closed enteredIncoming currentFits currentKnown
      selectionMembers selectionLength ceiling currentMass inheritedLength (reserved.ordinary _ countBound)
    have growth := SourcePruningEnumerationSharedPreparedReservation.stage_le_final
      recursiveFuel seed ceiling (edgesOf (.node entry rows depth free)).length countBound
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done (.node entry rows depth free) heap)),
      folded, ?_, (certificate.mono growth.1 growth.2).post preparationPost⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepCommon : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepCommon] at atPreparation
    have atBranch := branchRun (preparationFuel + extra)
    have branchCommon : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchCommon] at atBranch
    have actual := SourcePruningEnumerationSharedPreparedContinuations.ordinary
      (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (preparationFuel + branchFuel + extra) recursiveFuel) graph templates stop order
        (preparationFuel + branchFuel + extra) metadata uv)
      checkEmpty (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
        (preparationFuel + branchFuel + extra) uv uv handle scs decoded entry rows depth free heap entered.core
        edgesOf caller before memos.query atPreparation nonterminal
    rw [frame, atBranch] at actual
    exact actual
  · have dispatch : (match (generalizing := false) value with
        | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
        | _ => false) = false := by
      cases value with
      | node entry rows depth free =>
          cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
          | false => exact (ordinary ⟨entry, rows, depth, free, rfl, terminal⟩).elim
          | true => rfl
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ => rfl
    obtain ⟨branchFuel, _receipt, _middleCaller, _saved, _final, _next, _outcome, folded,
      _opaqueRun, _post, _query, _advance, _admitted, _pending, _history, _fits, _known,
      _shape, _headFits, _headKnown, _callbackRun, _receiptRun, certificate, composed, _finalization⟩ :=
      SourcePruningEnumerationSharedPreparedNativeHookResources.opaque_finite_complete_resources
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel start
        formulas solver recursive inventory preparedCaller memos entered uv handle scs value
        enteredPacket enteredReady enteredStored enteredIncoming available closed dispatch currentFits currentKnown
        selectionMembers selectionLength ceiling ceiling currentMass inheritedLength reserved.first
    have growth := SourcePruningEnumerationSharedPreparedReservation.first_le_final recursiveFuel seed ceiling
    refine ⟨preparationFuel + branchFuel,
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)), folded,
      ?_, (certificate.mono growth.1 growth.2).post preparationPost⟩
    intro extra
    have atPreparation := preparationRun (branchFuel + extra)
    have prepCommon : preparationFuel + (branchFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [prepCommon] at atPreparation
    have atBranch := composed (preparationFuel + extra)
    have branchCommon : branchFuel + (preparationFuel + extra) = preparationFuel + branchFuel + extra := by omega
    rw [branchCommon] at atBranch
    have actual : SourcePruningEnumerationSharedPreparedContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (preparationFuel + branchFuel + extra) recursiveFuel) graph templates stop order
          (preparationFuel + branchFuel + extra) metadata uv)
        checkEmpty (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
          (preparationFuel + branchFuel + extra) uv edgesOf caller before memos.query =
        (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)),
          some (SourcePruningEnumerationSharedReceiptContinuation.run
            (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (preparationFuel + branchFuel + extra) recursiveFuel) graph templates stop order
              (preparationFuel + branchFuel + extra) metadata uv) preparedCaller memos.query
            (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
              (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
              (preparationFuel + branchFuel + extra) (preparationFuel + branchFuel + extra)
              (preparationFuel + branchFuel + extra) uv scs value preparedCaller entered memos.query))) := by
      unfold SourcePruningEnumerationSharedPreparedContinuations.run
      rw [atPreparation]
      cases value with
      | node entry rows depth free =>
          have terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true := by
            cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
            | false => exact (ordinary ⟨entry, rows, depth, free, rfl, here⟩).elim
            | true => rfl
          simp only [terminal, ↓reduceIte, frame, preparedCaller]
      | empty | reference _ | mu _ _ _ _ | union _ _ _ _ =>
          cases here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;>
            simp only [here, Bool.false_eq_true, ↓reduceIte, frame, preparedCaller]
    rw [atBranch] at actual
    exact actual

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
