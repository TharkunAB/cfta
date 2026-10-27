import MicroCFTA.SourcePruningEnumerationFiniteCallbackResources
import MicroCFTA.SourcePruningEnumerationFiniteResources
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.SourcePruningEnumerationIsolatedPending
import MicroCFTA.EnumerationValidity

/-!
# Actual finite callback receipts and local assignment meaning

The original finite callback keeps its complete execution and resource packet.
The returned frame retains assignments at the unchanged native heap.
A false callback supplies its actual framed recursive restart input.
No semantic claim about rejection or the recursive continuation is assumed.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- An actual false callback retains its recorded state and concrete finite recursive restart. -/
structure FalseCallbackReceipt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveFuel fuel : Nat) (updated : Metadata Typing) (after : Core) (outcome : Result) : Prop where
  /-- The callback starts at the literal original caller, full Memos and cache. -/
  original : Packet formulas solver inventory caller memos metadata before
  /-- The next recursive input uses the actual returned metadata and framed core. -/
  returned : Packet formulas solver inventory caller memos updated (EnumerationExpandableIndex.frame after before)
  /-- The original safe render receipt remains available. -/
  stable : RenderStable before.core after
  /-- The callback retains the exact core frame. -/
  frame : Frame before.core after
  /-- Every larger common work bound records this exact false callback singleton. -/
  recording : ∀ extra,
    ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
      [.ok ((false, updated), after)]
  /-- The concrete callback uses the same work bound as its recursive continuation. -/
  continuing : ∀ extra, continueWith
    (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
    graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome
  /-- The actual false branch restarts at its updated metadata, framed cache and decision. -/
  restarting : ∀ extra,
    resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel
      updated caller memos.query (EnumerationExpandableIndex.frame after before)
      (SourcePruningEnumerationRestart.decision stop order updated (EnumerationExpandableIndex.frame after before)) = outcome

/-- Keep the entire finite callback packet and append local laws and its actual false restart receipt. -/
theorem callback_finite_complete_resources_with_receipt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveFuel : Nat)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core) (outcome : Result),
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      (∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result) stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      (∀ extra, continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap) residualMeaning assignment after ↔
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap) residualMeaning assignment before.core) ∧
      (EnumerationValidity.Canonical before.core → EnumerationValidity.Canonical after) ∧
      (∀ held handle, EnumerationDischargeHistory.IsolatedPending held handle before.core →
        EnumerationDischargeHistory.IsolatedPending held handle after) ∧
      (result.1 = false → FalseCallbackReceipt holeKey fits admits formulas solver inventory graph templates
        metadata uv fragment caller memos before checkEmpty edgesOf stop order recursiveFuel fuel result.2 after outcome) := by
  obtain ⟨fuel, result, after, outcome, returned, stable, frame, types, holes, typing, callback, running, resources⟩ :=
    callback_finite_complete_resources holeKey fits admits formulas solver inventory graph templates metadata uv fragment
      caller memos before checkEmpty edgesOf stop order recursiveFuel recursive seed ceiling packet allocated bounded known
      selectionMembers selectionLength mass reserved
  refine ⟨fuel, result, after, outcome, returned, stable, frame, types, holes, typing, callback, running, resources,
    ?_, ?_, ?_, ?_⟩
  · intro ambient residualMeaning assignment
    exact SourcePruningEnumerationNativeLanguage.satisfies_frame
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      residualMeaning assignment before.core after frame
  · intro canonical value member
    exact canonical value (by simpa only [frame.values] using member)
  · intro held handle isolated
    exact isolated.through_frame frame
  · intro accepted
    have resultSame : result = (false, result.2) := Prod.ext accepted rfl
    have notRejected : result.1 ≠ true := by
      intro impossible
      rw [accepted] at impossible
      cases impossible
    refine ⟨packet, returned, stable, frame, ?_, running, ?_⟩
    · intro extra
      have actual := (callback extra).2.1
      rw [resultSame] at actual
      exact actual
    · intro extra
      have actual := (callback extra).2.2
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
        stop order
      rw [ite_eq_right notRejected] at actual
      exact actual.symm.trans (running extra)

/-- Original finite resources supply the smaller-depth completion contract for the same full receipt. -/
theorem callback_finite_complete_receipt_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveFuel : Nat)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core) (outcome : Result),
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      (∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result) stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      (∀ extra, continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap) residualMeaning assignment after ↔
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap) residualMeaning assignment before.core) ∧
      (EnumerationValidity.Canonical before.core → EnumerationValidity.Canonical after) ∧
      (∀ held handle, EnumerationDischargeHistory.IsolatedPending held handle before.core →
        EnumerationDischargeHistory.IsolatedPending held handle after) ∧
      (result.1 = false → FalseCallbackReceipt holeKey fits admits formulas solver inventory graph templates
        metadata uv fragment caller memos before checkEmpty edgesOf stop order recursiveFuel fuel result.2 after outcome) := by
  exact callback_finite_complete_resources_with_receipt holeKey fits admits formulas solver inventory graph templates
    metadata uv fragment caller memos before checkEmpty edgesOf stop order recursiveFuel
    (finite_complete holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel)
    seed ceiling packet allocated bounded known selectionMembers selectionLength mass reserved

end MicroCFTA.SourcePruningEnumerationRecursive
