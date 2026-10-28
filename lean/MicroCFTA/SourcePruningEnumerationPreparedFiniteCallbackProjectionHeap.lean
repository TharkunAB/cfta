import MicroCFTA.SourcePruningEnumerationSuspendedMass
import MicroCFTA.SourcePruningEnumerationPreparedFiniteProjectionHeapContract
import MicroCFTA.SourcePruningEnumerationRecursiveCallback

/-!
# Projection at the actual finite prepared callback

The callback retains every stored bucket. The returned packet uses the
same original mass ceiling. One common work bound covers recording and
the recursive driver supplied by the smaller-depth contract.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output)
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
local notation "ProjectionHeap" => Heap
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- The original callback packet and finite-depth contract derive the actual hook and its resources. -/
theorem callback_finite_complete_resources_projection_heap
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveFuel : Nat)
    (recursive : CompleteWithProjectionHeap (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling)
    (initialProjection : ProjectionHeap caller.checked.native.machine.heap) :
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
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      OutcomeProjectionHeap outcome := by
  obtain ⟨callbackFuel, result, after, returned, stable, frame, types, holes, typing, originalCallback⟩ :=
    SourcePruningEnumerationRecursive.callback_complete formulas solver inventory graph templates metadata uv fragment caller memos before
      packet allocated
  have callback : ∀ extra,
      Success (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment)) before.core result after ∧
      ExceptT.run (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment) before.core) =
        [.ok (result, after)] ∧
      ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result) stop order,
        continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment caller memos.query before =
          if result.1 then .complete [] caller memos.query
          else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
            (SourcePruningEnumerationRestart.decision stop order result.2
              (EnumerationExpandableIndex.frame after before)) := by
    intro extra
    have actual := originalCallback extra
    refine ⟨actual.1, actual.2.1, ?_⟩
    intro recur stop order
    simp only [continueWith, actual.2.1]
    cases result with
    | mk accepted updated => cases accepted <;> rfl
  by_cases rejected : result.1 = true
  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact False.elim (List.not_mem_nil member)
    have growth := SourcePruningEnumerationPreparedReservation.final_ge recursiveFuel seed ceiling
    have projected : OutcomeProjectionHeap (Typing := Typing) (.complete [] caller memos.query) := by
      exact ⟨initialProjection, fun _ member => False.elim (List.not_mem_nil member)⟩
    refine ⟨callbackFuel, result, after, .complete [] caller memos.query,
      returned, stable, frame, types, holes, typing, callback, ?_,
      resources.mono growth.1 growth.2, projected⟩
    intro extra
    rw [(callback extra).2.2
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (callbackFuel + extra) recursiveFuel)
      stop order, ite_eq_left rejected]
  · have massAfter : suspendedBound (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
      change suspendedBound after ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
      exact mass
    obtain ⟨resumeFuel, outcome, running, resources, projected⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame after before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength massAfter reserved initialProjection
    refine ⟨callbackFuel + resumeFuel, result, after, outcome,
      returned, stable, frame, types, holes, typing, ?_, ?_, resources, projected⟩
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      exact actual
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      rw [actual.2.2
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (callbackFuel + resumeFuel + extra) recursiveFuel) stop order, ite_eq_right rejected]
      have observed := running (callbackFuel + extra)
      have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
      rw [common] at observed
      exact observed

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
