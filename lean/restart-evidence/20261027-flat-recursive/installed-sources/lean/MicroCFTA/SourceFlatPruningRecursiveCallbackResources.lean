import MicroCFTA.SourcePruningEnumerationSuspendedMass
import MicroCFTA.SourceFlatPruningFiniteContract
import MicroCFTA.SourceFlatPruningContinuation
import MicroCFTA.SourcePruningEnumerationRecursiveCallback

/-!
# Actual flat fragment callbacks at finite recursive depth

The original callback producer runs before the flat input is quantified.
The returned packet retains the original mass ceiling. One common work
bound covers recording and the related smaller-depth recursive driver.
-/
namespace MicroCFTA.SourceFlatPruningRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningRecordTypes
open SourcePruningEnumerationRecursive (Packet callback_complete OutcomeResources)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (SourcePruningEnumerationRecursive.Output (bits + 2) Typing)
  (SourcePruningEnumerationRecursive.Failure (bits + 2) Typing) (bits + 2)

/-- Original callback resources derive both actual hooks at one uniform finite-depth bound. -/
theorem callback_finite_complete_resources
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
          SourcePruningEnumerationRecursive.continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      (∀ extra, SourcePruningEnumerationRecursive.continueWith
        (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatOutcome,
          SourceFlatPruningRecursive.continueWith
            (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
              stop order (fuel + extra) recursiveFuel)
            graph templates stop order (fuel + extra) metadata uv fragment caller memos.query flat = flatOutcome ∧
          SourceFlatPruningRecursive.ResultRelated flatOutcome outcome) := by
  obtain ⟨callbackFuel, result, after, returned, stable, frame, types, holes, typing, callback⟩ :=
    callback_complete formulas solver inventory graph templates metadata uv fragment caller memos before
      packet allocated
  by_cases rejected : result.1 = true
  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact False.elim (List.not_mem_nil member)
    have growth := SourcePruningEnumerationFiniteReservation.final_ge recursiveFuel seed ceiling
    refine ⟨callbackFuel, result, after, .complete [] caller memos.query,
      returned, stable, frame, types, holes, typing, callback, ?_, resources.mono growth.1 growth.2, ?_⟩
    · intro extra
      rw [(callback extra).2.2
        (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
          stop order (callbackFuel + extra) recursiveFuel) stop order, ite_eq_left rejected]
    · intro flat related extra
      obtain ⟨flatAfter, actual, _cores⟩ := SourceFlatPruningOracle.recordTypes_replays graph templates
        (callbackFuel + extra) metadata uv (.inl fragment) flat.core before.core result after related.core
          (callback extra).1
      refine ⟨.complete [] caller memos.query, ?_, ?_⟩
      · change SourceFlatPruningContinuation.continueWith SourceFlatPruningRecursive.Failure.callback
          (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (callbackFuel + extra) recursiveFuel) graph templates stop order (callbackFuel + extra)
          metadata uv fragment caller memos.query flat = .complete [] caller memos.query
        rw [SourceFlatPruningContinuation.continueWith_exact SourceFlatPruningRecursive.Failure.callback
          (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (callbackFuel + extra) recursiveFuel) graph templates stop order (callbackFuel + extra)
          metadata uv fragment caller memos.query flat result flatAfter actual, ite_eq_left rejected]
      · exact ⟨.nil, rfl, rfl⟩
  · have massAfter : suspendedBound (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
      change suspendedBound after ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
      exact mass
    obtain ⟨resumeFuel, outcome, running, resources, flatRunning⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame after before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength massAfter reserved
    refine ⟨callbackFuel + resumeFuel, result, after, outcome,
      returned, stable, frame, types, holes, typing, ?_, ?_, resources, ?_⟩
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      exact actual
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      rw [actual.2.2
        (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
          stop order (callbackFuel + resumeFuel + extra) recursiveFuel) stop order, ite_eq_right rejected]
      have observed := running (callbackFuel + extra)
      have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
      rw [common] at observed
      exact observed
    · intro flat related extra
      have success := (callback (resumeFuel + extra)).1
      rw [← Nat.add_assoc] at success
      obtain ⟨flatAfter, actual, cores⟩ := SourceFlatPruningOracle.recordTypes_replays graph templates
        (callbackFuel + resumeFuel + extra) metadata uv (.inl fragment) flat.core before.core result after
        related.core success
      have caches := EnumerationFlatCached.frame_related related cores
      obtain ⟨flatOutcome, resumed, compared⟩ :=
        flatRunning (EnumerationFlatCached.frame flatAfter flat) caches (callbackFuel + extra)
      have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
      rw [common] at resumed
      refine ⟨flatOutcome, ?_, compared⟩
      change SourceFlatPruningContinuation.continueWith SourceFlatPruningRecursive.Failure.callback
        (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (callbackFuel + resumeFuel + extra) recursiveFuel) graph templates stop order
          (callbackFuel + resumeFuel + extra) metadata uv fragment caller memos.query flat = flatOutcome
      rw [SourceFlatPruningContinuation.continueWith_exact SourceFlatPruningRecursive.Failure.callback
        (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (callbackFuel + resumeFuel + extra) recursiveFuel) graph templates stop order
          (callbackFuel + resumeFuel + extra) metadata uv fragment caller memos.query flat result flatAfter actual,
        ite_eq_right rejected]
      exact resumed

end MicroCFTA.SourceFlatPruningRecursive
