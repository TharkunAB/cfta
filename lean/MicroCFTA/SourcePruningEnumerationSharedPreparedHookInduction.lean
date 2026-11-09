import MicroCFTA.SourcePruningEnumerationSharedPreparedCallbackResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedReservation
import MicroCFTA.SourcePruningEnumerationSuspendedMass

/-!
# The actual prepared shared Left hook at a smaller recursive depth

The callback supplies its own updated metadata and framed cache.
A smaller-depth induction hypothesis runs at those current inputs.
Its reservation and mass ceiling apply to that same cache and native seed.
The result retains every recursive output and the actual optional endpoint.
This composition does not discharge the whole recursive induction.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
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
variable {Typing : Type}

section Failure
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- An actual failed callback keeps its raw observation and the unchanged native endpoint. -/
theorem callback_failed_resources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (raw : List (Except EnumerationState.Error ((Bool × Metadata Typing) × Core)))
    (actual : ExceptT.run (recordTypes graph templates fuel metadata uv (.inl fragment) before.core) = raw)
    (failed : ∀ flag updated observed, raw ≠ [.ok ((flag, updated), observed)]) :
    continueWith recur graph templates stop order fuel metadata uv fragment caller memos.query before =
      .stopped [] (.callback uv raw) (some (caller, memos.query)) ∧
    OutcomeResources formulas solver caller seed
      (.stopped [] (.callback uv raw) (some (caller, memos.query))) := by
  refine ⟨?_, caller, inventory, memos, Post.refl packet.context, bounded, known, Or.inr rfl, ?_⟩
  · unfold continueWith
    rw [actual]
    cases raw with
    | nil => rfl
    | cons first rest =>
        cases rest with
        | cons second tail =>
            cases first with
            | error fault => rfl
            | ok observed =>
                obtain ⟨⟨flag, updated⟩, after⟩ := observed
                cases flag <;> rfl
        | nil =>
            cases first with
            | error fault => rfl
            | ok observed =>
                obtain ⟨⟨flag, updated⟩, after⟩ := observed
                exact (failed flag updated after rfl).elim
  · intro output member
    exact (List.not_mem_nil member).elim
end Failure

section Induction
variable {Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- The smaller-depth hypothesis quantifies current packets and actual shared resume calls. -/
def ResumeComplete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    suspendedBound before.core ≤ ceiling →
    SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveDepth seed ceiling →
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) recursiveDepth metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before) = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveDepth seed ceiling) outcome

/-- The actual callback supplies every current input of the smaller-depth recursion hypothesis. -/
theorem callback_induction_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveDepth : Nat)
    (recursive : ResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveDepth seed ceiling) :
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
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveDepth seed ceiling) outcome := by
  obtain ⟨callbackFuel, result, after, returned, stable, frame, types, holes, typing,
    _currentFits, _currentKnown, callback⟩ :=
    callback_complete_resources formulas solver inventory graph templates metadata uv fragment caller memos before
      seed packet allocated bounded known
  by_cases rejected : result.1 = true
  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed
        (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := SourcePruningEnumerationSharedPreparedReservation.final_ge recursiveDepth seed ceiling
    refine ⟨callbackFuel, result, after, .complete [] caller memos.query,
      returned, stable, frame, types, holes, typing, callback, ?_, resources.mono growth.1 growth.2⟩
    intro extra
    rw [(callback extra).2.2
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (callbackFuel + extra) recursiveDepth)
      stop order, ite_eq_left rejected]
  · have massAfter : suspendedBound (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
      change suspendedBound after ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
      exact mass
    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame after before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength massAfter reserved
    refine ⟨callbackFuel + resumeFuel, result, after, outcome,
      returned, stable, frame, types, holes, typing, ?_, ?_, resources⟩
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      exact actual
    · intro extra
      have actual := callback (resumeFuel + extra)
      rw [← Nat.add_assoc] at actual
      rw [actual.2.2
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (callbackFuel + resumeFuel + extra) recursiveDepth) stop order, ite_eq_right rejected]
      have observed := running (callbackFuel + extra)
      have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
      rw [common] at observed
      exact observed

end Induction
end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedNativeHookResources
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure ResumeComplete)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "advance" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- A current admitted receipt supplies its own callback packet before smaller-depth recursion. -/
theorem receipt_induction_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original next : Inventory) (caller reached : Caller (bits + 2)) (memos final : Memos) (before : Cached)
    (uv : Nat) (receipt : Receipt (bits + 2))
    (packet : Packet formulas solver original caller memos metadata before)
    (post : Post formulas solver next caller reached final)
    (advanced : advance receipt = some (reached, final.query))
    (admitted : Admitted uv receipt) (pending : Pending receipt) (history : FragmentHistory before.core receipt)
    (recursiveDepth : Nat)
    (recursive : ResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (bounded : Fits seed.2 reached.checked)
    (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : match receipt with
      | .complete _ _ _ current => suspendedBound current.core ≤ ceiling
      | _ => True)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveDepth seed ceiling) :
    ∃ (fuel : Nat) (outcome : Result),
      (∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            SourcePruningEnumerationSharedPreparedRecursive.continueWith
              (SourcePruningEnumerationSharedPreparedRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf
                stop order (fuel + extra) recursiveDepth)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after = outcome
        | _ => outcome = .complete [] reached final.query) ∧
      SourcePruningEnumerationSharedPreparedRecursive.OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveDepth seed ceiling) outcome := by
  cases receipt with
  | unhandled | finalizeStopped _ _ _ _ => cases advanced
  | rejected actual saved after | stopped fragments observation candidate =>
      have resources : SourcePruningEnumerationSharedPreparedRecursive.OutcomeResources (Typing := Typing) formulas solver caller seed
          (.complete [] reached final.query) := by
        refine ⟨reached, next, final, post, bounded, known, rfl, rfl, ?_⟩
        intro output member
        exact (List.not_mem_nil member).elim
      have growth := SourcePruningEnumerationSharedPreparedReservation.final_ge recursiveDepth seed ceiling
      exact ⟨0, .complete [] reached final.query, fun _ => rfl, resources.mono growth.1 growth.2⟩
  | complete fragment actual saved after =>
      have endpoints : (actual, saved) = (reached, final.query) := Option.some.inj advanced
      obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
      subst actual
      subst saved
      obtain ⟨level, frontier, ordered⟩ := packet.ordered
      have current := SourcePruningEnumerationSharedPreparedRecursive.receipt_packet formulas solver next reached final metadata
        before.core uv fragment after level frontier post.context admitted history pending ordered packet.bounded
      obtain ⟨fuel, result, observed, outcome, _updatedPacket, _stable, _frame, _types, _holes, _typing,
        _raw, running, resources⟩ :=
        SourcePruningEnumerationSharedPreparedRecursive.callback_induction_complete_resources holeKey fits admits
          formulas solver next graph templates metadata uv fragment reached final after checkEmpty edgesOf stop order
          recursiveDepth recursive seed ceiling current admitted.2.2.1 bounded known selectionMembers selectionLength mass reserved
      exact ⟨fuel, outcome, running, resources.post post⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparedNativeHookResources
