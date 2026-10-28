import MicroCFTA.SourcePruningEnumerationPreparedFiniteResources
import MicroCFTA.SourcePruningEnumerationPreparedFiniteCallbackResources
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.SourcePruningRecordTypesRefutation

/-!
# Models at the actual prepared fragment callback

The finite resource producer fixes the work bound and actual return first.
The callback frame preserves assignments at the unchanged native heap.
Original template policies exclude rejection and retain the same restart.
No semantic property of recursive outputs is assumed or concluded.
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
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- Retain the complete finite callback packet and derive its original-model restart. -/
theorem callback_finite_complete_resources_models
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
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core) (outcome : Result),
      (Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
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
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome) ∧
      (∀ (language : NodeLanguage Symbol)
        (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
        Satisfies language meaning assignment (EnumerationExpandableIndex.frame after before).core ↔
          Satisfies language meaning assignment before.core) ∧
      ∀ (language : NodeLanguage Symbol)
        (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
        Satisfies language meaning assignment before.core →
        Fragments.fill assignment fragment = assignment uv →
        (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
          (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) →
        SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment) →
        (∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
          SourcePruningTemplates.ProgramEncoding program) →
        Satisfies language meaning assignment (EnumerationExpandableIndex.frame after before).core ∧
          result.1 = false ∧
          (∀ group ∈ result.2.pending, @SourcePruningResume.Refutes Symbol
          (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) ∧
          ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (fuel + extra) recursiveFuel result.2 caller memos.query
              (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before)) = outcome := by
  have recursive := SourcePruningEnumerationPreparedRecursive.finite_complete
    (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
  obtain ⟨fuel, result, after, outcome, returned, stable, framed, types, holes, typing, callback, running, resources⟩ :=
    callback_finite_complete_resources holeKey fits admits formulas solver inventory graph templates metadata uv fragment
      caller memos before checkEmpty edgesOf stop order recursiveFuel recursive seed ceiling
      packet allocated bounded known selectionMembers selectionLength mass reserved
  refine ⟨fuel, result, after, outcome,
    ⟨returned, stable, framed, types, holes, typing, callback, running, resources⟩, ?_, ?_⟩
  · intro language meaning assignment
    exact SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning assignment before.core after framed
  · intro language meaning assignment satisfied filled refuted avoids encoded
    have kept := SourcePruningRecordTypes.recordTypes_inl_refutes graph language meaning assignment templates
      (fuel + 0) uv metadata fragment before.core after result packet.safe.1.total
      satisfied filled refuted avoids encoded (callback 0).1
    have afterSatisfied := (SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning assignment
      before.core after framed).mpr satisfied
    refine ⟨afterSatisfied, kept.1, kept.2, ?_⟩
    intro extra
    have actual := (callback extra).2.2
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
      stop order
    have notRejected : ¬ result.1 = true := by
      rw [kept.1]
      decide
    rw [ite_eq_right notRejected] at actual
    exact actual.symm.trans (running extra)

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
