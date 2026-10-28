import MicroCFTA.SourcePruningEnumerationPreparedRecursiveEquations
import MicroCFTA.SourcePruningEnumerationRecursiveCallback
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.SourcePruningRecordTypesRefutation

/-!
# Actual prepared terminal callback emission from an original model

The original callback cache has no remaining candidates.
Its complete recording preserves the original model and cannot reject it.
The actual prepared restart emits the same modeled cache at every depth.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open Language EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An original terminal callback model constructs its exact actual singleton emission. -/
theorem callback_no_candidates_emits_models
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (empty : EnumerationIndexSelection.candidates before = [])
    (language : NodeLanguage Symbol) (meaning : Constraint → Term Symbol → Prop)
    (assignment : Nat → Term Symbol)
    (satisfied : Satisfies language meaning assignment before.core)
    (filled : Fragments.fill assignment fragment = assignment uv)
    (refuted : ∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
      (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq)
      assignment group)
    (avoids : SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment))
    (encoded : ∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
      SourcePruningTemplates.ProgramEncoding program) :
    ∃ (fuel : Nat) (updated : Metadata Typing) (after : Core),
      Packet formulas solver inventory caller memos updated (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      updated.types = updatedTypes metadata uv (.inl fragment) ∧
      updated.openHoles = metadata.openHoles ∧ updated.typing = metadata.typing ∧
      Satisfies language meaning assignment (EnumerationExpandableIndex.frame after before).core ∧
      (∀ group ∈ updated.pending, @SourcePruningResume.Refutes Symbol
      (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq)
      assignment group) ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment))
          before.core (false, updated) after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok ((false, updated), after)] ∧
        ∀ depth, continueWith
          (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) depth)
          graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            .complete [⟨none, EnumerationExpandableIndex.frame after before, caller, memos.query⟩]
              caller memos.query := by
  obtain ⟨fuel, result, after, returned, stable, framed, types, holes, typing, callback⟩ :=
    SourcePruningEnumerationRecursive.callback_complete formulas solver inventory graph templates
      metadata uv fragment caller memos before packet allocated
  have kept := recordTypes_inl_refutes graph language meaning assignment templates (fuel + 0) uv metadata
    fragment before.core after result packet.safe.1.total satisfied filled refuted avoids encoded (callback 0).1
  have afterSatisfied := (SourcePruningEnumerationNativeLanguage.satisfies_frame
    language meaning assignment before.core after framed).mpr satisfied
  rcases result with ⟨rejected, updated⟩
  obtain ⟨notRejected, pendingRefutes⟩ := kept
  change rejected = false at notRejected
  subst rejected
  refine ⟨fuel, updated, after, returned, stable, framed, types, holes, typing, afterSatisfied, pendingRefutes, ?_⟩
  intro extra
  refine ⟨(callback extra).1, (callback extra).2.1, ?_⟩
  intro depth
  have done : SourcePruningEnumerationRestart.decision stop order updated
      (EnumerationExpandableIndex.frame after before) = some .done := by
    rw [SourcePruningEnumerationRestart.decision_frame stop order updated before after framed.counter]
    cases stop <;> simp [SourcePruningEnumerationRestart.decision, EnumerationPureSelection.next,
      EnumerationPureSelection.find, empty, pickNext]
  simp only [continueWith, (callback extra).2.1, done, resume]

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
