import MicroCFTA.SourcePruningEnumerationInitialCarriers
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.SourcePruningResumeRefutation

/-!
# An original accepted term supplies the literal startup model

The original startup producer supplies its complete operational packet first.
An accepted root term then supplies a complete initial assignment.
The empty original pending list has no refutation obligations.
No template avoidance or program encoding follows from native acceptance.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Retain the full startup packet and derive its model from an original accepted term. -/
theorem initial_packet_models
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing) (value : Node)
    (context : Context formulas solver inventory caller memos)
    (available : Available caller.checked.native.machine.heap value)
    (closed : value.free = []) (emptyPending : metadata.pending = []) :
    ∃ handle,
      encodeNode value = some handle ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      let startup : Cached :=
        ⟨EnumerationState.initial handle,
          fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
          fun _ => none⟩
      ((Packet formulas solver inventory caller memos metadata startup ∧
      EnumerationValidity.Canonical startup.core ∧
      startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 ∧
      EnumerationCanonicalWaiting.Correct (fun uv => uv) startup.core.values startup.waiting ∧
      ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((startup.core.values[slot]?).getD .eliminated) = some (startup.expandable slot)) ∧
      EnumerationCarriers.CarriesGraph startup.core 0 ∧
      EnumerationGraphReferences.ReferencesCarry startup.core) ∧
      ∀ (holds : Constraint → Language.Term Symbol → Bool)
        (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop)
        (term : Language.Term Symbol),
        InternedGuardedLanguage.meaning holds ambient value term →
        ∃ assignment : Nat → Language.Term Symbol,
          assignment 0 = term ∧
          Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
            caller.checked.native.machine.heap) residualMeaning assignment startup.core ∧
          ∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group := by
  obtain ⟨handle, encoded, decoded, retained⟩ :=
    initial_packet_carriers formulas solver inventory caller memos metadata value
      context available closed emptyPending
  refine ⟨handle, encoded, decoded, retained, ?_⟩
  intro holds ambient residualMeaning term accepted
  refine ⟨(fun _ => term), rfl, ?_, ?_⟩
  · exact (EnumerationCorrectness.initial_semantics
      (SourcePruningEnumerationNativeLanguage.handles holds ambient caller.checked.native.machine.heap)
      residualMeaning (fun _ => term) handle).mpr
      ((SourcePruningEnumerationNativeLanguage.handles_lookup holds ambient
        caller.checked.native.machine.heap handle value term decoded).mpr accepted)
  · intro group member
    rw [emptyPending] at member
    exact False.elim (List.not_mem_nil member)

end MicroCFTA.SourcePruningEnumerationRecursive
