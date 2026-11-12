import MicroCFTA.SourcePruningEnumerationInitialOrigins
import MicroCFTA.SourcePruningEnumerationNativeWork

/-!
# Initial progress from an original accepted term

The original startup packet and assignment remain intact.
The pending potential equals the native size of the accepted root term.
This derives an initial witness bound. It does not bound later total work,
recursive depth, or erased Program size.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationStorageProgress
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

private theorem initial_pending (handle : Nat) (assignment : Nat → Term Symbol) :
    pendingSize (EnumerationState.initial handle : Core) assignment =
      NumberedTerms.size (assignment 0) := by
  rfl

private theorem initial_work (handle initialBound : Nat) (value : Node)
    (assignment : Nat → Term Symbol) :
    let startup : Cached :=
      ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
        fun _ => none⟩
    SourcePruningEnumerationNativeWork.work initialBound startup assignment =
      (initialBound + 1) * NumberedTerms.size (assignment 0) +
        (if MergedOrdinaryHeight.recursiveBoundary value then 0 else 1) := by
  change (initialBound + 1) * pendingSize (EnumerationState.initial handle : Core) assignment +
      (([0] : List Nat).filter
        (fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false)).length = _
  rw [initial_pending]
  cases MergedOrdinaryHeight.recursiveBoundary value <;> rfl

variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The same startup assignment supplies its original-term pending and work bounds. -/
theorem initial_packet_models_origins_work
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
      ∀ (holds : Constraint → Term Symbol → Bool)
        (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Term Symbol → Prop)
        (term : Term Symbol),
        InternedGuardedLanguage.meaning holds ambient value term →
        ∃ assignment : Nat → Term Symbol,
          assignment 0 = term ∧
          Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
            caller.checked.native.machine.heap) residualMeaning assignment startup.core ∧
          (∀ group ∈ metadata.pending, SourcePruningResume.Refutes assignment group) ∧
          SourcePruningEnumerationOrigins.AssignmentOrigins term startup.core.counter assignment ∧
          pendingSize startup.core assignment = NumberedTerms.size term ∧
          pendingSize startup.core assignment ≤ NumberedTerms.size term ∧
          SourcePruningEnumerationNativeWork.work (NumberedTerms.size term) startup assignment =
            (NumberedTerms.size term + 1) * NumberedTerms.size term +
              (if MergedOrdinaryHeight.recursiveBoundary value then 0 else 1) := by
  obtain ⟨handle, encoded, decoded, retained, models⟩ :=
    initial_packet_models_origins formulas solver inventory caller memos metadata value
      context available closed emptyPending
  refine ⟨handle, encoded, decoded, retained, ?_⟩
  intro holds ambient residualMeaning term accepted
  obtain ⟨assignment, rootTerm, satisfied, refuted, origins⟩ :=
    models holds ambient residualMeaning term accepted
  have pending : pendingSize (EnumerationState.initial handle : Core) assignment =
      NumberedTerms.size term := by
    rw [initial_pending, rootTerm]
  refine ⟨assignment, rootTerm, satisfied, refuted, origins, pending, Nat.le_of_eq pending, ?_⟩
  simpa only [rootTerm] using initial_work handle (NumberedTerms.size term) value assignment

end MicroCFTA.SourcePruningEnumerationRecursive
