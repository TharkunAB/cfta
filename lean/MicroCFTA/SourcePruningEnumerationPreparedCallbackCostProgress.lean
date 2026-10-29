import MicroCFTA.SourcePruningEnumerationPreparedCallbackProgress
import MicroCFTA.SourcePruningRecordTypesRefutation
import MicroCFTA.SourcePruningEnumerationStorageCallbackProgress

/-!
# Model and cost at the actual prepared callback

One postcondition records the actual callback observation and its frame.
Original template policies preserve the same accepting assignment and cost.
The continuation uses the prepared worker's actual failure type.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningRecordTypes (recordTypes)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Refutes" => @SourcePruningResume.Refutes Symbol
  (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq)
variable {Typing : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- The actual recording call preserves the same model, strict cost and operational continuation. -/
def CallbackProgressAt
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol)
    (originalCost work : Nat) : Prop :=
  ∃ (recorded : Bool × Metadata Typing) (callbackCore : Core),
    Packet formulas solver inventory caller memos recorded.2 (EnumerationExpandableIndex.frame callbackCore before) ∧
    RenderStable before.core callbackCore ∧ Frame before.core callbackCore ∧
    Success (recordTypes graph templates work metadata uv (.inl fragment)) before.core recorded callbackCore ∧
    ExceptT.run (recordTypes graph templates work metadata uv (.inl fragment) before.core) =
      [.ok (recorded, callbackCore)] ∧
    recorded.1 = false ∧ (∀ group ∈ recorded.2.pending, Refutes assignment group) ∧
    EnumerationProgress.ProperState (EnumerationExpandableIndex.frame callbackCore before).core ∧
    Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
      assignment (EnumerationExpandableIndex.frame callbackCore before).core ∧
    EnumerationStorageProgress.pendingSize (EnumerationExpandableIndex.frame callbackCore before).core assignment + 1 ≤ originalCost ∧
    (∀ nextStop nextOrder, SourcePruningEnumerationRestart.decision nextStop nextOrder recorded.2
      (EnumerationExpandableIndex.frame callbackCore before) ≠ some .stuck) ∧
    ∀ (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result) nextStop nextOrder,
      continueWith recur graph templates nextStop nextOrder work metadata uv fragment caller memos.query before =
        recur recorded.2 caller memos.query (EnumerationExpandableIndex.frame callbackCore before)
          (SourcePruningEnumerationRestart.decision nextStop nextOrder recorded.2
            (EnumerationExpandableIndex.frame callbackCore before))

/-- An actual successful recording derives progress from original model, policy and cost facts. -/
theorem callback_progress_at_of_success
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (work : Nat) (recorded : Bool × Metadata Typing) (callbackCore : Core)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (proper : EnumerationProgress.ProperState before.core)
    (observed : Success (recordTypes graph templates work metadata uv (.inl fragment)) before.core recorded callbackCore)
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment before.core)
    (filled : Fragments.fill assignment fragment = assignment uv)
    (refuted : ∀ group ∈ metadata.pending, Refutes assignment group)
    (avoids : SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment))
    (encoded : ∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
      SourcePruningTemplates.ProgramEncoding program)
    (originalCost : Nat)
    (decrease : EnumerationStorageProgress.pendingSize before.core assignment + 1 ≤ originalCost) :
    CallbackProgressAt formulas solver inventory graph templates metadata uv fragment caller memos before
      ambient assignment originalCost work := by
  obtain ⟨returned, stable, framed, afterProper, afterSatisfied, _notStuck⟩ :=
    callback_record_progress formulas solver inventory graph templates metadata uv fragment caller memos before
      none (fun _ _ => none) work recorded callbackCore packet allocated proper observed ambient
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment satisfied
  have raw := SourcePruningCallbackExact.recordTypes_exact graph templates work metadata uv (.inl fragment)
    before.core callbackCore recorded observed
  have kept := SourcePruningRecordTypes.recordTypes_inl_refutes graph
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap)
    (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
    assignment templates work uv metadata fragment before.core callbackCore recorded packet.safe.1.total
    satisfied filled refuted avoids encoded observed
  have afterDecrease : EnumerationStorageProgress.pendingSize
      (EnumerationExpandableIndex.frame callbackCore before).core assignment + 1 ≤ originalCost := by
    change EnumerationStorageProgress.pendingSize callbackCore assignment + 1 ≤ _
    rw [EnumerationStorageProgress.frame_pendingSize before.core callbackCore assignment framed]
    exact decrease
  refine ⟨recorded, callbackCore, returned, stable, framed, observed, raw, kept.1, kept.2,
    afterProper, afterSatisfied, afterDecrease, ?_, ?_⟩
  · intro nextStop nextOrder
    exact SourcePruningEnumerationRestart.not_stuck_of_proper formulas solver nextStop nextOrder recorded.2 caller
      (EnumerationExpandableIndex.frame callbackCore before) returned.valid returned.safe afterProper
      ambient (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment afterSatisfied
  · intro recur nextStop nextOrder
    simp only [continueWith, raw]
    cases recorded with
    | mk rejected updated =>
        cases rejected
        · rfl
        · cases kept.1

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
