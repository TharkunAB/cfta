import MicroCFTA.SourcePruningEnumerationPreparedFiniteResources
import MicroCFTA.SourcePruningEnumerationPreparedFiniteReceiptResources
import MicroCFTA.SourcePruningEnumerationPreparedCallbackModels

/-!
# Original models at the actual prepared receipt restart

The original receipt resource producer fixes its actual outcome once.
The completed receipt supplies the actual callback input packet.
One common work bound aligns that outcome with the original-model callback.
No model of recursive outputs is an input or a conclusion.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open EnumerationSchedule InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory)
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- Preserve the complete receipt resources and derive its actual original-model restart. -/
theorem receipt_finite_complete_resources_models
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat)
    (original next : Inventory) (caller reached : Caller (bits + 2)) (memos final : Memos) (before : Cached)
    (uv : Nat) (receipt : Receipt (bits + 2))
    (packet : Packet formulas solver original caller memos metadata before)
    (post : Post formulas solver next caller reached final)
    (advanced : advance receipt = some (reached, final.query))
    (admitted : Admitted uv receipt) (pending : Pending receipt) (history : FragmentHistory before.core receipt)
    (seed : Seed) (ceiling : Nat)
    (bounded : Fits seed.2 reached.checked) (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : match (generalizing := false) receipt with
      | .complete _ _ _ after => SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling
      | _ => True)
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ (fuel : Nat) (outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      ((∀ extra, match (generalizing := false) receipt with
        | .complete fragment actual saved after =>
            continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
              graph templates stop order (fuel + extra) metadata uv fragment actual saved after = outcome
        | _ => outcome = .complete [] reached final.query) ∧
      OutcomeResources formulas solver reached
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome) ∧
      match (generalizing := false) receipt with
      | .complete fragment actual saved afterCache =>
          actual = reached ∧ saved = final.query ∧
          ∃ (recorded : Bool × Metadata Typing) (callbackCore : Core),
            Packet formulas solver next actual final metadata afterCache ∧
            FragmentBound afterCache.core.counter fragment ∧
            (Packet formulas solver next actual final recorded.2 (EnumerationExpandableIndex.frame callbackCore afterCache) ∧
            RenderStable afterCache.core callbackCore ∧ Frame afterCache.core callbackCore ∧
            recorded.2.types = updatedTypes metadata uv (.inl fragment) ∧
            recorded.2.openHoles = metadata.openHoles ∧ recorded.2.typing = metadata.typing ∧
            (∀ extra,
              Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) afterCache.core recorded callbackCore ∧
              ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) afterCache.core) =
                [.ok (recorded, callbackCore)] ∧
              ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result) stop order,
                continueWith recur graph templates stop order (fuel + extra) metadata uv fragment actual final.query afterCache =
                  if recorded.1 then .complete [] actual final.query
                  else recur recorded.2 actual final.query (EnumerationExpandableIndex.frame callbackCore afterCache)
                    (SourcePruningEnumerationRestart.decision stop order recorded.2
                      (EnumerationExpandableIndex.frame callbackCore afterCache))) ∧
            (∀ extra, continueWith
              (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
              graph templates stop order (fuel + extra) metadata uv fragment actual final.query afterCache = outcome) ∧
            OutcomeResources formulas solver actual
              (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome) ∧
            (∀ (language : NodeLanguage Symbol)
              (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
              Satisfies language meaning assignment (EnumerationExpandableIndex.frame callbackCore afterCache).core ↔
                Satisfies language meaning assignment afterCache.core) ∧
            ∀ (language : NodeLanguage Symbol)
              (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
              Satisfies language meaning assignment afterCache.core →
              Fragments.fill assignment fragment = assignment uv →
              (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
                (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) →
              SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment) →
              (∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
                SourcePruningTemplates.ProgramEncoding program) →
              Satisfies language meaning assignment (EnumerationExpandableIndex.frame callbackCore afterCache).core ∧
                recorded.1 = false ∧
                (∀ group ∈ recorded.2.pending, @SourcePruningResume.Refutes Symbol
                (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) ∧
                ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                    (fuel + extra) recursiveFuel recorded.2 actual final.query
                    (EnumerationExpandableIndex.frame callbackCore afterCache)
                    (SourcePruningEnumerationRestart.decision stop order recorded.2
                      (EnumerationExpandableIndex.frame callbackCore afterCache)) = outcome
      | _ => True := by
  have recursive := SourcePruningEnumerationPreparedRecursive.finite_complete
    (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
  obtain ⟨receiptFuel, outcome, receiptRunning, receiptResources⟩ := receipt_finite_complete_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver recursiveFuel
    recursive original next caller reached memos final before uv receipt packet post advanced admitted pending history
    seed ceiling bounded known selectionMembers selectionLength mass reserved
  cases receipt with
  | unhandled => cases advanced
  | rejected actual saved after | stopped fragments observation candidate =>
      exact ⟨receiptFuel, outcome, ⟨receiptRunning, receiptResources⟩, True.intro⟩
  | complete fragment actual saved afterCache =>
      have endpoints : (actual, saved) = (reached, final.query) := Option.some.inj advanced
      obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
      subst actual
      subst saved
      obtain ⟨level, frontier, ordered⟩ := packet.ordered
      have current := SourcePruningEnumerationRecursive.receipt_packet before.core uv fragment afterCache
        level frontier post.context admitted history pending ordered packet.bounded
      have allocated : FragmentBound afterCache.core.counter fragment := admitted.2.2.1
      obtain ⟨callbackFuel, recorded, callbackCore, callbackOutcome, returned, equivalence, models⟩ :=
        callback_finite_complete_resources_models holeKey fits admits formulas solver next graph templates metadata
          uv fragment reached final afterCache checkEmpty edgesOf stop order recursiveFuel seed ceiling
          current allocated bounded known selectionMembers selectionLength mass reserved
      obtain ⟨callbackPacket, stable, framed, types, holes, typing, callback, callbackRunning, callbackResources⟩ := returned
      have sameOutcome : callbackOutcome = outcome := by
        have oldRun := receiptRunning callbackFuel
        have modelRun := callbackRunning receiptFuel
        rw [Nat.add_comm callbackFuel receiptFuel] at modelRun
        exact modelRun.symm.trans oldRun
      subst callbackOutcome
      refine ⟨receiptFuel + callbackFuel, outcome, ⟨?_, receiptResources⟩,
        rfl, rfl, recorded, callbackCore, current, allocated,
        ⟨callbackPacket, stable, framed, types, holes, typing, ?_, ?_, callbackResources⟩,
        equivalence, ?_⟩
      · intro extra
        have actual := receiptRunning (callbackFuel + extra)
        rw [← Nat.add_assoc] at actual
        exact actual
      · intro extra
        have actual := callback (receiptFuel + extra)
        have common : callbackFuel + (receiptFuel + extra) = receiptFuel + callbackFuel + extra := by omega
        rw [common] at actual
        exact actual
      · intro extra
        have actual := callbackRunning (receiptFuel + extra)
        have common : callbackFuel + (receiptFuel + extra) = receiptFuel + callbackFuel + extra := by omega
        rw [common] at actual
        exact actual
      · intro language meaning assignment satisfied filled refuted avoids encoded
        obtain ⟨afterSatisfied, notRejected, pendingRefutes, restarting⟩ :=
          models language meaning assignment satisfied filled refuted avoids encoded
        refine ⟨afterSatisfied, notRejected, pendingRefutes, ?_⟩
        intro extra
        have actual := restarting (receiptFuel + extra)
        have common : callbackFuel + (receiptFuel + extra) = receiptFuel + callbackFuel + extra := by omega
        rw [common] at actual
        exact actual

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
