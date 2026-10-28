import MicroCFTA.SourcePruningEnumerationPreparedRecursive
import MicroCFTA.SourcePruningEnumerationRecursiveCallback
import MicroCFTA.SourcePruningEnumerationNativeProgress

/-!
# Progress at the actual prepared recording callback

The original callback packet supplies one complete recording result.
Exact recording observations identify any actual successful call with it.
The original proper model excludes a stuck restart at the actual frame.
No recursive output or output history is required.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]

/-- An actual successful recording call retains the original packet and excludes stuck restart. -/
theorem callback_record_progress
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (result : Bool × Metadata Typing) (after : Core)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (proper : EnumerationProgress.ProperState before.core)
    (observed : Success (recordTypes graph templates fuel metadata uv (.inl fragment))
      before.core result after)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : Constraint → Language.Term Symbol → Prop)
    (assignment : Nat → Language.Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap) meaning assignment before.core) :
    Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      EnumerationProgress.ProperState (EnumerationExpandableIndex.frame after before).core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap) meaning assignment
        (EnumerationExpandableIndex.frame after before).core ∧
      SourcePruningEnumerationRestart.decision stop order result.2
        (EnumerationExpandableIndex.frame after before) ≠ some .stuck := by
  obtain ⟨producedFuel, producedResult, producedAfter, returned, stable, framed,
    _types, _holes, _typing, callback⟩ :=
    SourcePruningEnumerationRecursive.callback_complete formulas solver inventory graph templates
      metadata uv fragment caller memos before packet allocated
  have actualMore := recordTypes_moreFuel graph templates fuel producedFuel metadata uv (.inl fragment)
    before.core result after observed
  have exactActual := SourcePruningCallbackExact.recordTypes_exact graph templates (fuel + producedFuel)
    metadata uv (.inl fragment) before.core after result actualMore
  have exactProduced := (callback fuel).2.1
  rw [Nat.add_comm producedFuel fuel] at exactProduced
  have pairSame := Except.ok.inj (List.cons.inj (exactProduced.symm.trans exactActual)).1
  obtain ⟨resultSame, afterSame⟩ := Prod.mk.inj pairSame
  cases resultSame
  cases afterSame
  have afterProper : EnumerationProgress.ProperState
      (EnumerationExpandableIndex.frame after before).core := by
    change EnumerationProgress.ProperState after
    simpa only [EnumerationProgress.ProperState, framed.values] using proper
  have afterSatisfied := (SourcePruningEnumerationNativeLanguage.satisfies_frame
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap) meaning assignment before.core after framed).mpr satisfied
  exact ⟨returned, stable, framed, afterProper, afterSatisfied,
    SourcePruningEnumerationRestart.not_stuck_of_proper formulas solver stop order result.2 caller
      (EnumerationExpandableIndex.frame after before) returned.valid returned.safe afterProper
      ambient meaning assignment afterSatisfied⟩

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
