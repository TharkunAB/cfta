import MicroCFTA.EnumerationExecution
import MicroCFTA.EnumerationPartialExact
import MicroCFTA.SourcePruningEnumerationRecursion
import MicroCFTA.SourcePruningEnumerationNativeIndexStability
import MicroCFTA.SourcePruningEnumerationParkedRestart
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationObservedPrefixFuel
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {EnumGuard NativeGuard : Type}
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- A successful read retains its complete raw result at a larger bound. -/
private theorem getValue_success_raw_moreFuel
    (fuel extra uv : Nat) (before after : EnumerationState.State Symbol EnumGuard)
    (value : UVarValue Symbol)
    (observed : Success (getValue fuel uv) before value after) :
    ExceptT.run (getValue (fuel + extra) uv before) =
      ExceptT.run (getValue fuel uv before) := by
  have retained := EnumerationExecution.getValue_moreFuel fuel extra uv before value after observed
  exact (EnumerationPartialExact.getValue_exact (fuel + extra) uv before after value retained).trans
    (EnumerationPartialExact.getValue_exact fuel uv before after value observed).symm

/-- A successful native recursion check retains its complete raw result. -/
private theorem checkRepeated_success_raw_moreFuel
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel extra uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard) (repeated : Bool)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before repeated after) :
    ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated heap
      (fuel + extra) uv handle scs before) =
      ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs before) := by
  cases decoded : lookupNode heap handle with
  | none => simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded]
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, reading, _continued⟩ := (success_bind _ _ _ _ _).mp observed
        have retained := EnumerationExecution.representative_moreFuel fuel extra uv
          before root resolved reading
        have oldExact := EnumerationPartialExact.representative_success_exact
          fuel uv before resolved root reading
        have newExact := EnumerationPartialExact.representative_success_exact
          (fuel + extra) uv before resolved root retained
        simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte]
        rw [bind_single _ _ before resolved root newExact,
          bind_single _ _ before resolved root oldExact]
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte]

/-- A successful indexed parked adapter retains its exact cached endpoint. -/
private theorem parked_adapt_some_moreFuel
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel extra uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (checked : EnumerationState.State Symbol Constraint)
    (observed : SourcePruningEnumerationParkedRestart.adapt heap fuel uv handle scs
      before checked = some after) :
    SourcePruningEnumerationParkedRestart.adapt heap (fuel + extra) uv handle scs
      before checked = some after := by
  unfold SourcePruningEnumerationParkedRestart.adapt at observed ⊢
  rw [Option.map_eq_some_iff] at observed ⊢
  obtain ⟨saved, written, mapped⟩ := observed
  exact ⟨saved, SourcePruningEnumerationNativeIndex.write_some_moreFuel heap fuel extra uv
    (.unenumerated (some handle) []) [] scs
    (EnumerationExpandableIndex.frame checked before) saved written, mapped⟩

end MicroCFTA.SourcePruningEnumerationObservedPrefixFuel

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Observation" => ChildDispatch.Observation
variable {width : Nat}
local notation "Fold" => NativeContinuations.Result (Output width Unit) (Failure width Unit) width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Fold) →
  (Observation width → Option Cached → Fold) → Fold
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The actual worker stops with no outputs on either unsupported prefix form. -/
private theorem unsupported_prefix_stops
    (child : Visitor)
    (narrow : Metadata Unit → Nat → Nat → Node →
      InternedConstructorTemplates.State Symbol Constraint →
      MergedSourceComparison.Result Symbol Constraint Node)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Unit → Nat → Bool))
    (order : Metadata Unit → List Nat → Option Nat)
    (workFuel recursiveFuel uv : Nat)
    (metadata : Metadata Unit) (caller : Caller width) (queries : Queries) (before : Cached)
    (observed : SourcePruningEnumerationSelectedStep.Result width Unit)
    (observing : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow narrow graph templates
      stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel
      uv caller before queries = observed)
    (unsupported : match observed with
      | .stopped _ _ => True
      | .parked _ none _ => True
      | _ => False) :
    resumeWithNarrow child narrow graph templates checkEmpty edgesOf stop order workFuel
      (recursiveFuel + 1) metadata caller queries before (some (.expand uv)) =
      .stopped [] (.selected uv observed) (some (caller, queries)) := by
  cases observed with
  | stopped reading checking => simp only [resumeWithNarrow, observing]
  | parked checked candidate raw =>
      cases candidate with
      | none => simp only [resumeWithNarrow, observing]
      | some saved => cases unsupported
  | narrowed checked prepared reached saved action candidate right ordinary => cases unsupported

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

namespace MicroCFTA.SourcePruningEnumerationObservedPrefixFuel
#print axioms getValue_success_raw_moreFuel
#print axioms checkRepeated_success_raw_moreFuel
#print axioms parked_adapt_some_moreFuel
end MicroCFTA.SourcePruningEnumerationObservedPrefixFuel
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
#print axioms unsupported_prefix_stops
end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
