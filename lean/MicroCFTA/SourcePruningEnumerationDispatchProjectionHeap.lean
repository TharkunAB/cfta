import MicroCFTA.SourcePruningEnumerationDispatchResources
import MicroCFTA.SourcePruningEnumerationIncomingQueryProjectionHeap

/-!
# Projection heaps at actual dispatcher returns

Branches without native queries retain the original physical heap.
The actual completed query and optional Empty check retain their reached heap.
Missing actions remain distinct from outer native errors.
-/
namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "forecast" => SourcePruningEnumerationIncomingQuery.forecast
local notation "queryAlphabet" => SourceCurrentGeneratedQueryGuardResources.forecast
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
variable {EnumGuard : Type} {bits : Nat}
local notation "Core" => EnumerationState.State Symbol EnumGuard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]

variable [DecidableEq Node]

/-- Each actual outer success retains its original resource pair and reached projection heap. -/
theorem observed_resources_projection_heap (alphabet : List Constraint) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Core)
    (checkEmpty : Bool) (nativeFuel p h source target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap)
    (originalProjection : ProjectionHeap beforeCaller.checked.native.machine.heap)
    {result : Option (EnumerateM Symbol EnumGuard Unit)}
    {afterCaller : Caller (bits + 2)} {savedQueries : Queries}
    (observed : dispatch checkEmpty nativeFuel p h beforeCaller before source target memos.query =
      (.ok result, afterCaller, savedQueries)) :
    Fits (forecast alphabet profile) afterCaller.checked ∧
      Heap (fun guard => guard ∈ queryAlphabet alphabet profile) afterCaller.checked.native.machine.heap ∧
      ProjectionHeap afterCaller.checked.native.machine.heap := by
  have unchanged : Fits (forecast alphabet profile) beforeCaller.checked ∧
      Heap (fun guard => guard ∈ queryAlphabet alphabet profile) beforeCaller.checked.native.machine.heap ∧
      ProjectionHeap beforeCaller.checked.native.machine.heap := by
    refine ⟨fits.mono (SourcePruningEnumerationIncomingQuery.forecast_ge alphabet profile), ?_, originalProjection⟩
    intro key edge found
    exact SourceCurrentGeneratedQueryGuardResources.forecast_ge alphabet profile (known key edge found)
  simp only [dispatch, Id.run] at observed
  by_cases same : source = target
  · simp only [ite_eq_left same] at observed
    have callerSame := congrArg (fun output => output.2.1) observed
    dsimp only at callerSame
    rw [← callerSame]
    exact unchanged
  · simp only [ite_eq_right same] at observed
    cases sourceStored : before.values[source]? with
    | none =>
        simp only [sourceStored] at observed
        have callerSame := congrArg (fun output => output.2.1) observed
        dsimp only at callerSame
        rw [← callerSame]
        exact unchanged
    | some sourceValue =>
        cases sourceValue with
        | eliminated =>
            simp only [sourceStored] at observed
            have callerSame := congrArg (fun output => output.2.1) observed
            dsimp only at callerSame
            rw [← callerSame]
            exact unchanged
        | enumerated _fragment =>
            cases targetStored : before.values[target]? <;>
              simp only [sourceStored, targetStored] at observed <;>
              have callerSame := congrArg (fun output => output.2.1) observed <;>
              dsimp only at callerSame <;>
              rw [← callerSame] <;> exact unchanged
        | unenumerated sourceNode sourceScs =>
            simp only [sourceStored] at observed
            cases targetStored : before.values[target]? with
            | none =>
                simp only [targetStored] at observed
                have callerSame := congrArg (fun output => output.2.1) observed
                dsimp only at callerSame
                rw [← callerSame]
                exact unchanged
            | some targetValue =>
                cases targetValue with
                | eliminated | enumerated =>
                    simp only [targetStored] at observed
                    have callerSame := congrArg (fun output => output.2.1) observed
                    dsimp only at callerSame
                    rw [← callerSame]
                    exact unchanged
                | unenumerated targetNode targetScs =>
                    simp only [targetStored] at observed
                    cases sourceNode with
                    | none =>
                        have callerSame := congrArg (fun output => output.2.1) observed
                        dsimp only at callerSame
                        rw [← callerSame]
                        exact unchanged
                    | some leftHandle =>
                        cases targetNode with
                        | none =>
                            have callerSame := congrArg (fun output => output.2.1) observed
                            dsimp only at callerSame
                            rw [← callerSame]
                            exact unchanged
                        | some rightHandle =>
                            cases leftLookup : lookupNode beforeCaller.checked.native.machine.heap leftHandle with
                            | none =>
                                simp only [leftLookup] at observed
                                have callerSame := congrArg (fun output => output.2.1) observed
                                dsimp only at callerSame
                                rw [← callerSame]
                                exact unchanged
                            | some left =>
                                simp only [leftLookup] at observed
                                cases rightLookup : lookupNode beforeCaller.checked.native.machine.heap rightHandle with
                                | none =>
                                    simp only [rightLookup] at observed
                                    have callerSame := congrArg (fun output => output.2.1) observed
                                    dsimp only at callerSame
                                    rw [← callerSame]
                                    exact unchanged
                                | some right =>
                                    obtain ⟨first, firstLookup, leftAvailable, leftClosed⟩ :=
                                      realized source leftHandle sourceScs sourceStored
                                    obtain ⟨second, secondLookup, rightAvailable, rightClosed⟩ :=
                                      realized target rightHandle targetScs targetStored
                                    have firstSame := Option.some.inj (firstLookup.symm.trans leftLookup)
                                    have secondSame := Option.some.inj (secondLookup.symm.trans rightLookup)
                                    subst first
                                    subst second
                                    simp only [rightLookup] at observed
                                    cases native : SourceEqualityNativeDemand.execute nativeFuel
                                        (.code (SourceRecursiveIntersectionCode.requestNode
                                          IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked with
                                    | yielded | failed | constraintError | blocked =>
                                        simp only [native] at observed
                                        cases observed
                                    | done query queried =>
                                        simp only [native, afterQuery] at observed
                                        cases phase : (if checkEmpty then
                                            SourcePruningEnumerationEnabledEmpty.check p h query queried
                                              beforeCaller.fourth memos.query
                                            else (.done false queried beforeCaller.fourth, memos.query)) with
                                        | mk outcome queries =>
                                            simp only [phase] at observed
                                            cases outcome with
                                            | failed =>
                                                simp only [Except.mapError] at observed
                                                cases observed
                                            | done answer checkedAfter saved =>
                                                have bounded := SourcePruningEnumerationIncomingQuery.raw_done_resources_projection_heap
                                                  alphabet profile formulas solver inventory beforeCaller left right
                                                  checkEmpty memos initial leftAvailable rightAvailable leftClosed
                                                  rightClosed fits room known originalProjection native phase
                                                simp only [Except.mapError] at observed
                                                have callerSame := congrArg (fun output => output.2.1) observed
                                                dsimp only at callerSame
                                                rw [← callerSame]
                                                exact ⟨bounded.1, bounded.2.1, bounded.2.2.1⟩


end MicroCFTA.SourcePruningEnumerationDispatch
