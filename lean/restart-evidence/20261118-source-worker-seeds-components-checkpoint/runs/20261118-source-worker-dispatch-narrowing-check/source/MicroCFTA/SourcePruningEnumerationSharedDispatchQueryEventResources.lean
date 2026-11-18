import MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents
import MicroCFTA.SourcePruningEnumerationSharedDispatchResources
import MicroCFTA.SourcePruningEnumerationSharedIncomingReservation

namespace MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourcePruningEnumerationObservation (PendingRealized)
open SourcePruningEnumerationSharedIncomingReservation (Seed Reserved)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Resources at the actual dispatch query event]
The observer records a query only after both pending handles decode.
The same two slot reads identify the operands of that exact event tuple.
PendingRealized supplies their availability and closedness in its input heap.
Context, Fits and the reserved query refer to that same input caller.
The query event remains present when the native or optional phase stops.
No returned endpoint or separate length-one witness supplies these facts.
-/

private theorem observe_operands_available
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller (bits + 2))
    (before : EnumerationState.State Symbol EnumGuard) (source target : Nat) (queries : Queries)
    (realized : PendingRealized caller.checked.native.machine.heap before) :
    ∀ start saved left right actual,
      (start, saved, left, right, actual) ∈
        (observe checkEmpty nativeFuel p h caller before source target queries).2 →
      Available caller.checked.native.machine.heap left ∧
      Available caller.checked.native.machine.heap right ∧
      left.free = [] ∧ right.free = []
 := by
  intro start saved left right actual member
  by_cases same : source = target
  · simp [observe, same] at member
  · cases sourceRead : before.values[source]? with
    | none => simp [observe, same, sourceRead] at member
    | some sourceValue =>
        cases sourceValue with
        | eliminated => simp [observe, same, sourceRead] at member
        | enumerated fragment =>
            cases targetRead : before.values[target]? <;>
              simp [observe, same, sourceRead, targetRead] at member
        | unenumerated sourceNode sourceScs =>
            cases targetRead : before.values[target]? with
            | none => simp [observe, same, sourceRead, targetRead] at member
            | some targetValue =>
                cases targetValue with
                | eliminated => simp [observe, same, sourceRead, targetRead] at member
                | enumerated fragment => simp [observe, same, sourceRead, targetRead] at member
                | unenumerated targetNode targetScs =>
                    cases sourceNode with
                    | none => simp [observe, same, sourceRead, targetRead] at member
                    | some sourceHandle =>
                        cases targetNode with
                        | none => simp [observe, same, sourceRead, targetRead] at member
                        | some targetHandle =>
                            cases leftRead : lookupNode caller.checked.native.machine.heap sourceHandle with
                            | none => simp [observe, same, sourceRead, targetRead, leftRead] at member
                            | some readLeft =>
                                cases rightRead : lookupNode caller.checked.native.machine.heap targetHandle with
                                | none => simp [observe, same, sourceRead, targetRead, leftRead, rightRead] at member
                                | some readRight =>
                                    obtain ⟨leftValue, leftDecoded, leftResident, leftClosed⟩ :=
                                      realized source sourceHandle sourceScs sourceRead
                                    have leftSame : leftValue = readLeft :=
                                      Option.some.inj (leftDecoded.symm.trans leftRead)
                                    subst leftValue
                                    obtain ⟨rightValue, rightDecoded, rightResident, rightClosed⟩ :=
                                      realized target targetHandle targetScs targetRead
                                    have rightSame : rightValue = readRight :=
                                      Option.some.inj (rightDecoded.symm.trans rightRead)
                                    subst rightValue
                                    cases nativeRead : SourceEqualityNativeDemand.execute nativeFuel
                                        (.code (SourceRecursiveIntersectionCode.requestNode
                                          IntersectionEmptyDomain.emptyDomain readLeft readRight)) caller.checked <;>
                                      simp [observe, same, sourceRead, targetRead,
                                        leftRead, rightRead, nativeRead, Prod.mk.injEq] at member <;>
                                      rcases member with ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
                                      exact ⟨leftResident, rightResident, leftClosed, rightClosed⟩

theorem observe_query_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2))
    (before : EnumerationState.State Symbol EnumGuard) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (realized : PendingRealized caller.checked.native.machine.heap before)
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed 1)
    (checkEmpty : Bool) (nativeFuel p h source target : Nat) :
    let observed := observe checkEmpty nativeFuel p h caller before source target memos.query
    observed.1 = SourcePruningEnumerationSharedDispatch.dispatch
      checkEmpty nativeFuel p h caller before source target memos.query ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      start = caller ∧ saved = memos.query ∧
      SourceCurrentConjunctionClassScan.Ready start.checked ∧
      Fits seed.2 start.checked ∧ SourceCurrentAllocatedNativeCreditProfile.Admits bits seed.2 ∧
      Available start.checked.native.machine.heap left ∧
      Available start.checked.native.machine.heap right ∧
      left.free = [] ∧ right.free = [] ∧
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
        start.checked
 := by
  dsimp only
  have receipt := observe_exact checkEmpty nativeFuel p h caller before source target memos.query
  refine ⟨receipt.1, ?_⟩
  intro start saved left right actual member
  obtain ⟨startSame, savedSame, actualSame⟩ := receipt.2.2.2 start saved left right actual member
  have operands := observe_operands_available checkEmpty nativeFuel p h caller before source target
    memos.query realized start saved left right actual member
  subst start
  exact ⟨rfl, savedSame, initial.ready, fits, reserved.head,
    operands.1, operands.2.1, operands.2.2.1, operands.2.2.2, actualSame⟩

end MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents

#print axioms MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents.observe_query_resources
