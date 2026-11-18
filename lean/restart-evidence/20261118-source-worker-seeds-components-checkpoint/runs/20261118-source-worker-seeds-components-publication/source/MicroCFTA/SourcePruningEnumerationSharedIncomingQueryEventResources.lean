import MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEvents
import MicroCFTA.SourcePruningEnumerationSharedIncomingNodeResources
import MicroCFTA.SourcePruningEnumerationSharedIncomingReservation

namespace MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEvents
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
local notation "NativeOutcome" => SourceEqualityNativeDemand.Outcome
local notation "Observed" => SourcePruningEnumerationSharedEnabledEmpty.Outcome
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Resources at the actual incoming query event]
The observer records the original query input before inspecting its outcome.
The literal pending slot identifies that same event's old operand.
PendingRealized supplies availability and closedness in the same input heap.
The current Context, Fits and reservation apply at that event's input caller.
Native errors and enabled-empty errors retain their recorded query event.
No returned endpoint is used to infer an earlier input invariant.
-/

private theorem observe_right_available
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (beforeCaller : Caller (bits + 2)) (before : EnumerationState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before) :
    ∀ start saved left right actual,
      (start, saved, left, right, actual) ∈
        (observe checkEmpty representativeFuel nativeFuel p h
          beforeCaller before uv incoming incomingScs queries).2 →
      Available beforeCaller.checked.native.machine.heap right ∧ right.free = []
 := by
  intro start saved left right actual member
  cases rootRead : UnionFind.findRoot representativeFuel before.representatives uv with
  | none => simp [observe, rootRead] at member
  | some found =>
      cases slotRead : before.values[found.representative]? with
      | none => simp [observe, rootRead, slotRead] at member
      | some value =>
          cases value with
          | eliminated => simp [observe, rootRead, slotRead] at member
          | enumerated fragment => simp [observe, rootRead, slotRead] at member
          | unenumerated oldNode oldScs =>
              cases oldNode with
              | none =>
                  cases encoded : encodeNode incoming <;>
                    simp [observe, rootRead, slotRead, encoded] at member
              | some oldHandle =>
                  cases oldRead : lookupNode beforeCaller.checked.native.machine.heap oldHandle with
                  | none => simp [observe, rootRead, slotRead, oldRead] at member
                  | some old =>
                      obtain ⟨value, decoded, resident, oldClosed⟩ :=
                        realized found.representative oldHandle oldScs slotRead
                      have same : value = old := Option.some.inj (decoded.symm.trans oldRead)
                      subst value
                      cases nativeRead : SourceEqualityNativeDemand.execute nativeFuel
                          (.code (SourceRecursiveIntersectionCode.requestNode
                            IntersectionEmptyDomain.emptyDomain incoming old)) beforeCaller.checked <;>
                        simp only [observe, rootRead, slotRead, oldRead, nativeRead] at member <;>
                        try (simp only [List.mem_singleton, Prod.mk.injEq] at member
                             rcases member with ⟨rfl, rfl, rfl, rfl, rfl⟩
                             exact ⟨resident, oldClosed⟩)
                      case done query queried =>
                        generalize phaseRead : (if checkEmpty then
                          SourcePruningEnumerationSharedEnabledEmpty.check p h query queried beforeCaller.fourth queries
                          else (.skipped queried beforeCaller.fourth, queries) :
                            Observed (bits + 2) × Queries) = phase at member
                        cases completed : phase.1.completed with
                        | none =>
                            simp only [completed, List.mem_singleton, Prod.mk.injEq] at member
                            rcases member with ⟨rfl, rfl, rfl, rfl, rfl⟩
                            exact ⟨resident, oldClosed⟩
                        | some answer =>
                            simp only [completed] at member
                            cases encoded : encodeNode (if answer then .empty else query) <;>
                              simp only [encoded, List.mem_singleton, Prod.mk.injEq] at member <;>
                              rcases member with ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
                              exact ⟨resident, oldClosed⟩

theorem observe_query_resources
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationState.State Symbol EnumGuard) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed 1)
    (checkEmpty : Bool) (representativeFuel nativeFuel p h uv : Nat)
    (incoming : Node) (incomingScs : List Suspended)
    (available : Available beforeCaller.checked.native.machine.heap incoming)
    (closed : incoming.free = []) :
    let observed := observe checkEmpty representativeFuel nativeFuel p h
      beforeCaller before uv incoming incomingScs memos.query
    observed.1 = SourcePruningEnumerationSharedIncomingNode.run
      checkEmpty representativeFuel nativeFuel p h
      beforeCaller before uv incoming incomingScs memos.query ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      start = beforeCaller ∧ saved = memos.query ∧ left = incoming ∧
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
  have receipt := observe_exact checkEmpty representativeFuel nativeFuel p h
    beforeCaller before uv incoming incomingScs memos.query
  refine ⟨receipt.1, ?_⟩
  intro start saved left right actual member
  obtain ⟨startSame, savedSame, leftSame, actualSame⟩ :=
    receipt.2.2.2 start saved left right actual member
  have rightFacts := observe_right_available checkEmpty representativeFuel nativeFuel p h
    beforeCaller before uv incoming incomingScs memos.query realized
    start saved left right actual member
  subst start
  subst left
  exact ⟨rfl, savedSame, rfl, initial.ready, fits, reserved.head,
    available, rightFacts.1, closed, rightFacts.2, actualSame⟩

end MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEvents
