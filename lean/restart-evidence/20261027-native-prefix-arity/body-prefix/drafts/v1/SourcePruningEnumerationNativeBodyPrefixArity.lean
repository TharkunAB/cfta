import MicroCFTA.SourcePruningEnumerationNativeNodePrefixArity

/-!
# Arity through actual checked native edge-body prefixes

The actual body prefix can stop before a child returns.
Completed earlier children use the completed query theorem.
Only the current child uses the bounded prefix condition.
The final constructor uses the actual ready guard and child count.
-/
namespace MicroCFTA.SourcePruningEnumerationNativePrefixArity
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourcePruningEnumerationArityOrigins (Fits Heap edge_heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {A : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem pure_prefix_heap (value : A) (fuel : Nat) (before after : Checked width)
    (remaining : Control A) (actual : Trace fuel (.code (.pure value)) before remaining after)
    (heap : Heap before.native.machine.heap) : Heap after.native.machine.heap := by
  cases actual with
  | refl => exact heap
  | cons control state next middle final result count inputs one tail => cases one

private theorem edge_work_prefix_heap (symbol : Symbol) (constraint : Guard)
    (children : List (Value Symbol Guard)) (fuel : Nat) (before after : Checked width)
    (remaining : Control (EdgeValue Symbol Guard))
    (heap : Heap before.native.machine.heap) (checked : Fits constraint children.length)
    (actual : Trace fuel (.code (.work (makeEdge symbol constraint children) .pure)) before remaining after) :
    Heap after.native.machine.heap := by
  cases actual with
  | refl => exact heap
  | cons control state next middle final result count inputs one tail =>
      cases one
      exact pure_prefix_heap _ count _ after remaining tail
        (edge_heap symbol constraint children before.native.machine.heap heap checked)

private theorem top_fits (arity : Nat) : Fits (top : Guard) arity := by
  intro tries residual projected start
  have topProjection : SourcePruningEnumerationConstraint.project (top : Guard) = some ([], none) := rfl
  rw [topProjection] at projected
  have triesSame : [] = tries := congrArg Prod.fst (Option.some.inj projected)
  subst tries
  rfl

/-- Every actual body prefix retains the entire arity heap at its exact remaining control. -/
theorem body_prefix_heap
    (limit : Nat)
    (calls : ∀ (request : NodeRequest Symbol Guard) (count : Nat), count ≤ limit →
      ∀ (start final : Checked width) (remaining : Control (Value Symbol Guard)), Good start →
        Heap start.native.machine.heap →
        Trace count (.code (requestNode request.domain request.left request.right)) start remaining final →
        Heap final.native.machine.heap)
    (request : EdgeRequest Symbol Guard) (fuel : Nat) (before after : Checked width)
    (remaining : Control (EdgeValue Symbol Guard)) (bounded : fuel ≤ limit)
    (valid : Good before) (inputs : EdgeReady before.native.machine request)
    (heap : Heap before.native.machine.heap)
    (actual : Trace fuel (.edgeBody request .pure) before remaining after) :
    Heap after.native.machine.heap := by
  cases actual with
  | refl => exact heap
  | cons control state next started final result rest _operands one tail =>
      obtain ⟨code, same⟩ := SourceEqualityNativeDemandBodyYield.pure_yielded_code
        request before started next one
      subst next
      have firstTrace : Trace 1 (.edgeBody request .pure) before (.code code) started :=
        .cons _ _ _ _ _ _ 0 (by trivial) one (.refl _ _)
      have startedEffects := SourceCurrentAllocatedNativeSemanticTraceReadback.effects firstTrace valid
        (show Fields (.edgeBody request .pure) before from ⟨inputs, fun _ => trivial⟩)
      obtain ⟨nativeSame, branch⟩ :=
        SourcePruningEnumerationNativeCheckedOriginArity.body_choice_checked request before started code one
      have startedHeap : Heap started.native.machine.heap := by rw [nativeSame]; exact heap
      rcases branch with sentinelSame | ⟨first, second, combined, left, right, accepted, codeSame⟩
      · have workTrace : Trace rest
            (.code (.work (makeEdge request.left.entry.key.symbol top [.empty]) .pure)) started remaining after := by
          simpa only [sentinelSame, SourceEqualityNativeCheckedCode.sentinel] using tail
        exact edge_work_prefix_heap request.left.entry.key.symbol top [.empty] rest started after remaining
          startedHeap (top_fits _) workTrace
      · let call := fun pair : Value Symbol Guard × Value Symbol Guard =>
          requestNode request.domain pair.1 pair.2
        let children := request.left.children.zip request.right.children
        let finish := fun values : List (Value Symbol Guard) =>
          .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure
        have childTrace : Trace rest ((.code (walk call children) : Control (List (Value Symbol Guard))).bind finish)
            started remaining after := by
          simpa only [codeSame, SourceEqualityNativeCheckedCode.children, Control.bind, call, children, finish] using tail
        have completed : ∀ (pair : Value Symbol Guard × Value Symbol Guard) (count : Nat), count ≤ limit →
            ∀ (start final : Checked width) (value : Value Symbol Guard), Good start →
              Heap start.native.machine.heap → Trace count (.code (call pair)) start (.code (.pure value)) final →
              Heap final.native.machine.heap := by
          intro pair count _bounded start final value good current called
          exact SourcePruningEnumerationNativeQueryArity.node_query_heap
            ⟨request.domain, pair.1, pair.2⟩ start final value count good current called
        have fields : ∀ (pair : Value Symbol Guard × Value Symbol Guard) (state : Checked width),
            Fields (.code (call pair)) state := fun _ _ => fun _ => trivial
        rcases SourceCurrentNativeTracePrefixBind.bind_prefix_cases rest (.code (walk call children)) finish
            started after remaining childTrace with
          ⟨inner, walked, _nonpure, _same⟩ |
          ⟨walkFuel, outerFuel, values, middle, total, walked, later⟩
        · exact walk_prefix_heap limit call completed
            (fun pair count bound start final rest good current called =>
              calls ⟨request.domain, pair.1, pair.2⟩ count bound start final rest good current called)
            fields children rest started after inner (by omega) startedEffects.1 startedHeap walked
        · have earlier := SourceCurrentAllocatedNativeSemanticTraceReadback.walk_readback
            call children walkFuel started middle values walked
          have middleHeap := SourcePruningEnumerationNativeQueryArity.walk_heap limit call completed fields
            children values started middle walkFuel (by omega) startedEffects.1 startedHeap earlier
          have arity : request.left.children.length = request.right.children.length := by
            by_cases equal : request.left.children.length = request.right.children.length
            · exact equal
            · have impossible := congrArg Prod.fst
                (SourceEqualityIntersectionEdgeAllocation.run_mismatch GuardStructuralOrder.le first second
                  request.left.children.length request.right.children.length before.operations equal)
              rw [accepted] at impossible
              cases impossible
          have lengthSame : values.length = request.left.children.length := by
            rw [SourcePruningEnumerationNativeBodyTrace.walk_length earlier, List.length_zip, arity, Nat.min_self]
          have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.operations.constraints
            (valid.fields _ _ inputs.2.1).1 first left).1
          have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ valid.operations.constraints
            (valid.fields _ _ inputs.2.2).1 second right).1
          have checked := SourcePruningEnumerationNativeCheckedOriginArity.ready_fits
            GuardStructuralOrder.le first second combined request.left.children.length request.right.children.length
            before.operations valid.operations firstReady secondReady accepted
          rw [← lengthSame] at checked
          exact edge_work_prefix_heap request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined)
            values outerFuel middle after remaining middleHeap checked later

end MicroCFTA.SourcePruningEnumerationNativePrefixArity
