import MicroCFTA.SourceEqualityNativeCheckedWidth
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion
import MicroCFTA.SourceEqualityNativeDemandControl
import MicroCFTA.SourceEqualityNativeDemandRejectedReceipt

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace MicroCFTA.CheckedWidthKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionCodeMass (At)
open SourceEqualityNativeCheckedWidth
open InternedFreshOrdinaryResultMass (inflate)
local notation "Stored" => InternedValueMassHeap.Stored
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

private theorem node_suffix [DecidableEq (EdgeKey Symbol Guard)] (edge : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard) (bound : Nat) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (stored : Stored bound state.heap) (resident : EdgeResident state.heap edge) :
    At (.work (makeNode [edge]) .pure) state bound (fun after value => Available after.heap value) := by
  apply SourceRecursiveIntersectionCodeMass.node [edge] state bound valid
  · intro actual member
    exact List.mem_singleton.mp member ▸ resident
  · have square := Nat.mul_le_mul_left bound stored.positive
    simp only [Nat.mul_one] at square
    exact Nat.le_trans stored.positive square

/-- An own two-child edge certifies the whole accepted walk and node suffix before any recursive result exists. -/
theorem constructed_two_children [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (guard : Guard) (child : Value Symbol Guard) (source : State Symbol Guard)
    (facts : Facts source) (bound : Nat) (stored : Stored bound source) (available : Available source child)
    (combined : SourceEqualityConjoinAllocation.Constraint Formula) :
    let made := run (makeEdge symbol guard [child, .empty]) source
    let state : Machine Symbol Guard := ⟨made.2, Cache.emptyState⟩
    let current := inflate 2 bound
    At ((SourceEqualityNativeCheckedCode.children IntersectionEmptyDomain.emptyDomain made.1 made.1 combined).bind
      (fun edge => .work (makeNode [edge]) .pure)) state current (fun after value => Available after.heap value) := by
  dsimp only
  let made := run (makeEdge symbol guard [child, .empty]) source
  let state : Machine Symbol Guard := ⟨made.2, Cache.emptyState⟩
  have inputs : Values source [child, .empty] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | rest
    · exact available
    · cases List.mem_singleton.mp rest
      exact empty_available _
  have physical := InternedNestedFacts.edge_verified symbol guard [child, .empty] source facts inputs
  have current := SourceRecursiveIntersectionWorkMass.edge symbol guard [child, .empty] source stored
    (fun value member => InternedValueMassHeap.available source stored value (inputs value member))
  have valid : SourceRecursiveIntersectionKernel.Valid state := ⟨physical.facts, Cache.empty_valid⟩
  have resident : EdgeResident made.2 made.1 := physical.result _ _ rfl
  have certificate := children_at IntersectionEmptyDomain.emptyDomain made.1 made.1 combined state (inflate 2 bound)
    valid current.1 (empty_domain state) resident resident
  apply SourceRecursiveIntersectionCodeMass.bind _ _ state (inflate 2 bound) valid current.1 _ _ certificate
  intro edge after larger afterValid _ _ afterStored returned
  exact node_suffix edge after larger afterValid afterStored returned

section Current
local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Initial Top fields construct an accepted checked edge and node return with its initial width certificate. -/
theorem accepted_checked_node [DecidableEq SourceSymbol] [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
    (request : EdgeRequest SourceSymbol SourceGuard) (before : Checked width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before) (ready : EdgeReady before.native.machine request)
    (bound : Nat) (stored : Stored bound before.native.machine.heap)
    (leftEmpty : request.left.children = []) (rightEmpty : request.right.children = [])
    (leftTop : request.left.entry.key.constraint = SourceEqualityConstraintConstructors.top)
    (rightTop : request.right.entry.key.constraint = SourceEqualityConstraintConstructors.top) :
    ∃ code middle result after,
      SourceEqualityNativeDemand.body request (fun edge => .work (makeNode [edge]) .pure) before =
        .yielded (.code code) middle ∧
      At code middle.native.machine bound (fun final value => Available final.heap value) ∧
      SourceEqualityNativeDemand.execute 4 (.edgeBody request (fun edge => .work (makeNode [edge]) .pure)) before =
        .done result after ∧ Available after.native.machine.heap result ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      after.operations = middle.operations := by
  obtain ⟨first, firstLoaded, firstReady, firstReadback, _⟩ :=
    SourceCurrentConjunctionEquality.FieldAvailable.receipts (good.fields _ _ ready.2.1) good.operations
  obtain ⟨second, secondLoaded, secondReady, secondReadback, _⟩ :=
    SourceCurrentConjunctionEquality.FieldAvailable.receipts (good.fields _ _ ready.2.2) good.operations
  have arity : request.left.children.length = request.right.children.length := by rw [leftEmpty, rightEmpty]
  have sourceTop : SourceEqualityIntersectionEdgeAllocation.source GuardStructuralOrder.le
      (SourceEqualityConjoinAllocation.readback first) (SourceEqualityConjoinAllocation.readback second)
      request.left.children.length request.right.children.length = .ready SourceEqualityConstraintConstructors.top := by
    rw [firstReadback, secondReadback, leftTop, rightTop, leftEmpty, rightEmpty]
    cbv
  obtain ⟨branch, done, same, _valid, _growth, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct GuardStructuralOrder.le
    first second request.left.children.length request.right.children.length before.operations good.operations firstReady secondReady
  have mapped := same.trans sourceTop
  cases branch with
  | mismatch | rejected => cases mapped
  | ready combined =>
      let middle : Checked width := {before with operations :=
        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
          request.left.children.length request.right.children.length before.operations).2}
      have yielded := SourceEqualityNativeDemand.body_ready request .pure before arity first second combined firstLoaded secondLoaded done
      simp only [SourceEqualityNativeDemand.code_bind_pure] at yielded
      have certified := body_bind_at request before middle _ (fun edge => .work (makeNode [edge]) .pure)
        bound good.native.machine stored ready yielded (fun final value => Available final.heap value)
        (fun edge final larger finalValid _ _ current resident => node_suffix edge final larger finalValid current resident)
      have literal : SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined =
          .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) []) .pure := by
        simp only [SourceEqualityNativeCheckedCode.children, leftEmpty, rightEmpty, List.zip_nil_right,
          SourceRecursiveIntersectionCode.walk, Code.bind]
      let edge := run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) []) before.native.machine.heap
      let node := run (makeNode [edge.1]) edge.2
      have edgePhysical := InternedNestedFacts.edge_verified request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined)
        [] before.native.machine.heap good.native.machine.1 (by intro value member; cases member)
      have nodePhysical := InternedNestedFacts.node_verified [edge.1] edge.2 edgePhysical.facts (by
        intro value member
        exact List.mem_singleton.mp member ▸ edgePhysical.result _ _ rfl)
      refine ⟨_, middle, node.1, ⟨advance before.native {before.native.machine with heap := node.2}, middle.operations⟩,
        certified.1, certified.2, ?_, nodePhysical.result _ _ rfl, rfl, rfl, rfl⟩
      simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step, certified.1, literal, Code.bind]
      rfl

/-- Actual contradictory fields produce sentinel code and its own checked return without a future width premise. -/
theorem rejected_checked [DecidableEq SourceSymbol] [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
    (request : EdgeRequest SourceSymbol SourceGuard) (before : Checked width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before) (ready : EdgeReady before.native.machine request)
    (bound : Nat) (stored : Stored bound before.native.machine.heap)
    (leftEmpty : request.left.children = []) (rightEmpty : request.right.children = [])
    (leftFalse : request.left.entry.key.constraint = ⟨none, .top⟩)
    (rightTop : request.right.entry.key.constraint = SourceEqualityConstraintConstructors.top) :
    ∃ code middle result after,
      SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) middle ∧
      code = SourceEqualityNativeCheckedCode.sentinel request.left ∧
      At code middle.native.machine bound (fun final edge => EdgeResident final.heap edge) ∧
      SourceEqualityNativeDemand.execute 3 (.edgeBody request .pure) before = .done result after ∧
      result.children = [.empty] ∧ after.operations = middle.operations ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges := by
  obtain ⟨first, firstLoaded, firstReady, firstReadback, _⟩ :=
    SourceCurrentConjunctionEquality.FieldAvailable.receipts (good.fields _ _ ready.2.1) good.operations
  obtain ⟨second, secondLoaded, secondReady, secondReadback, _⟩ :=
    SourceCurrentConjunctionEquality.FieldAvailable.receipts (good.fields _ _ ready.2.2) good.operations
  have arity : request.left.children.length = request.right.children.length := by rw [leftEmpty, rightEmpty]
  have sourceRejected : SourceEqualityIntersectionEdgeAllocation.source GuardStructuralOrder.le
      (SourceEqualityConjoinAllocation.readback first) (SourceEqualityConjoinAllocation.readback second)
      request.left.children.length request.right.children.length = .rejected := by
    rw [firstReadback, secondReadback, leftFalse, rightTop, leftEmpty, rightEmpty]
    cbv
  obtain ⟨branch, done, same, _valid, _growth, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct GuardStructuralOrder.le
    first second request.left.children.length request.right.children.length before.operations good.operations firstReady secondReady
  have mapped := same.trans sourceRejected
  cases branch with
  | mismatch | ready => cases mapped
  | rejected =>
      let middle : Checked width := {before with operations := (SourceEqualityMkEdgeAllocation.emptyField
        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
          request.left.children.length request.right.children.length before.operations).2)}
      have yielded := SourceEqualityNativeDemand.body_rejected request .pure before arity first second firstLoaded secondLoaded done
      simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
      have certificate := body_at request before middle _ bound good.native.machine stored ready yielded
      let made := run (makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) before.native.machine.heap
      refine ⟨_, middle, made.1, ⟨advance before.native {before.native.machine with heap := made.2}, middle.operations⟩,
        yielded, rfl, certificate,
        SourceEqualityNativeDemandRejectedReceipt.rejected_body_complete request before first second arity firstLoaded secondLoaded done,
        ?_, rfl, rfl, rfl⟩
      exact InternedShallowValues.makeEdge_children _ _ [.empty] before.native.machine.heap good.native.machine.1.coherent
        good.native.machine.1.cached (by
          intro value member
          cases List.mem_singleton.mp member
          exact empty_available _)
end Current
end MicroCFTA.CheckedWidthKernels

#print axioms MicroCFTA.CheckedWidthKernels.constructed_two_children
#check @MicroCFTA.CheckedWidthKernels.constructed_two_children
#print axioms MicroCFTA.CheckedWidthKernels.accepted_checked_node
#check @MicroCFTA.CheckedWidthKernels.accepted_checked_node
#print axioms MicroCFTA.CheckedWidthKernels.rejected_checked
#check @MicroCFTA.CheckedWidthKernels.rejected_checked
