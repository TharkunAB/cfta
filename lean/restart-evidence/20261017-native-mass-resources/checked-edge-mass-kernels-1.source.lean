import MicroCFTA.SourceEqualityNativeCheckedMassInputs
import MicroCFTA.EqualityMergedTargetFixedPoint
import MicroCFTA.SourceEqualityNativeDemandRejectedReceipt

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace MicroCFTA.CheckedEdgeMassKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeCheckedMass
open InternedFreshOrdinaryResultMass (inflate)
local notation "Stored" => InternedValueMassHeap.Stored
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- Two actual source calls retain distinct ordered children and replay their own resident edge winner. -/
theorem ordered_accepted_warm [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (guard : Guard) (child : Value Symbol Guard)
    (source : State Symbol Guard) (facts : Facts source) (bound : Nat) (stored : Stored bound source)
    (available : Available source child) (closed : child.free = []) (nonempty : child.referenceOf ≠ .empty)
    (combined : SourceEqualityConjoinAllocation.Constraint Formula)
    (readback : SourceEqualityConjoinAllocation.readback combined = guard) :
    let made := run (makeEdge symbol guard [child, .empty]) source
    let before : Machine Symbol Guard := ⟨made.2, Cache.emptyState⟩
    let nodes : NodeCall Symbol Guard := fun request current =>
      SourceRecursiveIntersectionKernel.execute SourceEqualityConstraintConstructors.top (fun first _ => first)
        1 request.domain request.left request.right current
    let edges : EdgeCall Symbol Guard := fun _ current => .failed .exhausted current
    let prefixBound := inflate 2 bound
    interpret nodes edges (SourceEqualityNativeCheckedCode.children IntersectionEmptyDomain.emptyDomain made.1 made.1 combined) before =
        .done made.1 before ∧
      made.1.children = [child, .empty] ∧
      Stored (inflate prefixBound prefixBound) made.2 ∧
      InternedValueMass.edge made.1 ≤ inflate prefixBound prefixBound ∧
      SourceRecursiveIntersectionWorkMass.Inputs (prefixBound * prefixBound) made.2
        (makeEdge symbol guard [child, .empty]) := by
  dsimp only
  let made := run (makeEdge symbol guard [child, .empty]) source
  let before : Machine Symbol Guard := ⟨made.2, Cache.emptyState⟩
  let nodes : NodeCall Symbol Guard := fun request current =>
    SourceRecursiveIntersectionKernel.execute SourceEqualityConstraintConstructors.top (fun first _ => first)
      1 request.domain request.left request.right current
  let edges : EdgeCall Symbol Guard := fun _ current => .failed .exhausted current
  have inputs : Values source [child, .empty] := by
    intro value member
    rcases List.mem_cons.mp member with rfl | rest
    · exact available
    · cases List.mem_singleton.mp rest
      exact empty_available _
  have physical := InternedNestedFacts.edge_verified symbol guard [child, .empty] source facts inputs
  have afterFacts : Facts made.2 := physical.facts
  have resident : EdgeResident made.2 made.1 := physical.result _ _ rfl
  have fields := MergedPhysicalGroupEdges.makeEdge_fields source facts symbol guard [child, .empty] inputs
  have bounds := SourceRecursiveIntersectionWorkMass.edge symbol guard [child, .empty] source stored
    (fun value member => InternedValueMassHeap.available source stored value (inputs value member))
  have valid : SourceRecursiveIntersectionKernel.Valid before := ⟨afterFacts, Cache.empty_valid⟩
  have selected : SourceRecursiveIntersectionControl.decision IntersectionEmptyDomain.emptyDomain.key child child = .self := by
    simp [SourceRecursiveIntersectionControl.decision, SourceRecursiveIntersectionControl.hasEmpty,
      SourceRecursiveIntersectionControl.reset, SourceRecursiveIntersectionControl.closedSelf,
      nonempty, closed, IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey]
  have first : nodes ⟨IntersectionEmptyDomain.emptyDomain, child, child⟩ before = .done child before := by
    simp only [nodes, SourceRecursiveIntersectionKernel.execute, onNode, selected]
  have second : nodes ⟨IntersectionEmptyDomain.emptyDomain, .empty, .empty⟩ before = .done .empty before := by rfl
  have trace : WalkTrace (fun pair => nodes ⟨IntersectionEmptyDomain.emptyDomain, pair.1, pair.2⟩)
      (made.1.children.zip made.1.children) before [child, .empty] before := by
    rw [fields.2.2]
    exact .cons _ _ _ _ _ _ _ first (.cons _ _ _ _ _ _ _ second (.nil before))
  have calls : Calls (fun domain left right => nodes ⟨domain, left, right⟩) :=
    execute_checked SourceEqualityConstraintConstructors.top (fun first _ => first) 1
  have assembled := children_assembled nodes edges calls IntersectionEmptyDomain.emptyDomain made.1 made.1 combined
    before before [child, .empty] valid (empty_domain before) resident resident (inflate 2 bound) (inflate 2 bound)
    bounds.1 bounds.1 trace
  have repeated : run (makeEdge made.1.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) [child, .empty]) made.2 =
      (made.1, made.2) := by
    rw [show SourceEqualityConjoinAllocation.readback combined = made.1.entry.key.constraint from readback.trans fields.2.1.symm,
      ← fields.2.2]
    exact EqualityMergedTargetFixedPoint.edge_replay made.1 made.2 afterFacts resident
  have emitted := SourceEqualityNativeCheckedMassInputs.children_inputs nodes calls IntersectionEmptyDomain.emptyDomain made.1 made.1
    combined before before [child, .empty] valid (empty_domain before) resident resident (inflate 2 bound) (inflate 2 bound)
    bounds.1 bounds.1 (Nat.le_refl _) trace
  rw [fields.1, readback] at emitted
  simpa only [repeated] using And.intro assembled.1
    (And.intro fields.2.2 (And.intro assembled.2.2.2.2.2.1 (And.intro assembled.2.2.2.2.2.2.1 emitted)))

section Checked
local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CheckedState" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Initial arity mismatch constructs its own checked sentinel and derives mass and Work-width bounds. -/
theorem mismatch_checked [DecidableEq SourceSymbol] [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
    (request : EdgeRequest SourceSymbol SourceGuard) (before : CheckedState width)
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (bound : Nat) (stored : Stored bound before.native.machine.heap)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    ∃ result after, SourceEqualityNativeDemand.execute 3 (.edgeBody request .pure) before = .done result after ∧
      result.children = [.empty] ∧ Stored (max bound 3) after.native.machine.heap ∧
      InternedValueMass.edge result ≤ max bound 3 ∧
      after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      after.operations = SourceEqualityMkEdgeAllocation.emptyField before.operations ∧
      SourceRecursiveIntersectionWorkMass.Inputs (bound * bound) before.native.machine.heap
        (makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) := by
  let nodes : NodeCall SourceSymbol SourceGuard := fun _ current => .failed .exhausted current
  let edges : EdgeCall SourceSymbol SourceGuard := fun _ current => .failed .exhausted current
  have assembly := sentinel_assembled nodes edges request.left before.native.machine valid bound stored
  let made := run (makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) before.native.machine.heap
  refine ⟨made.1, ⟨advance before.native {before.native.machine with heap := made.2},
    SourceEqualityMkEdgeAllocation.emptyField before.operations⟩,
    SourceEqualityNativeDemandMismatchReceipt.mismatch_body_complete request before mismatch,
    assembly.2.2.2.1, assembly.2.2.2.2.1, assembly.2.2.2.2.2.1,
    assembly.2.2.2.2.2.2.1, assembly.2.2.2.2.2.2.2, rfl, rfl, rfl, ?_⟩
  exact SourceEqualityNativeCheckedMassInputs.sentinel_inputs request.left before.native.machine.heap bound stored

/-- Initial contradictory fields derive actual rejection before the sentinel and retain its precise operation cache. -/
theorem rejection_checked [DecidableEq SourceSymbol] [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
    (request : EdgeRequest SourceSymbol SourceGuard) (before : CheckedState width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (ready : EdgeReady before.native.machine request) (bound : Nat)
    (stored : Stored bound before.native.machine.heap)
    (leftEmpty : request.left.children = []) (rightEmpty : request.right.children = [])
    (leftFalse : request.left.entry.key.constraint = ⟨none, .top⟩)
    (rightTop : request.right.entry.key.constraint = SourceEqualityConstraintConstructors.top) :
    ∃ first second result after,
      SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first) ∧
      SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second) ∧
      SourceEqualityNativeDemand.execute 3 (.edgeBody request .pure) before = .done result after ∧
      result.children = [.empty] ∧ Stored (max bound 3) after.native.machine.heap ∧
      InternedValueMass.edge result ≤ max bound 3 ∧
      after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      after.operations = SourceEqualityMkEdgeAllocation.emptyField
        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second 0 0 before.operations).2 := by
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
  obtain ⟨branch, completed, same, _valid, _growth, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct GuardStructuralOrder.le
    first second request.left.children.length request.right.children.length before.operations good.operations firstReady secondReady
  have mapped := same.trans sourceRejected
  cases branch with
  | mismatch | ready => cases mapped
  | rejected =>
      let nodes : NodeCall SourceSymbol SourceGuard := fun _ current => .failed .exhausted current
      let edges : EdgeCall SourceSymbol SourceGuard := fun _ current => .failed .exhausted current
      have assembly := sentinel_assembled nodes edges request.left before.native.machine good.native.machine bound stored
      let made := run (makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) before.native.machine.heap
      refine ⟨first, second, made.1, ⟨advance before.native {before.native.machine with heap := made.2},
        SourceEqualityMkEdgeAllocation.emptyField
          (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second 0 0 before.operations).2⟩,
        firstLoaded, secondLoaded, ?_, assembly.2.2.2.1, assembly.2.2.2.2.1,
        assembly.2.2.2.2.2.1, assembly.2.2.2.2.2.2.1, assembly.2.2.2.2.2.2.2, rfl, rfl, rfl⟩
      simpa only [leftEmpty, rightEmpty, List.length_nil] using
        SourceEqualityNativeDemandRejectedReceipt.rejected_body_complete request before first second arity firstLoaded secondLoaded completed
end Checked
end MicroCFTA.CheckedEdgeMassKernels

#print axioms MicroCFTA.CheckedEdgeMassKernels.ordered_accepted_warm
#check @MicroCFTA.CheckedEdgeMassKernels.ordered_accepted_warm
#print axioms MicroCFTA.CheckedEdgeMassKernels.mismatch_checked
#check @MicroCFTA.CheckedEdgeMassKernels.mismatch_checked
#print axioms MicroCFTA.CheckedEdgeMassKernels.rejection_checked
#check @MicroCFTA.CheckedEdgeMassKernels.rejection_checked
