import MicroCFTA.SourceCurrentConstrainedCapCheckedJointEdge
import MicroCFTA.SourceEqualityNativeDemandMismatchReceipt

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace MicroCFTA.CheckedEdgeJointIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointCode (EdgeLaw)
open SourceCurrentConstrainedCapCheckedJointEdge
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "CheckedState" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Initial arity mismatch constructs its own checked return and full joint row law without child calls. -/
theorem mismatch_own_completion [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : State Symbol Guard) (request : EdgeRequest Symbol Guard) (before : CheckedState width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (context : Context Plain source before.native.machine) (ready : EdgeReady before.native.machine request)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    ∃ result after, SourceEqualityNativeDemand.execute 3 (.edgeBody request .pure) before = .done result after ∧
      after.operations = SourceEqualityMkEdgeAllocation.emptyField before.operations ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      EdgeLaw Plain source request result ∧ SourceCurrentConstrainedCap.Edge Plain 0 result ∧
      Context Plain source after.native.machine := by
  let built := run (makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) before.native.machine.heap
  let machine : Machine Symbol Guard := {before.native.machine with heap := built.2}
  let middle : CheckedState width := {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations}
  have yielded : SourceEqualityNativeDemand.body request .pure before =
      .yielded (.code (SourceEqualityNativeCheckedCode.sentinel request.left)) middle := by
    simpa only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] using
      SourceEqualityNativeDemand.body_mismatch request .pure before mismatch
  have physical := InternedNestedFacts.edge_verified request.left.entry.key.symbol SourceEqualityConstraintConstructors.top
    [.empty] before.native.machine.heap context.valid.1 (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)
  have extension : Extension before.native.machine machine := ⟨physical.growth, physical.history, extends_refl _⟩
  have afterContext : Context Plain source machine := context.edge request.left.entry.key.symbol
    SourceEqualityConstraintConstructors.top [.empty] (by intro value member; cases List.mem_singleton.mp member; exact empty_available _)
  have certificate := body_law_certified source request before middle _ good context ready yielded
  have law : EdgeLaw Plain source request built.1 := certificate built.1 machine rfl extension afterContext
  have sentinel := sentinel_certified source 0 request before.native.machine context
  have post : Post Plain source 0 request machine built.1 := sentinel built.1 machine rfl extension afterContext
  refine ⟨built.1, ⟨advance before.native machine, middle.operations⟩,
    SourceEqualityNativeDemandMismatchReceipt.mismatch_body_complete request before mismatch,
    rfl, rfl, rfl, law, post.2.1, afterContext⟩

/-- Initial nullary Top fields construct their own accepted middle and checked return at its exact operation cache. -/
theorem accepted_nullary_own_completion [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : State Symbol Guard) (request : EdgeRequest Symbol Guard) (before : CheckedState width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (context : Context Plain source before.native.machine) (ready : EdgeReady before.native.machine request)
    (leftEmpty : request.left.children = []) (rightEmpty : request.right.children = [])
    (leftTop : request.left.entry.key.constraint = SourceEqualityConstraintConstructors.top)
    (rightTop : request.right.entry.key.constraint = SourceEqualityConstraintConstructors.top) :
    ∃ result after, SourceEqualityNativeDemand.execute 3 (.edgeBody request .pure) before = .done result after ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧
      EdgeLaw Plain source request result ∧ SourceCurrentConstrainedCap.Edge Plain 0 result ∧
      Context Plain source after.native.machine ∧ result.children = [] := by
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
      have combinedTop : SourceEqualityConjoinAllocation.readback combined = SourceEqualityConstraintConstructors.top := by
        exact SourceEqualityIntersectionEdgeAllocation.Branch.ready.inj mapped
      let middle : CheckedState width := {before with operations :=
        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second request.left.children.length
          request.right.children.length before.operations).2}
      have yielded := SourceEqualityNativeDemand.body_ready request .pure before arity first second combined firstLoaded secondLoaded done
      simp only [SourceEqualityNativeDemand.code_bind_pure] at yielded
      have literal : SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined =
          .work (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) []) .pure := by
        simp only [SourceEqualityNativeCheckedCode.children, leftEmpty, rightEmpty, List.zip_nil_right,
          SourceRecursiveIntersectionCode.walk, Code.bind]
      let built := run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) []) before.native.machine.heap
      let machine : Machine Symbol Guard := {before.native.machine with heap := built.2}
      have physical := InternedNestedFacts.edge_verified request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined)
        [] before.native.machine.heap context.valid.1 (by intro value member; cases member)
      have extension : Extension before.native.machine machine := ⟨physical.growth, physical.history, extends_refl _⟩
      have afterContext : Context Plain source machine := context.edge request.left.entry.key.symbol
        (SourceEqualityConjoinAllocation.readback combined) [] (by intro value member; cases member)
      have certificate := body_law_certified source request before middle _ good context ready yielded
      rw [literal] at certificate
      have law : EdgeLaw Plain source request built.1 := certificate built.1 machine rfl extension afterContext
      have cap : SourceCurrentConstrainedCap.Edge Plain 0 built.1 :=
        SourceCurrentConstrainedCap.makeEdge Plain 0 request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined)
          [] before.native.machine.heap context.valid.1.coherent context.valid.1.cached
          (by intro value member; cases member) (by intro _; rw [combinedTop]; exact SourceCurrentUnconstrainedGuardClosure.top_plain)
          (by intro value member; cases member)
      have effects := body_effects request before middle _ good ready yielded
      have complete : SourceEqualityNativeDemand.execute 3 (.edgeBody request .pure) before =
          .done built.1 ⟨advance before.native machine, middle.operations⟩ := by
        simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step, yielded, literal]
        rfl
      exact ⟨built.1, _, complete, rfl, rfl, effects.2.1, effects.2.2, law, cap, afterContext,
        InternedShallowValues.makeEdge_children _ _ [] before.native.machine.heap context.valid.1.coherent context.valid.1.cached
          (by intro value member; cases member)⟩

#print axioms mismatch_own_completion
#check @mismatch_own_completion
#print axioms accepted_nullary_own_completion
#check @accepted_nullary_own_completion
end MicroCFTA.CheckedEdgeJointIndependent
