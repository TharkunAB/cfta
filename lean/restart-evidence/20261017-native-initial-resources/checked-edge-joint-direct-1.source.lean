import MicroCFTA.SourceCurrentConstrainedCapKernelJointRows
import MicroCFTA.SourceCurrentConstrainedCapNativeEdge

/-!
# Joint laws for literal checked native edge bodies

The actual field allocation chooses accepted child code or the sentinel.
Accepted code uses its allocated readback. It does not replace rejection
with an eager conjunction. Smaller actual node calls supply their own
joint return laws. Equality operations retain their exact returned cache.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedEdgeJoint
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs EdgeInputs edgeBudget)
open SourceCurrentConstrainedCapPairOccurrences (FreeLE sourceWeight)
open SourceRecursiveIntersectionResultScope (Scope EdgeScope)
open SourceCurrentConstrainedCapKernelJoint (Context)
local notation "JointChecked" => SourceCurrentConstrainedCapKernelJoint.Checked
local notation "JointCalls" => SourceCurrentConstrainedCapKernelJoint.Calls
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "CheckedState" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- One actual returned row retains its cap, literal child budget and pair scope. -/
def Post (annotation : Guard → Prop) (source : State Symbol Guard) (depth : Nat)
    (request : EdgeRequest Symbol Guard) (after : Machine Symbol Guard) (result : EdgeValue Symbol Guard) : Prop :=
  EdgeResident after.heap result ∧ Edge annotation depth result ∧
    (∀ child ∈ result.children, FreeLE (sourceWeight annotation source) (edgeBudget annotation request) child) ∧
    EdgeScope request.domain.key.seen result

private theorem edge_work [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : State Symbol Guard) (depth : Nat) (request : EdgeRequest Symbol Guard)
    (guard : Guard) (values : List (Value Symbol Guard)) (state : Machine Symbol Guard)
    (context : Context annotation source state) (available : ∀ value ∈ values, Available state.heap value)
    (guardValid : depth = 0 → annotation guard) (bounded : ∀ value ∈ values, Cap annotation (depth - 1) value)
    (free : ∀ value ∈ values, FreeLE (sourceWeight annotation source) (edgeBudget annotation request) value)
    (scopes : ∀ value ∈ values, Scope request.domain.key.seen value) :
    JointChecked annotation source (work (makeEdge request.left.entry.key.symbol guard values) state)
      (Post annotation source depth request) := by
  intro edge after done
  obtain ⟨rfl, rfl⟩ := work_done _ state edge after done
  refine ⟨context.edge _ guard values available,
    (InternedNestedFacts.edge_verified _ guard values state.heap context.valid.1 available).result _ _ rfl,
    SourceCurrentConstrainedCap.makeEdge annotation depth _ guard values state.heap
      context.valid.1.coherent context.valid.1.cached available guardValid bounded, ?_, ?_⟩
  · rw [InternedShallowValues.makeEdge_children _ guard values state.heap context.valid.1.coherent context.valid.1.cached available]
    exact free
  · exact SourceRecursiveIntersectionResultScope.edge request.domain.key.seen _ guard values state.heap context.valid.1 available scopes

/-- Actual accepted child code derives its row laws from the ordered smaller original requests. -/
theorem children_joint [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : State Symbol Guard)
    (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (physical : SourceRecursiveIntersectionKernel.Calls (fun domain left right => nodes ⟨domain, left, right⟩))
    (joint : JointCalls annotation source (fun domain left right => nodes ⟨domain, left, right⟩))
    (depth : Nat) (request : EdgeRequest Symbol Guard) (combined : Allocated)
    (state : Machine Symbol Guard) (context : Context annotation source state)
    (ready : EdgeReady state request) (bindings : OriginalBindings annotation source request.domain.key)
    (inputs : EdgeInputs source request) (leftCap : Edge annotation depth request.left) (rightCap : Edge annotation depth request.right)
    (combinedValid : depth = 0 → annotation (SourceEqualityConjoinAllocation.readback combined)) :
    JointChecked annotation source
      (interpret nodes edges (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state)
      (Post annotation source depth request) := by
  rw [SourceEqualityNativeCheckedCode.children_exact]
  let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain current request.domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2 ∧
      Cap annotation (depth - 1) pair.1 ∧ Cap annotation (depth - 1) pair.2 ∧ NodeInputs source ⟨request.domain, pair.1, pair.2⟩
  let output := fun (after : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Available after.heap value ∧ Cap annotation (depth - 1) value ∧
      FreeLE (sourceWeight annotation source) (edgeBudget annotation request) value ∧ Scope request.domain.key.seen value
  have walked := SourceCurrentConstrainedCapKernelJoint.walk annotation source
    (fun pair : Value Symbol Guard × Value Symbol Guard => nodes ⟨request.domain, pair.1, pair.2⟩)
    (request.left.children.zip request.right.children) input output
    (by intro before after growth pair known; exact ⟨known.1.grows _ growth, growth.available _ known.2.1,
      growth.available _ known.2.2.1, known.2.2.2⟩)
    (by intro before after growth value result; exact ⟨growth.available _ result.1, result.2⟩)
    (by
      intro pair _ current valid currentInputs
      have checked := physical request.domain pair.1 pair.2 current valid currentInputs.1 currentInputs.2.1 currentInputs.2.2.1
      exact ⟨checked.valid, checked.extension, by intro _ _ _; trivial⟩)
    (by
      intro pair member current currentContext currentInputs
      apply SourceCurrentConstrainedCapKernelJoint.map annotation source _ _ _
        (joint (depth - 1) request.domain pair.1 pair.2 current currentContext currentInputs.1 bindings
          currentInputs.2.2.2.2.2 currentInputs.2.2.2.1 currentInputs.2.2.2.2.1)
      intro value after _ result
      exact ⟨result.1, result.2.1, fun name named => Nat.le_trans (result.2.2.1.free name named)
        (SourceCurrentConstrainedCapNativeOccurrenceCache.childBudget_member annotation _ pair member), result.2.2.2⟩)
    state context (by
      intro pair member
      have inside := List.of_mem_zip member
      have first := inputs.1 pair.1 inside.1
      have second := inputs.2 pair.2 inside.2
      have capped : Cap annotation (depth - 1) pair.1 ∧ Cap annotation (depth - 1) pair.2 :=
        SourceCurrentConstrainedCapNativeScope.edge_child annotation depth request.left request.right leftCap rightCap pair member
      exact ⟨ready.1, context.valid.1.cached.edges _ _ ready.2.1 pair.1 inside.1,
        context.valid.1.cached.edges _ _ ready.2.2 pair.2 inside.2, capped.1, capped.2,
        first.1, second.1, first.2.1, second.2.1, first.2.2, second.2.2⟩)
  apply SourceCurrentConstrainedCapKernelJoint.bind annotation source _ _ _ _ walked
  intro values after _ afterContext results
  exact edge_work annotation source depth request (SourceEqualityConjoinAllocation.readback combined) values after afterContext
    (fun value member => (results value member).1) combinedValid
    (fun value member => (results value member).2.1) (fun value member => (results value member).2.2.1)
    (fun value member => (results value member).2.2.2)

/-- Literal rejection code has every cap depth and requires no child callback law. -/
theorem sentinel_joint [DecidableEq (EdgeKey Symbol Guard)]
    (source : State Symbol Guard) (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (depth : Nat) (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard)
    (context : Context Plain source state) :
    JointChecked Plain source (interpret nodes edges (SourceEqualityNativeCheckedCode.sentinel request.left) state)
      (Post Plain source depth request) := by
  rw [SourceEqualityNativeCheckedCode.sentinel_exact]
  apply edge_work Plain source depth request SourceEqualityConstraintConstructors.top [.empty] state context
  · intro value member; cases List.mem_singleton.mp member; exact empty_available _
  · intro _; exact SourceCurrentUnconstrainedGuardClosure.top_plain
  · intro value member; cases List.mem_singleton.mp member; exact .plain _ .empty
  · intro value member; cases List.mem_singleton.mp member; exact fun _ impossible => by cases impossible
  · intro value member; cases List.mem_singleton.mp member; exact SourceRecursiveIntersectionResultScope.closed _ _ rfl

/-- The actual checked yield retains its native state and growing valid equality operations. -/
theorem body_effects (request : EdgeRequest Symbol Guard) (before after : CheckedState width)
    (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before) (ready : EdgeReady before.native.machine request)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    after.native = before.native ∧ SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations := by
  have same := SourceEqualityNativeDemandOperations.body_native request .pure before
  have operations := SourceEqualityNativeDemandOperations.body_operations request .pure before good.operations
    (good.fields _ _ ready.2.1).1 (good.fields _ _ ready.2.2).1
  simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using And.intro same operations

/-- Actual allocated field decisions certify the emitted code at the same returned operations and native state. -/
theorem body_joint [DecidableEq (EdgeKey Symbol Guard)]
    (source : State Symbol Guard) (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (physical : SourceRecursiveIntersectionKernel.Calls (fun domain left right => nodes ⟨domain, left, right⟩))
    (joint : JointCalls Plain source (fun domain left right => nodes ⟨domain, left, right⟩))
    (depth : Nat) (request : EdgeRequest Symbol Guard) (before after : CheckedState width)
    (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (context : Context Plain source before.native.machine) (ready : EdgeReady before.native.machine request)
    (bindings : OriginalBindings Plain source request.domain.key) (inputs : EdgeInputs source request)
    (left : Edge Plain depth request.left) (right : Edge Plain depth request.right)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    after.native = before.native ∧ SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
      SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations ∧
      JointChecked Plain source (interpret nodes edges code after.native.machine) (Post Plain source depth request) := by
  obtain ⟨same, operations, growth⟩ := body_effects request before after code good ready yielded
  refine ⟨same, operations, growth, ?_⟩
  rw [same]
  by_cases arity : request.left.children.length = request.right.children.length
  · have matched : ¬ request.left.children.length ≠ request.right.children.length := by omega
    simp only [SourceEqualityNativeDemand.body, ite_eq_right matched] at yielded
    cases firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints with
    | error message => simp only [firstLoaded] at yielded; cases yielded
    | ok first =>
        cases first with
        | none => simp only [firstLoaded] at yielded; cases yielded
        | some first =>
            simp only [firstLoaded] at yielded
            cases secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints with
            | error message => simp only [secondLoaded] at yielded; cases yielded
            | ok second =>
                cases second with
                | none => simp only [secondLoaded] at yielded; cases yielded
                | some second =>
                    simp only [secondLoaded] at yielded
                    have firstCached := (good.fields _ _ ready.2.1).1
                    have secondCached := (good.fields _ _ ready.2.2).1
                    have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
                      firstCached first firstLoaded).1
                    have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
                      secondCached second secondLoaded).1
                    obtain ⟨branch, done, _, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct
                      GuardStructuralOrder.le first second request.left.children.length request.right.children.length
                      before.operations good.operations firstReady secondReady
                    cases branch with
                    | mismatch | rejected =>
                        simp only [done, SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
                        cases yielded
                        exact sentinel_joint source nodes edges depth request _ context
                    | ready combined =>
                        have combinedPlain : depth = 0 → SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback combined) = true := by
                          intro zero
                          subst depth
                          exact SourceCurrentUnconstrainedGuardClosure.loaded_ready_plain
                            GuardStructuralOrder.le request.left.entry.key.constraint request.right.entry.key.constraint
                            first second request.left.children.length request.right.children.length before.operations good.operations
                            firstCached secondCached firstLoaded secondLoaded left.1 right.1 combined done
                        simp only [done, SourceEqualityNativeDemand.code_bind_pure] at yielded
                        cases yielded
                        exact children_joint Plain source nodes edges physical joint depth request combined _ context ready bindings inputs left right combinedPlain
  · simp only [SourceEqualityNativeDemand.body, ite_eq_left arity, SourceEqualityNativeDemand.sentinel,
      SourceEqualityNativeDemand.code_bind_pure] at yielded
    cases yielded
    exact sentinel_joint source nodes edges depth request _ context

end MicroCFTA.SourceCurrentConstrainedCapCheckedEdgeJoint
