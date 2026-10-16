import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion

open MicroCFTA
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionControl SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

#print axioms SourceCurrentAllocatedNativePhysicalCompletion.step_fields
#print axioms SourceCurrentAllocatedNativePhysicalCompletion.step_invariants
#print axioms SourceCurrentAllocatedNativePhysicalCompletion.execute_invariants
#print axioms SourceCurrentAllocatedNativePhysicalCompletion.node_step_yields
#print axioms SourceCurrentAllocatedNativePhysicalCompletion.edge_step_yields
#print axioms SourceCurrentAllocatedNativePhysicalCompletion.body_prefix
#print axioms SourceCurrentAllocatedNativePhysicalCompletion.pure_miss_complete
#check SourceCurrentAllocatedNativePhysicalCompletion.node_step_yields
#check SourceCurrentAllocatedNativePhysicalCompletion.body_prefix
#check SourceCurrentAllocatedNativePhysicalCompletion.pure_miss_complete

/-- Actual source self tests derive physical completion without a result-language receipt. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : Checked width) (valid : Good state)
    (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (missing : state.native.nodes.table key = none)
    (nonempty : hasEmpty request.left request.right = false)
    (noReset : reset request.domain.key request.left request.right = false)
    (same : closedSelf request.left request.right = true) :
    ∃ after, SourceEqualityNativeDemand.execute 3 (.code (requestNode request.domain request.left request.right)) state =
      .done request.left after ∧ Good after ∧ Available after.native.machine.heap request.left := by
  have compiled : compileNode request = .pure request.left := by
    simp only [compileNode, self_first request.domain.key request.left request.right nonempty noReset same]
  obtain ⟨after, done, _, _, good, _, _, available⟩ :=
    pure_miss_complete request state valid ready safe key requested missing request.left compiled
  exact ⟨after, done, good, available⟩

/-- The actual empty-first source branch derives its physical empty return. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : Checked width) (valid : Good state)
    (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (missing : state.native.nodes.table key = none)
    (empty : request.left = .empty ∨ request.right = .empty) :
    ∃ after, SourceEqualityNativeDemand.execute 3 (.code (requestNode request.domain request.left request.right)) state =
      .done .empty after ∧ Good after ∧ Available after.native.machine.heap .empty := by
  have selected : hasEmpty request.left request.right = true := by
    rcases empty with left | right
    · simp only [hasEmpty, left, Value.referenceOf, beq_self_eq_true, Bool.true_or]
    · simp only [hasEmpty, right, Value.referenceOf, beq_self_eq_true, Bool.or_true]
  have compiled : compileNode request = .pure .empty := by
    simp only [compileNode, empty_first request.domain.key request.left request.right selected]
  obtain ⟨after, done, _, _, good, _, _, available⟩ :=
    pure_miss_complete request state valid ready safe key requested missing .empty compiled
  exact ⟨after, done, good, available⟩

/-- Physical direct requests retain loaded fields without an impossible unconditional key bound. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (state : Checked width) (valid : Good state)
    (ready : NodeReady state.native.machine request)
    (none : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = none) :
    SourceCurrentAllocatedNativeFieldClosure.OutcomeFields (step (.code (.node request .pure)) state) := by
  apply step_fields (.code (.node request .pure)) state valid valid.fields ?_ (fun _ => trivial)
  refine ⟨ready, ?_⟩
  intro key present
  rw [none] at present
  cases present

/-- Actual physical finish retains loaded fields without NodeProduced. -/
example [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state : Checked width) (valid : Good state)
    (handle : Nat) (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (running : state.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (available : Available state.native.machine.heap value) :
    Good (step (.code (.finishNode handle value (.pure value))) state).state :=
  (step_invariants (.code (.finishNode handle value (.pure value))) state valid ⟨request, running, available⟩ trivial).1
