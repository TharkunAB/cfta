import MicroCFTA.SourceEqualityNativeDemandNodeShortcut
import MicroCFTA.SourceCurrentAllocatedNativeReturnedProperties
import MicroCFTA.InternedBoundaryAtoms

/-!
# Footprints from actual evaluated node shortcuts

The real lookup and demand enter an evaluating memo cell. The existing
checked-code completion law then returns through that same finish handle.
Empty and self bodies give structural footprints for the actual returned cell.
Other node and edge bodies and the whole memo history remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeNodeShortcutFootprints
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl
open InternedBoundaryAtoms (atoms)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat}

set_option autoImplicit false

private theorem started_pure_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request actual : NodeRequest Symbol Guard) (state : Checked width)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (handle : Nat) (chosen current : Native width Symbol Guard)
    (selected : lookupNode width request state.native = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.evaluate actual, current))
    (expected : Value Symbol Guard) (pureBody : compileNode request = .pure expected)
    (available : Available state.native.machine.heap expected) :
    actual = request ∧ SourceCurrentAllocatedNativePhysicalCache.Valid current ∧
      current.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
      Available current.machine.heap expected ∧
      (∀ extra, SourceEqualityNativeDemand.execute (4 + extra) (.code (.node request .pure)) state =
        .done expected ⟨finishNode handle expected current, state.operations⟩) ∧
      ∀ fuel value after,
        SourceEqualityNativeDemand.execute fuel (.code (.node request .pure)) state = .done value after →
        value = expected ∧ after = ⟨finishNode handle expected current, state.operations⟩ := by
  have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual
    state.native chosen current handle physical ready safe selected demanded
  have chosenPhysical := SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid
    state.native physical request ready safe
  simp only [selected] at chosenPhysical
  have currentPhysical := SourceCurrentAllocatedNativePhysicalCache.demandNode_valid
    chosen chosenPhysical handle
  simp only [demanded] at currentPhysical
  have cell := (SourceRecursiveIntersectionNative.demandNode_evaluate
    handle chosen current actual demanded).2
  have running : current.nodes.cells handle = some ⟨request, .evaluating⟩ := by
    simpa only [same] using cell
  have selectedMachine := SourceRecursiveIntersectionNative.lookupNode_machine request state.native
  simp only [selected] at selectedMachine
  have demandedMachine := SourceRecursiveIntersectionNative.demandNode_machine handle chosen
  simp only [demanded] at demandedMachine
  have currentMachine : current.machine = state.native.machine := demandedMachine.trans selectedMachine
  have currentAvailable : Available current.machine.heap expected := by
    rw [currentMachine]
    exact available
  have started : demandNode handle chosen = (.evaluate request, current) := by
    simpa only [same] using demanded
  have completed := SourceEqualityNativeDemandProvenance.pure_node_complete
    request state expected pureBody handle chosen current selected started
  refine ⟨same, currentPhysical, running, currentAvailable, ?_, ?_⟩
  · intro extra
    exact SourceEqualityNativeDemand.done_stable 4 extra (.code (.node request .pure))
      state ⟨finishNode handle expected current, state.operations⟩ expected completed
  · intro fuel value after observed
    have supplied := SourceEqualityNativeDemand.done_stable fuel 4 (.code (.node request .pure))
      state after value observed
    have canonical := SourceEqualityNativeDemand.done_stable 4 fuel (.code (.node request .pure))
      state ⟨finishNode handle expected current, state.operations⟩ expected completed
    have sameDone : SourceEqualityNativeDemand.Outcome.done value after =
        .done expected ⟨finishNode handle expected current, state.operations⟩ := by
      exact supplied.symm.trans (by simpa only [Nat.add_comm] using canonical)
    exact SourceEqualityNativeDemand.Outcome.done.inj sameDone

/-- A real evaluated empty body stores an atomless result at its captured finish handle. -/
theorem empty_node_evaluation_footprint
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request actual : NodeRequest Symbol Guard) (state : Checked width)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (handle : Nat) (chosen current : Native width Symbol Guard)
    (selected : lookupNode width request state.native = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.evaluate actual, current))
    (empty : request.left = .empty ∨ request.right = .empty) :
    actual = request ∧ SourceCurrentAllocatedNativePhysicalCache.Valid current ∧
      current.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
      (∀ extra, SourceEqualityNativeDemand.execute (4 + extra) (.code (.node request .pure)) state =
        .done .empty ⟨finishNode handle .empty current, state.operations⟩) ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid (finishNode handle .empty current) ∧
      (finishNode handle .empty current).nodes.cells handle = some ⟨request, .returned .empty⟩ ∧
      ∀ fuel value after,
        SourceEqualityNativeDemand.execute fuel (.code (.node request .pure)) state = .done value after →
        value = .empty ∧ after = ⟨finishNode handle .empty current, state.operations⟩ ∧ atoms value = [] := by
  have guard : hasEmpty request.left request.right = true := by
    rcases empty with left | right
    · simp only [hasEmpty, left, Value.referenceOf, beq_self_eq_true, Bool.true_or]
    · simp only [hasEmpty, right, Value.referenceOf, beq_self_eq_true, Bool.or_true]
  have branch := empty_first request.domain.key request.left request.right guard
  have pureBody : compileNode request = .pure .empty := by simp only [compileNode, branch]
  obtain ⟨same, currentPhysical, running, available, completed, observedResult⟩ :=
    started_pure_result request actual state physical ready safe handle chosen current selected demanded
      .empty pureBody (empty_available _)
  have afterPhysical := SourceCurrentAllocatedNativePhysicalCache.finishNode_valid
    current currentPhysical handle request .empty running available
  have exactCell := FlatMemoThunk.setStatus_cell handle (.returned (.empty : Value Symbol Guard))
    current.nodes ⟨request, .evaluating⟩ running
  have returned : (finishNode handle .empty current).nodes.cells handle = some ⟨request, .returned .empty⟩ := by
    simpa only [finishNode, FlatMemoThunk.finish, running] using exactCell
  refine ⟨same, currentPhysical, running, completed, afterPhysical, returned, ?_⟩
  intro fuel value after observed
  obtain ⟨sameValue, sameAfter⟩ := observedResult fuel value after observed
  refine ⟨sameValue, sameAfter, ?_⟩
  rw [sameValue]
  simp only [atoms]

/-- A real evaluated self body stores the same source operand and inherits its only-U atoms. -/
theorem self_node_evaluation_footprint
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request actual : NodeRequest Symbol Guard) (state : Checked width)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (ready : NodeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (handle : Nat) (chosen current : Native width Symbol Guard)
    (selected : lookupNode width request state.native = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.evaluate actual, current))
    (nonempty : hasEmpty request.left request.right = false)
    (noReset : reset request.domain.key request.left request.right = false)
    (sameOperands : closedSelf request.left request.right = true)
    (universeIdentity : Nat)
    (onlyU : ∀ atom ∈ atoms request.left, atom = .mu universeIdentity) :
    actual = request ∧ request.left = request.right ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid current ∧
      current.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
      (∀ extra, SourceEqualityNativeDemand.execute (4 + extra) (.code (.node request .pure)) state =
        .done request.left ⟨finishNode handle request.left current, state.operations⟩) ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid (finishNode handle request.left current) ∧
      (finishNode handle request.left current).nodes.cells handle = some ⟨request, .returned request.left⟩ ∧
      ∀ fuel value after,
        SourceEqualityNativeDemand.execute fuel (.code (.node request .pure)) state = .done value after →
        value = request.left ∧ after = ⟨finishNode handle request.left current, state.operations⟩ ∧
          ∀ atom ∈ atoms value, atom = .mu universeIdentity := by
  have branch := self_first request.domain.key request.left request.right nonempty noReset sameOperands
  have pureBody : compileNode request = .pure request.left := by simp only [compileNode, branch]
  have records := self_record state.native.machine.heap physical.machine.1 request.left request.right
    ready.2.1 ready.2.2 sameOperands
  obtain ⟨same, currentPhysical, running, available, completed, observedResult⟩ :=
    started_pure_result request actual state physical ready safe handle chosen current selected demanded
      request.left pureBody ready.2.1
  have afterPhysical := SourceCurrentAllocatedNativePhysicalCache.finishNode_valid
    current currentPhysical handle request request.left running available
  have exactCell := FlatMemoThunk.setStatus_cell handle (.returned request.left)
    current.nodes ⟨request, .evaluating⟩ running
  have returned : (finishNode handle request.left current).nodes.cells handle =
      some ⟨request, .returned request.left⟩ := by
    simpa only [finishNode, FlatMemoThunk.finish, running] using exactCell
  refine ⟨same, records, currentPhysical, running, completed, afterPhysical, returned, ?_⟩
  intro fuel value after observed
  obtain ⟨sameValue, sameAfter⟩ := observedResult fuel value after observed
  refine ⟨sameValue, sameAfter, ?_⟩
  rw [sameValue]
  exact onlyU

end MicroCFTA.SourceCurrentAllocatedNativeNodeShortcutFootprints
