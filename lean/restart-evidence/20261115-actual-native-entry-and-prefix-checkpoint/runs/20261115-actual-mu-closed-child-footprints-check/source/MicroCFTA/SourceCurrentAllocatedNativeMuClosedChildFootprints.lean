import MicroCFTA.SourceCurrentAllocatedNativeMuSource
import MicroCFTA.SourceEqualityNativeDemandTraceSplit
import MicroCFTA.InternedBoundaryAtoms

/-!
# Closed child footprints at the actual Mu body

An observed completion determines the exact entered child and its shorter trace.
A closed child value makes the optional binder return that same value.
The child law remains an induction obligation for the actual native worker.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeMuClosedChildFootprints
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

set_option autoImplicit false

/-- Actual Mu completion derives the entered child trace and the exact binder continuation. -/
theorem node_mu_observation
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (before after : Checked width)
    (first second fuel : Nat) (value : Value Symbol Guard)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (done : SourceEqualityNativeDemand.execute fuel (.code (compileNode request)) before = .done value after) :
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
      request.left request.right first second
    let started : Checked width :=
      {before with native := advance before.native {before.native.machine with domains := entered.2}}
    ∃ child middle childSteps restSteps,
      childSteps + 1 < fuel ∧
      Steps 1 (.code (compileNode request)) before
        (.code ((requestNode entered.1 (SourceRecursiveIntersectionKernel.body request.left)
          (SourceRecursiveIntersectionKernel.body request.right)).bind fun result =>
            .optionalBinder (SourceRecursiveIntersectionControl.pair first second) result .pure)) started ∧
      Steps childSteps
        (.code (requestNode entered.1 (SourceRecursiveIntersectionKernel.body request.left)
          (SourceRecursiveIntersectionKernel.body request.right))) started (.code (.pure child)) middle ∧
      SourceEqualityNativeDemand.execute (restSteps + 1)
        (.code (.optionalBinder (SourceRecursiveIntersectionControl.pair first second) child .pure))
        middle = .done value after := by
  let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
    request.left request.right first second
  let started : Checked width :=
    {before with native := advance before.native {before.native.machine with domains := entered.2}}
  let childCode := requestNode entered.1 (SourceRecursiveIntersectionKernel.body request.left)
    (SourceRecursiveIntersectionKernel.body request.right)
  let next := fun result : Value Symbol Guard =>
    Code.optionalBinder (SourceRecursiveIntersectionControl.pair first second) result .pure
  have compiled : compileNode request = compileMu request.domain request.left request.right := by
    rcases selected with chosen | chosen | chosen <;> simp only [compileNode, chosen]
  have one : SourceEqualityNativeDemand.step (.code (compileNode request)) before =
      .yielded (.code (childCode.bind next)) started := by
    rw [compiled]
    exact SourceCurrentAllocatedNativeMuSource.enter_prefix request before first second leftIdentity rightIdentity
  have firstTrace : Steps 1 (.code (compileNode request)) before
      (.code (childCode.bind next)) started :=
    Steps.cons _ _ _ _ _ _ 0 one (Steps.refl _ _)
  cases fuel with
  | zero => cases done
  | succ remaining =>
      have tail : SourceEqualityNativeDemand.execute remaining (.code (childCode.bind next)) started =
          .done value after := by
        simpa only [SourceEqualityNativeDemand.execute, one] using done
      obtain ⟨total, bounded, trace⟩ := done_trace remaining _ started after value tail
      obtain ⟨inner, outer, child, middle, count, childTrace, binderTrace⟩ :=
        steps_bind_inverse total (.code childCode) next started after value trace
      refine ⟨child, middle, inner, outer, by omega, firstTrace, childTrace, ?_⟩
      exact trace_done outer _ middle after value binderTrace

private theorem closed_optional_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (key : Nat × Nat) (child : Value Symbol Guard) (before after : Checked width)
    (fuel : Nat) (value : Value Symbol Guard) (closed : child.free = [])
    (done : SourceEqualityNativeDemand.execute fuel (.code (.optionalBinder key child .pure)) before =
      .done value after) : value = child ∧ after = before := by
  have unused : InternedBinderProtocol.Reference.intersection key.1 key.2 ∉ child.free := by
    simp only [closed, List.not_mem_nil, not_false_eq_true]
  have same := SourceRecursiveIntersectionMaybeMu.unused key child before.native.machine.heap unused
  have completed : SourceEqualityNativeDemand.execute 2 (.code (.optionalBinder key child .pure)) before =
      .done child before := by
    simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step,
      SourceRecursiveIntersectionNative.step, same, SourceEqualityNativeDemand.lift]
    rfl
  have actual := SourceEqualityNativeDemand.done_stable fuel 2 _ before after value done
  have expected := SourceEqualityNativeDemand.done_stable 2 fuel _ before before child completed
  rw [Nat.add_comm 2 fuel] at expected
  exact Outcome.done.inj (actual.symm.trans expected)

/-- A closed actual entered child gives the same Mu-body result without a new binder or heap effect. -/
theorem node_mu_closed_child_footprint
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (before after : Checked width)
    (first second fuel universeIdentity : Nat) (value : Value Symbol Guard)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (done : SourceEqualityNativeDemand.execute fuel (.code (compileNode request)) before = .done value after)
    (children :
      let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
        request.left request.right first second
      let started : Checked width :=
        {before with native := advance before.native {before.native.machine with domains := entered.2}}
      ∀ childFuel, childFuel < fuel → ∀ child middle,
        SourceEqualityNativeDemand.execute childFuel
          (.code (requestNode entered.1 (SourceRecursiveIntersectionKernel.body request.left)
            (SourceRecursiveIntersectionKernel.body request.right))) started = .done child middle →
        child.free = [] ∧ ∀ atom ∈ InternedBoundaryAtoms.atoms child, atom = .mu universeIdentity) :
    value.free = [] ∧
      (∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu universeIdentity) ∧
      ∃ childSteps,
        childSteps + 1 < fuel ∧
        Steps childSteps
          (.code (requestNode
            (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
              request.left request.right first second).1
            (SourceRecursiveIntersectionKernel.body request.left) (SourceRecursiveIntersectionKernel.body request.right)))
          {before with native := advance before.native {before.native.machine with domains :=
            (SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
              request.left request.right first second).2}}
          (.code (.pure value)) after := by
  obtain ⟨child, middle, childSteps, restSteps, shorter, _entered, childTrace, binderDone⟩ :=
    node_mu_observation request before after first second fuel value leftIdentity rightIdentity selected done
  have childDone := trace_done childSteps _ _ middle child childTrace
  have profile := children (childSteps + 1) shorter child middle childDone
  obtain ⟨sameValue, sameAfter⟩ := closed_optional_result
    (SourceRecursiveIntersectionControl.pair first second) child middle after
      (restSteps + 1) value profile.1 binderDone
  subst value
  subst after
  exact ⟨profile.1, profile.2, childSteps, shorter, childTrace⟩

end MicroCFTA.SourceCurrentAllocatedNativeMuClosedChildFootprints

#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuClosedChildFootprints.node_mu_observation
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuClosedChildFootprints.node_mu_closed_child_footprint
