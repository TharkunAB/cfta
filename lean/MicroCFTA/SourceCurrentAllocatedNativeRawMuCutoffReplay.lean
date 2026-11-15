import MicroCFTA.SourceCurrentAllocatedNativeMuSource
import MicroCFTA.SourceEqualityNativeDemandTraceSplit

/-!
# Raw left-Mu cutoff replay at the actual current domain cache

The actual Mu entry fixes the child domain and complete started state.
The child hypothesis keeps its original outer prefix and raw count.
An absent paired binder returns the literal child value.
The result retains the exact entry, child, optional step, and endpoint.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeRawMuCutoffReplay
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

set_option autoImplicit false

private theorem optional_unused_trace
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (binder : Nat × Nat) (expected : Value Symbol Guard)
    (before after : Checked width) (count : Nat) (result : Value Symbol Guard)
    (absent : InternedBinderProtocol.Reference.intersection binder.1 binder.2 ∉ expected.free)
    (actual : Steps count (.code (.optionalBinder binder expected .pure)) before (.code (.pure result)) after) :
    count = 1 ∧ result = expected ∧
      after = {before with native := advance before.native {before.native.machine with heap := before.native.machine.heap}} := by
  have unused := SourceRecursiveIntersectionMaybeMu.unused binder expected before.native.machine.heap absent
  have one : SourceEqualityNativeDemand.step (.code (.optionalBinder binder expected .pure)) before =
      .yielded (.code (.pure expected)) {before with native := advance before.native {before.native.machine with heap := before.native.machine.heap}} := by
    simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
      unused, SourceEqualityNativeDemand.lift]
  cases count with
  | zero =>
      have same := steps_zero _ _ _ _ actual
      rw [same.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ actual
      obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (chosen.symm.trans one)
      have terminal := pure_trace remaining expected result
        {before with native := advance before.native {before.native.machine with heap := before.native.machine.heap}} after tail
      have remainingZero : remaining = 0 := terminal.1
      exact ⟨by omega, terminal.2.1.symm, terminal.2.2.symm⟩

/-- Actual current-cache Mu entry and a smaller raw child query return the cutoff without a new binder. -/
theorem left_mu_cutoff_trace_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (original before after : Checked width)
    (parentFuel bodySteps : Nat) (result expected : Value Symbol Guard) (first second : Nat)
    (finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (childPure : compileNode
      ⟨(SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
        request.left request.right first second).1,
        SourceRecursiveIntersectionKernel.body request.left,
        SourceRecursiveIntersectionKernel.body request.right⟩ = .pure expected)
    (absent : let binder := SourceRecursiveIntersectionControl.pair first second
      InternedBinderProtocol.Reference.intersection binder.1 binder.2 ∉ expected.free)
    (entered : Steps 1 (.code (.node request .pure)) original
      (.code ((compileNode request).bind finishNext)) before)
    (smaller : bodySteps < parentFuel)
    (actual : Steps bodySteps (.code (compileNode request)) before (.code (.pure result)) after)
    (children :
      let allocated := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
        request.left request.right first second
      let started : Checked width :=
        {before with native := advance before.native {before.native.machine with domains := allocated.2}}
      ∀ used count, 0 < used → used + count ≤ parentFuel → count < parentFuel →
      ∀ (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (value : Value Symbol Guard) (middle : Checked width),
      Steps used (.code (.node request .pure)) original
        (.code ((requestNode allocated.1 (SourceRecursiveIntersectionKernel.body request.left)
          (SourceRecursiveIntersectionKernel.body request.right)).bind next)) started →
      Steps count (.code (requestNode allocated.1 (SourceRecursiveIntersectionKernel.body request.left)
        (SourceRecursiveIntersectionKernel.body request.right))) started (.code (.pure value)) middle →
      compileNode ⟨allocated.1, SourceRecursiveIntersectionKernel.body request.left,
        SourceRecursiveIntersectionKernel.body request.right⟩ = .pure expected → value = expected) :
    let allocated := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
      request.left request.right first second
    let started : Checked width :=
      {before with native := advance before.native {before.native.machine with domains := allocated.2}}
    let binder := SourceRecursiveIntersectionControl.pair first second
    result = expected ∧ ∃ (childSteps : Nat) (middle : Checked width),
      bodySteps = 1 + childSteps + 1 ∧ 2 + childSteps ≤ parentFuel ∧ childSteps < parentFuel ∧
      Steps 1 (.code (compileNode request)) before
        (.code ((requestNode allocated.1 (SourceRecursiveIntersectionKernel.body request.left)
          (SourceRecursiveIntersectionKernel.body request.right)).bind
            (fun value => .optionalBinder binder value .pure))) started ∧
      Steps 2 (.code (.node request .pure)) original
        (.code ((requestNode allocated.1 (SourceRecursiveIntersectionKernel.body request.left)
          (SourceRecursiveIntersectionKernel.body request.right)).bind
            (fun value => .optionalBinder binder value finishNext))) started ∧
      Steps childSteps (.code (requestNode allocated.1 (SourceRecursiveIntersectionKernel.body request.left)
        (SourceRecursiveIntersectionKernel.body request.right))) started (.code (.pure expected)) middle ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu binder expected middle.native.machine.heap =
        .done expected middle.native.machine.heap ∧
      Steps 1 (.code (.optionalBinder binder expected .pure)) middle (.code (.pure expected)) after ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap := middle.native.machine.heap}} := by

  let allocated := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
    request.left request.right first second
  let started : Checked width :=
    {before with native := advance before.native {before.native.machine with domains := allocated.2}}
  let binder := SourceRecursiveIntersectionControl.pair first second
  let query := requestNode allocated.1 (SourceRecursiveIntersectionKernel.body request.left)
    (SourceRecursiveIntersectionKernel.body request.right)
  let next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun value => .optionalBinder binder value .pure
  let lifted : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun value => (next value).bind finishNext
  have compiled : compileNode request = compileMu request.domain request.left request.right := by
    simp only [compileNode, selected]
  have one : SourceEqualityNativeDemand.step (.code (compileNode request)) before =
      .yielded (.code (query.bind next)) started := by
    rw [compiled]
    exact SourceCurrentAllocatedNativeMuSource.enter_prefix request before first second leftIdentity rightIdentity
  have origin : Steps 1 (.code (compileNode request)) before (.code (query.bind next)) started :=
    .cons _ _ _ _ _ _ _ one (.refl _ _)
  have appended := origin.bind _ _ _ _ _ finishNext
  have composed := entered.trans _ _ _ _ _ _ _ _ appended
  have outer : Steps 2 (.code (.node request .pure)) original (.code (query.bind lifted)) started := by
    simpa only [Control.bind, Code.bind_assoc, Code.bind, lifted] using composed
  cases bodySteps with
  | zero =>
      have same := steps_zero _ _ _ _ actual
      rw [same.1] at one
      cases one
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ actual
      obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (chosen.symm.trans one)
      obtain ⟨childSteps, optionalSteps, value, middle, splitCount, childTrace, optionalTrace⟩ :=
        steps_bind_inverse remaining (.code query) next started after result tail
      have childEq : value = expected := children 2 childSteps (by omega) (by omega) (by omega)
        lifted value middle outer childTrace childPure
      subst value
      obtain ⟨optionalCount, resultEq, endpoint⟩ :=
        optional_unused_trace binder expected middle after optionalSteps result absent optionalTrace
      refine ⟨resultEq, childSteps, middle, by omega, by omega, by omega, origin, outer,
        childTrace, ?_, ?_, endpoint⟩
      · exact SourceRecursiveIntersectionMaybeMu.unused binder expected middle.native.machine.heap absent
      · simpa only [optionalCount, resultEq] using optionalTrace

end MicroCFTA.SourceCurrentAllocatedNativeRawMuCutoffReplay
