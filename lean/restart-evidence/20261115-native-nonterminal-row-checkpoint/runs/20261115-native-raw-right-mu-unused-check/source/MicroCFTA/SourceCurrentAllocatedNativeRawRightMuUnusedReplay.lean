import MicroCFTA.SourceCurrentAllocatedNativeRawMuCutoffReplay

/-!
# Raw right-Mu replay with an unused paired binder

The actual entry fixes both original bodies and the current child domain.
A smaller raw child query supplies its static value predicate.
The predicate excludes this frame's paired reference.
Optional binding returns the same actual child value and complete state.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeRawRightMuUnusedReplay
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

/-- The actual right-Mu body returns its child predicate and complete state when the paired binder is unused. -/
theorem right_mu_unused_trace_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (P : Value Symbol Guard → Prop)
    (request : NodeRequest Symbol Guard) (original before after : Checked width)
    (parentFuel bodySteps : Nat) (result : Value Symbol Guard) (first second : Nat)
    (finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (unused : let binder := SourceRecursiveIntersectionControl.pair first second
      ∀ value, P value → InternedBinderProtocol.Reference.intersection binder.1 binder.2 ∉ value.free)
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
        (SourceRecursiveIntersectionKernel.body request.right))) started (.code (.pure value)) middle → P value) :
    let allocated := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
      request.left request.right first second
    let started : Checked width :=
      {before with native := advance before.native {before.native.machine with domains := allocated.2}}
    let binder := SourceRecursiveIntersectionControl.pair first second
    P result ∧ ∃ (childSteps : Nat) (middle : Checked width),
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
        (SourceRecursiveIntersectionKernel.body request.right))) started (.code (.pure result)) middle ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu binder result middle.native.machine.heap =
        .done result middle.native.machine.heap ∧
      Steps 1 (.code (.optionalBinder binder result .pure)) middle (.code (.pure result)) after ∧
      after = middle := by

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
      have childProperty : P value := children 2 childSteps (by omega) (by omega) (by omega)
        lifted value middle outer childTrace
      have absent : InternedBinderProtocol.Reference.intersection binder.1 binder.2 ∉ value.free :=
        unused value childProperty
      obtain ⟨optionalCount, resultEq, endpoint⟩ :=
        optional_unused_trace binder value middle after optionalSteps result absent optionalTrace
      subst result
      refine ⟨childProperty, childSteps, middle, by omega, by omega, by omega, origin, outer,
        childTrace, ?_, ?_, ?_⟩
      · exact SourceRecursiveIntersectionMaybeMu.unused binder value middle.native.machine.heap absent
      · simpa only [optionalCount] using optionalTrace
      · exact endpoint

end MicroCFTA.SourceCurrentAllocatedNativeRawRightMuUnusedReplay


set_option warningAsError true
#check MicroCFTA.SourceCurrentAllocatedNativeRawRightMuUnusedReplay.right_mu_unused_trace_result
#print axioms MicroCFTA.SourceCurrentAllocatedNativeRawRightMuUnusedReplay.right_mu_unused_trace_result
