import MicroCFTA.SourceCurrentAllocatedRecursivePrefixReceipt

namespace MicroCFTA.StateReceiptKernels

open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedRecursivePrefixState SourceCurrentAllocatedRecursivePrefixReceipt
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fields" => SourceCurrentAllocatedNativeFieldClosure.Fields
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def key : IntersectionFlatMemoKeyDomain.DomainKey :=
  SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey []
    (SourceRecursiveIntersectionControl.pair 0 1)

private def entered (before : Checked width) : Checked width :=
  {before with native := advance before.native {before.native.machine with domains :=
    (IntersectionEmptyDomain.make before.native.machine.domains key).2}}

private def workCode : Code Symbol Guard Unit := .work (.pure ()) .pure
private def readCode : Code Symbol Guard Unit := .read 0 (fun _ => workCode)
private def program : Code Symbol Guard Unit :=
  .enter IntersectionEmptyDomain.emptyDomain .empty .empty 0 1 (fun _ => readCode)

/-- Three literal checked steps derive their own physical receipt and actual past allocation bound. -/
theorem enter_read_work (before : Checked width) (good : Good before)
    (semantic : SemanticReady before.native.machine.heap) :
    Receipt before.native.machine.heap [key] before.native.machine.domains 3 (.code program) before
      (.code (.pure ())) (entered before)
      (fun machine (_ : Unit) => machine.domains =
        (IntersectionEmptyDomain.make before.native.machine.domains key).2) ∧
      (entered before).native.machine.domains.next ≤ before.native.machine.domains.next + 1 ∧
      (entered before).operations = before.operations ∧
      (entered before).native.nodes = before.native.nodes ∧ (entered before).native.edges = before.native.edges := by
  have known := SourceCurrentAllocatedRecursivePrefixState.initial before.native.machine.heap [key] before good semantic rfl
  have inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code program) before :=
    ⟨empty_domain _, empty_available _, empty_available _⟩
  have admitted : SourceCurrentAllocatedNativeDomainTrace.Entered [key] (.code program) := by
    simp [SourceCurrentAllocatedNativeDomainTrace.Entered, SourceCurrentAllocatedNativeDomainTrace.CodeEntered,
      program, key, SourceRecursiveIntersectionEnvironment.bindings,
      SourceRecursiveIntersectionEnvironment.binder, IntersectionEmptyDomain.emptyDomain]
  have fields : Fields (.code program) before := by
    simp [SourceCurrentAllocatedNativeFieldClosure.Fields, SourceCurrentAllocatedNativeCodeFields.Fields, program, readCode, workCode, SourceEqualityAnnotationHeap.SafeWork]
  have first : SourceEqualityNativeDemand.step (.code program) before =
      .yielded (.code readCode) (entered before) := rfl
  have state := SourceCurrentAllocatedRecursivePrefixState.yielded (.code program) (.code readCode)
    before (entered before) known inputs admitted fields first
  have final : Receipt before.native.machine.heap [key] before.native.machine.domains 0
      (.code (.pure ())) (entered before) (.code (.pure ())) (entered before)
      (fun machine (_ : Unit) => machine.domains =
        (IntersectionEmptyDomain.make before.native.machine.domains key).2) := by
    apply zero (.code (.pure ())) (entered before) state.1 trivial trivial trivial
    intro value same
    rfl
  have workFields : Fields (.code workCode) (entered before) := by
    simp [SourceCurrentAllocatedNativeFieldClosure.Fields, SourceCurrentAllocatedNativeCodeFields.Fields, workCode, SourceEqualityAnnotationHeap.SafeWork]
  have workReceipt := before_step (.code workCode) (.code (.pure ())) (entered before) (entered before)
    state.1 (SourceEqualityNativeDemandHeapPrimitives.WorkInputs.pure ()) trivial workFields rfl final
  have readFields : Fields (.code readCode) (entered before) := by
    simp [SourceCurrentAllocatedNativeFieldClosure.Fields, SourceCurrentAllocatedNativeCodeFields.Fields, readCode, workCode, SourceEqualityAnnotationHeap.SafeWork]
  have readReceipt := before_step (.code readCode) (.code workCode) (entered before) (entered before)
    state.1 trivial trivial readFields rfl workReceipt
  have total := before_step (.code program) (.code readCode) before (entered before)
    known inputs admitted fields first readReceipt
  exact ⟨total, by simpa using total.current.domains.next_le, rfl, rfl, rfl⟩

private def innerCode : Code Symbol Guard Nat := .read 0 (fun _ => .read 1 (fun _ => .pure 7))
private def tailCode : Code Symbol Guard Nat := .read 1 (fun _ => .pure 7)
private def nextCode (value : Nat) : Code Symbol Guard Unit := .read value (fun _ => .pure ())

/-- An actual unfinished read prefix appends code, and the completed inner prefix joins at the same full state. -/
theorem inside_then_join {source inventory initial} (before : Checked width)
    (known : Current source inventory initial before) :
    Receipt source inventory initial 1 ((.code innerCode : Control Nat).bind nextCode) before
      ((.code tailCode : Control Nat).bind nextCode) before (fun _ (_ : Unit) => True) ∧
      Receipt source inventory initial 3 ((.code innerCode : Control Nat).bind nextCode) before
        (.code (.pure ())) before (fun _ (_ : Unit) => True) := by
  have tailZero : Receipt source inventory initial 0 (.code tailCode) before (.code tailCode) before
      (fun _ (_ : Nat) => True) :=
    zero (.code tailCode) before known trivial trivial (by intro _; trivial) (by intro _ _; trivial)
  have unfinished :=  before_step (.code innerCode) (.code tailCode) before before known trivial trivial
    (by intro _ _; trivial) rfl tailZero
  have nonpure : ∀ value, (Control.code tailCode) ≠ .code (.pure value) := by
    intro value impossible
    cases impossible
  have inside := bind_inside nextCode unfinished nonpure (by intro _ _; trivial) (fun _ (_ : Unit) => True)
  have returned : Receipt source inventory initial 0 (.code (.pure 7)) before (.code (.pure 7)) before
      (fun _ (_ : Nat) => True) :=
    zero (.code (.pure 7)) before known trivial trivial trivial (by intro _ _; trivial)
  have tail := before_step (.code tailCode) (.code (.pure 7)) before before known trivial trivial
    (by intro _; trivial) rfl returned
  have inner := before_step (.code innerCode) (.code tailCode) before before known trivial trivial
    (by intro _ _; trivial) rfl tail
  have outerZero : Receipt source inventory initial 0 (.code (.pure ())) before (.code (.pure ())) before
      (fun _ (_ : Unit) => True) :=
    zero (.code (.pure ())) before known trivial trivial trivial (by intro _ _; trivial)
  have outer := before_step (.code (nextCode 7)) (.code (.pure ())) before before known trivial trivial
    (by intro _; trivial) rfl outerZero
  exact ⟨inside, join nextCode 7 inner outer⟩

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms enter_read_work
#check @enter_read_work
#print axioms inside_then_join
#check @inside_then_join

end MicroCFTA.StateReceiptKernels
