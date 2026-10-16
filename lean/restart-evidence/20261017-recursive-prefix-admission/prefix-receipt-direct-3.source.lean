import MicroCFTA.SourceCurrentAllocatedRecursivePrefixState
import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
import MicroCFTA.SourceEqualityNativeDemandProtectedPrefix

/-!
# Receipts for actual recursive checked prefixes

Each receipt derives the physical checks along its supplied raw prefix.
An unfinished inner body retains an appended continuation. An actual inner
return joins its continuation at the same checked state.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursivePrefixReceipt
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedRecursivePrefixState
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
local notation "Entered" => SourceCurrentAllocatedNativeDomainTrace.Entered
local notation "CodeFields" => SourceCurrentAllocatedNativeCodeFields.Fields
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable {A B : Type} {width fuel extra : Nat}

/-- A supplied raw prefix derives its trace checks, current state, and actual return post. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard)
    (inventory : List DomainKey) (initial : Cache.State DomainKey)
    (fuel : Nat) (control : Control A) (before : Checked width)
    (remaining : Control A) (after : Checked width) (post : Machine Symbol Guard → A → Prop) : Prop where
  /-- Every executed instruction has its current physical input check. -/
  trace : Trace fuel control before remaining after
  /-- The returned full state retains the source and past domain history. -/
  current : Current source inventory initial after
  /-- The prefix retains the initial machine records and both identity histories. -/
  extension : Extension before.native.machine after.native.machine
  /-- The prefix retains heap readiness and original equality records. -/
  keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap
  /-- The prefix retains every earlier equality-operation entry. -/
  operations : SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations
  /-- The exact reached control has its current physical input check. -/
  inputs : Inputs remaining after
  /-- The exact reached enter key belongs to the initial finite inventory. -/
  entered : Entered inventory remaining
  /-- The reached continuation retains its allocated equality fields. -/
  fields : Fields remaining after
  /-- An actual reached pure return supplies the local source postcondition. -/
  result : ∀ value, remaining = .code (.pure value) → post after.native.machine value

variable {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}
variable {control middle remaining : Control A} {before current after : Checked width}
variable {post : Machine Symbol Guard → A → Prop}

/-- Equality-operation growth composes at the same returned cache. -/
theorem operations_trans {before middle after : SourceEqualityConstraintMemoAllocation.State}
    (first : SourceEqualityConstraintMemoAllocation.Grows before middle)
    (second : SourceEqualityConstraintMemoAllocation.Grows middle after) :
    SourceEqualityConstraintMemoAllocation.Grows before after :=
  ⟨SourceEqualityConstraintAllocation.steps_trans first.constraints second.constraints,
    Cache.extends_trans first.combinations second.combinations, Cache.extends_trans first.descents second.descents⟩

/-- Zero executed steps retain the current instruction and its own physical post. -/
theorem zero [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (control : Control A) (state : Checked width)
    (known : Current source inventory initial state) (inputs : Inputs control state)
    (admitted : Entered inventory control) (fields : Fields control state)
    (result : ∀ value, control = .code (.pure value) → post state.native.machine value) :
    Receipt source inventory initial 0 control state control state post :=
  ⟨.refl _ _, known, .refl _, SourceEqualityRequiredCache.pure_keeps _ known.good.heap,
    SourceEqualityConstraintMemoAllocation.grows_refl _, inputs, admitted, fields, result⟩

/-- A checked step joins its already derived continuation receipt. -/
theorem before_step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control next : Control A) (before middle : Checked width)
    (known : Current source inventory initial before) (inputs : Inputs control before)
    (admitted : Entered inventory control) (fields : Fields control before)
    (one : SourceEqualityNativeDemand.step control before = .yielded next middle)
    (later : Receipt source inventory initial fuel next middle remaining after post) :
    Receipt source inventory initial (fuel + 1) control before remaining after post := by
  have effects := SourceCurrentAllocatedRecursivePrefixState.yielded control next before middle known inputs admitted fields one
  exact ⟨.cons _ _ _ _ _ _ _ inputs one later.trace, later.current,
    effects.2.1.trans later.extension, effects.2.2.1.trans later.keeps,
    operations_trans effects.2.2.2.1 later.operations, later.inputs, later.entered, later.fields, later.result⟩

/-- Appended source code retains field checks on both ordinary and demanded controls. -/
theorem fields_bind (control : Control A) (next : A → Code Symbol Guard B) (state : Checked width)
    (fields : Fields control state) (continuations : ∀ value, CodeFields state.operations (next value)) :
    Fields (control.bind next) state := by
  cases control with
  | code code => exact SourceCurrentAllocatedNativeCodeFields.fields_bind _ code next fields continuations
  | edgeBody request rest =>
    exact ⟨fields.1, fun value => SourceCurrentAllocatedNativeCodeFields.fields_bind _ _ _ (fields.2 value) continuations⟩

/-- An unfinished actual inner prefix retains all checks before its appended continuation. -/
theorem bind_inside [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (next : A → Code Symbol Guard B)
    (inner : Receipt source inventory initial fuel control before remaining after post)
    (nonpure : ∀ value, remaining ≠ .code (.pure value))
    (continuations : ∀ value, CodeFields before.operations (next value))
    (outputPost : Machine Symbol Guard → B → Prop) :
    Receipt source inventory initial fuel (control.bind next) before (remaining.bind next) after outputPost := by
  refine ⟨inner.trace.bind next, inner.current, inner.extension, inner.keeps, inner.operations,
    SourceEqualityNativeDemandProtectedPrefix.inputs_bind remaining next after nonpure inner.inputs,
    SourceEqualityNativeDemandProtectedPrefix.entered_bind inventory remaining next nonpure inner.entered,
    fields_bind remaining next after inner.fields (fun value =>
      SourceCurrentAllocatedNativeCodeFields.fields_grows before.operations after.operations (next value)
        (continuations value) inner.operations), ?_⟩
  intro value same
  exact False.elim (SourceEqualityNativeDemandProtectedPrefix.bind_nonpure remaining next nonpure value same)

/-- A completed actual inner prefix joins its exact continuation and retains all effects. -/
theorem join [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (next : A → Code Symbol Guard B) (value : A)
    (inner : Receipt source inventory initial fuel control before (.code (.pure value)) current post)
    {remaining : Control B} {outputPost : Machine Symbol Guard → B → Prop}
    (outer : Receipt source inventory initial extra (.code (next value)) current remaining after outputPost) :
    Receipt source inventory initial (fuel + extra) (control.bind next) before remaining after outputPost := by
  exact ⟨(inner.trace.bind next).trans outer.trace, outer.current, inner.extension.trans outer.extension,
    inner.keeps.trans outer.keeps, operations_trans inner.operations outer.operations,
    outer.inputs, outer.entered, outer.fields, outer.result⟩

/-- The derived current physical input check contains the reached machine-word checks. -/
theorem Receipt.words [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (receipt : Receipt source inventory initial fuel control before remaining after post) :
    SourceCurrentAllocatedNativeRequestBounds.Words width remaining := by
  cases remaining with
  | edgeBody => trivial
  | code code => cases code <;> first | exact receipt.inputs.2 | trivial

end MicroCFTA.SourceCurrentAllocatedRecursivePrefixReceipt
