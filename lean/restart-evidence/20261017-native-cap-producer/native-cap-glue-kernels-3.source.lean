import MicroCFTA.SourceCurrentConstrainedCapNativeTraceGlue

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.NativeCapGlueKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentConstrainedCapNativeLaws (NodeLaw)
open SourceCurrentAllocatedRecursivePrefixState (Current)
open SourceCurrentConstrainedCapNativeTraceGlue
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable {width : Nat} {annotation : Guard → Prop} {source : State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}

/-- An actual self body derives its universal law and installs it at the captured running owner. -/
theorem self_publication [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (request : NodeRequest Symbol Guard) (before : Checked width) (handle : Nat)
    (known : Current source inventory initial before) (stored : Stored annotation before)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self) :
    Receipt annotation source inventory initial 1
      ((.code (compileNode request) : Control (Value Symbol Guard)).bind (fun value => .finishNode handle value (.pure value)))
      before request.left {before with native := finishNode handle request.left before.native}
      (fun state value => Available state.heap value) (fun _ value => ∀ scope, NodeLaw annotation scope request value) ∧
    (finishNode handle request.left before.native).nodes.cells handle = some ⟨request, .returned request.left⟩ := by
  have available := (known.good.native.nodes.checked handle _ running).1.2.1
  have compiled : compileNode request = .pure request.left := by simp only [compileNode, branch]
  have physical : SourceCurrentAllocatedRecursivePrefixReceipt.Receipt source inventory initial 0
      (.code (compileNode request)) before (.code (.pure request.left)) before
      (fun state value => Available state.heap value) := by
    rw [compiled]
    exact SourceCurrentAllocatedRecursivePrefixReceipt.zero _ _ known trivial trivial trivial
      (by intro value same; cases same; exact available)
  exact finish_node request known running ⟨physical, stored, fun _ _ _ left _ => left⟩

/-- Literal node construction composes with the actual self return and its exact owner finish. -/
theorem constructor_then_publication [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (request : NodeRequest Symbol Guard) (before : Checked width) (handle : Nat)
    (known : Current source inventory initial before) (stored : Stored annotation before)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self) :
    ∃ middle after,
      middle = {before with native := advance before.native {before.native.machine with heap := (run (makeNode []) before.native.machine.heap).2}} ∧
      after = {middle with native := finishNode handle request.left middle.native} ∧
      Receipt annotation source inventory initial 2
        (.code (.work (makeNode []) (fun _ => (compileNode request).bind (fun value => .finishNode handle value (.pure value)))))
        before request.left after (fun state value => Available state.heap value)
        (fun _ value => ∀ scope, NodeLaw annotation scope request value) ∧
      after.native.nodes.cells handle = some ⟨request, .returned request.left⟩ := by
  let output := (run (makeNode []) before.native.machine.heap).1
  let middle : Checked width := {before with native := advance before.native {before.native.machine with heap := (run (makeNode []) before.native.machine.heap).2}}
  have one : step (.code (.work (makeNode []) .pure)) before = .yielded (.code (.pure output)) middle := rfl
  have inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.work (makeNode []) .pure)) before :=
    .node [] (fun _ member => by cases member)
  have fields : SourceCurrentAllocatedNativeFieldClosure.Fields (.code (.work (makeNode []) .pure)) before :=
    ⟨SourceCurrentAllocatedNativeCodeFields.makeNode_fields _ [], fun _ => trivial⟩
  have effects := SourceCurrentAllocatedRecursivePrefixState.yielded
    (.code (.work (makeNode []) .pure)) (.code (.pure output)) before middle known inputs trivial fields one
  have storedMiddle : Stored annotation middle := work_stored annotation (makeNode []) before
    (SourceCurrentHereditaryNativeEffects.WorkSafe.makeNode annotation []) stored
  have terminal : SourceCurrentAllocatedRecursivePrefixReceipt.Receipt source inventory initial 0
      (.code (.pure output)) middle (.code (.pure output)) middle (fun _ _ => True) :=
    SourceCurrentAllocatedRecursivePrefixReceipt.zero _ _ effects.1 trivial trivial trivial (by intros; trivial)
  have first : Receipt annotation source inventory initial 1 (.code (.work (makeNode []) .pure)) before output middle
      (fun _ _ => True) (fun _ _ => True) :=
    ⟨SourceCurrentAllocatedRecursivePrefixReceipt.before_step _ _ _ _ known inputs trivial fields one terminal, storedMiddle, trivial⟩
  have owner : middle.native.nodes.cells handle = some ⟨request, .evaluating⟩ := running
  have published := self_publication request middle handle effects.1 storedMiddle owner branch
  let next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
    fun _ => (compileNode request).bind (fun value => .finishNode handle value (.pure value))
  have last : Receipt annotation source inventory initial 1 (.code (next output)) middle request.left
      {middle with native := finishNode handle request.left middle.native}
      (fun state value => Available state.heap value) (fun _ value => ∀ scope, NodeLaw annotation scope request value) := by
    simpa only [next, Control.bind] using published.1
  exact ⟨middle, _, rfl, rfl, join next first last, published.2⟩

/-- The same generated publication supplies the cap-code continuation at its exact final machine. -/
theorem published_cap_continuation (request : NodeRequest Symbol Guard) (before : Checked width) (handle depth : Nat)
    (known : Current source inventory initial before) (stored : Stored annotation before)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self)
    (bindings : SourceCurrentHereditaryNativeScope.Bindings annotation source request.domain.key)
    (left : SourceCurrentConstrainedCap.Cap annotation depth request.left)
    (right : SourceCurrentConstrainedCap.Cap annotation depth request.right) :
    let after : Checked width := {before with native := finishNode handle request.left before.native}
    Stored annotation after ∧ Available after.native.machine.heap request.left ∧
      SourceCurrentConstrainedCap.Cap annotation depth request.left := by
  classical
  have published := self_publication request before handle known stored running branch
  have certificate := SourceCurrentConstrainedCapNativeCode.request_node annotation source (MuStored annotation)
    depth request before.native.machine bindings left right
  have returned := next_node certificate published.1
  exact ⟨published.1.stored, returned⟩

#print axioms self_publication
#check @self_publication
#print axioms constructor_then_publication
#check @constructor_then_publication
#print axioms published_cap_continuation
#check @published_cap_continuation
end MicroCFTA.NativeCapGlueKernels
