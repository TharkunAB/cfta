import MicroCFTA.SourceCurrentAllocatedRecursivePrefixAdmission

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.RecursivePrefixInductionIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceCurrentAllocatedRecursivePrefixState
open SourceCurrentAllocatedRecursivePrefixReceipt (Receipt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable {bits : Nat} {source : InternedConstructorTemplates.State Symbol Guard}
variable {inventory : List DomainKey} {initial : Cache.State DomainKey}

/-- An actual compiled body publishes its own returned value at its captured node owner. -/
theorem node_body_finish (resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory initial)
    (fuel handle : Nat) (request : NodeRequest Symbol Guard) (before middle : Checked (bits + 2))
    (value : Value Symbol Guard) (current : Current source inventory initial before)
    (scope : NodeScope source request) (member : request.domain.key ∈ inventory)
    (ready : NodeReady before.native.machine request)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (body : Steps fuel (.code (compileNode request)) before (.code (.pure value)) middle) :
    let finished : Checked (bits + 2) := {middle with native := finishNode handle value middle.native}
    Receipt source inventory initial (fuel + 1)
      ((.code (compileNode request) : Control (Value Symbol Guard)).bind (fun result => .finishNode handle result (.pure result)))
      before (.code (.pure value)) finished (fun after result => Available after.heap result) ∧
      Available finished.native.machine.heap value ∧
      finished.native.nodes.cells handle = some ⟨request, .returned value⟩ ∧
      finished.operations = middle.operations := by
  dsimp only
  let finished : Checked (bits + 2) := {middle with native := finishNode handle value middle.native}
  have certificate := SourceCurrentAllocatedRecursivePrefixCode.node_certified source inventory resources.facts
    resources.closed request scope member before.native.machine current.good.native.machine current.semantic ready
    current.growth current.history
  have fields := SourceCurrentAllocatedNativeCodeFields.compileNode_fields before.operations request
  have wrapped := body.bind fuel _ _ before middle body (fun result => .finishNode handle result (.pure result))
  have one : Steps 1 (.code (.finishNode handle value (.pure value))) middle (.code (.pure value)) finished :=
    .cons _ _ _ _ _ _ _ rfl (.refl _ _)
  have actual := wrapped.trans fuel 1 _ _ _ before middle finished wrapped one
  have receipt := SourceCurrentAllocatedRecursivePrefixInduction.node_bind (fuel + 2) (fuel + 1) handle
    (fun count _ => SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources count) (by omega)
    request .pure before finished (.code (.pure value)) (fun after result => Available after.heap result)
    current certificate fields (fun _ => trivial) running
    (fun _ _ _ _ available => ⟨available, trivial, available⟩) actual
  have owner := SourceEqualityNativeDemandProtectedPrefix.node_body_owner fuel handle request before middle value
    current.good.native.shape running body
  exact ⟨receipt, receipt.result value rfl, owner.2, rfl⟩

/-- The exact checked edge body supplies residency before its captured owner receives the result. -/
theorem edge_body_finish (resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory initial)
    (fuel handle : Nat) (request : EdgeRequest Symbol Guard) (before middle : Checked (bits + 2))
    (value : EdgeValue Symbol Guard) (current : Current source inventory initial before)
    (scope : EdgeScope source request) (member : request.domain.key ∈ inventory)
    (ready : EdgeReady before.native.machine request)
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (body : Steps fuel (.edgeBody request .pure) before (.code (.pure value)) middle) :
    let finished : Checked (bits + 2) := {middle with native := finishEdge handle value middle.native}
    Receipt source inventory initial (fuel + 1)
      ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind (fun result => .finishEdge handle result (.pure result)))
      before (.code (.pure value)) finished (fun after result => EdgeResident after.heap result) ∧
      EdgeResident finished.native.machine.heap value ∧
      finished.native.edges.cells handle = some ⟨request, .returned value⟩ ∧
      finished.operations = middle.operations := by
  dsimp only
  let finished : Checked (bits + 2) := {middle with native := finishEdge handle value middle.native}
  have certificate := SourceCurrentAllocatedRecursivePrefixControl.edge_body source inventory request before.native.machine
    scope member ready
  have wrapped := body.bind fuel _ _ before middle body (fun result => .finishEdge handle result (.pure result))
  have one : Steps 1 (.code (.finishEdge handle value (.pure value))) middle (.code (.pure value)) finished :=
    .cons _ _ _ _ _ _ _ rfl (.refl _ _)
  have actual := wrapped.trans fuel 1 _ _ _ before middle finished wrapped one
  have receipt := SourceCurrentAllocatedRecursivePrefixInduction.edge_bind (fuel + 2) (fuel + 1) handle
    (fun count _ => SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources count) (by omega)
    request .pure before finished (.code (.pure value)) (fun after result => EdgeResident after.heap result)
    current certificate ⟨ready, fun _ => trivial⟩ (fun _ => trivial) running
    (fun _ _ _ _ resident => ⟨resident, trivial, resident⟩) actual
  have owner := SourceEqualityNativeDemandProtectedPrefix.edge_body_owner fuel handle request before middle value
    current.good.native.shape running body
  exact ⟨receipt, receipt.result value rfl, owner.2, rfl⟩

/-- An unfinished actual body prefix retains its outer finish and has no pure output. -/
theorem node_inside_vacuous (resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits source inventory initial)
    (fuel handle : Nat) (request : NodeRequest Symbol Guard) (before after : Checked (bits + 2))
    (remaining : Control (Value Symbol Guard)) (current : Current source inventory initial before)
    (scope : NodeScope source request) (member : request.domain.key ∈ inventory)
    (ready : NodeReady before.native.machine request)
    (body : Steps fuel (.code (compileNode request)) before remaining after)
    (nonpure : ∀ result, remaining ≠ .code (.pure result)) :
    Receipt source inventory initial fuel
      ((.code (compileNode request) : Control (Value Symbol Guard)).bind (fun result => .finishNode handle result (.pure result)))
      before (remaining.bind (fun result => .finishNode handle result (.pure result))) after (fun _ _ => False) ∧
      ∀ result, remaining.bind (fun value => .finishNode handle value (.pure value)) ≠ .code (.pure result) := by
  have certificate := SourceCurrentAllocatedRecursivePrefixCode.node_certified source inventory resources.facts
    resources.closed request scope member before.native.machine current.good.native.machine current.semantic ready
    current.growth current.history
  have admitted := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel _ before remaining after
    (fun final value => Available final.heap value) current certificate
    (SourceCurrentAllocatedNativeCodeFields.compileNode_fields before.operations request) body
  exact ⟨SourceCurrentAllocatedRecursivePrefixReceipt.bind_inside (fun value => .finishNode handle value (.pure value))
      admitted nonpure (fun _ => trivial) (fun _ _ => False),
    SourceEqualityNativeDemandProtectedPrefix.bind_nonpure remaining _ nonpure⟩

#print axioms node_body_finish
#check @node_body_finish
#print axioms edge_body_finish
#check @edge_body_finish
#print axioms node_inside_vacuous
#check @node_inside_vacuous

end MicroCFTA.RecursivePrefixInductionIndependent
