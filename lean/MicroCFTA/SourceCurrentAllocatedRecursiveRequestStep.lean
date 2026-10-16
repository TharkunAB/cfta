import MicroCFTA.SourceCurrentAllocatedNativePhysicalExecution

/-!
# Exact yielded current request branches

Physical memo validity and current request words identify captured owners.
A yielded instruction excludes absent and busy observations. The result
retains the exact continuation, machine, and equality-operation state.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursiveRequestStep
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Control" => SourceEqualityNativeDemand.Control
local notation "Words" => SourceCurrentAllocatedNativeRequestBounds.Words
local notation "PhysicalValid" => SourceCurrentAllocatedNativePhysicalCache.Valid
variable {width : Nat} {A : Type}

/-- A yielded node demand is direct, ready, or evaluating its exact original request. -/
theorem node_yielded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (before : Checked width) (control : Control A) (after : Checked width)
    (valid : PhysicalValid before.native) (ready : NodeReady before.native.machine request)
    (words : Words width (.code (.node request next)))
    (yielded : SourceEqualityNativeDemand.step (.code (.node request next)) before = .yielded control after) :
    after.native.machine = before.native.machine ∧ after.operations = before.operations ∧
      ((control = .code ((compileNode request).bind next) ∧ after = before) ∨
      (∃ value, control = .code (next value) ∧ Available after.native.machine.heap value) ∨
      (∃ handle, control = .code ((compileNode request).bind
        (fun value => .finishNode handle value (next value))) ∧
        after.native.nodes.cells handle = some ⟨request, .evaluating⟩)) := by
  cases selected : lookupNode width request before.native with
  | mk selection chosen =>
    have chosenMachine : chosen.machine = before.native.machine := by
      simpa only [selected] using SourceRecursiveIntersectionNative.lookupNode_machine request before.native
    cases selection with
    | direct actual =>
      obtain ⟨rfl, rfl⟩ := SourceRecursiveIntersectionNative.lookupNode_direct request actual before.native chosen selected
      simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected,
        SourceEqualityNativeDemand.lift] at yielded
      cases yielded
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | memoized handle =>
      obtain ⟨key, encoded, _, _⟩ :=
        SourceRecursiveIntersectionNative.lookupNode_memoized request before.native chosen handle selected
      have safe := words key encoded
      cases demanded : demandNode handle chosen with
      | mk observation running =>
        have machine : running.machine = before.native.machine := by
          simpa only [demanded, chosenMachine] using SourceRecursiveIntersectionNative.demandNode_machine handle chosen
        cases observation with
        | absent | busy =>
          simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded,
            SourceEqualityNativeDemand.lift] at yielded
          cases yielded
        | ready value =>
          have receipt := SourceCurrentAllocatedNativePhysicalCache.node_ready request before.native chosen running
            handle value valid ready safe selected demanded
          simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded,
            SourceEqualityNativeDemand.lift] at yielded
          cases yielded
          exact ⟨machine, rfl, Or.inr (Or.inl ⟨value, rfl, receipt.2.2⟩)⟩
        | evaluate actual =>
          have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual before.native chosen running
            handle valid ready safe selected demanded
          subst actual
          have owner := (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen running request demanded).2
          simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded,
            SourceEqualityNativeDemand.lift] at yielded
          cases yielded
          exact ⟨machine, rfl, Or.inr (Or.inr ⟨handle, rfl, owner⟩)⟩

/-- A yielded edge demand is ready or enters its exact original checked body. -/
theorem edge_yielded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before : Checked width) (control : Control A) (after : Checked width)
    (valid : PhysicalValid before.native) (ready : EdgeReady before.native.machine request)
    (words : Words width (.code (.edge request next)))
    (yielded : SourceEqualityNativeDemand.step (.code (.edge request next)) before = .yielded control after) :
    after.native.machine = before.native.machine ∧ after.operations = before.operations ∧
      ((∃ value, control = .code (next value) ∧ EdgeResident after.native.machine.heap value) ∨
      (∃ handle, control = .edgeBody request (fun value => .finishEdge handle value (next value)) ∧
        after.native.edges.cells handle = some ⟨request, .evaluating⟩)) := by
  cases selected : lookupEdge width request before.native with
  | mk handle chosen =>
    have chosenMachine : chosen.machine = before.native.machine := by
      simpa only [selected] using SourceRecursiveIntersectionNative.lookupEdge_machine request before.native
    cases demanded : demandEdge handle chosen with
    | mk observation running =>
      have machine : running.machine = before.native.machine := by
        simpa only [demanded, chosenMachine] using SourceRecursiveIntersectionNative.demandEdge_machine handle chosen
      cases observation with
      | absent | busy =>
        simp only [SourceEqualityNativeDemand.step, selected, demanded] at yielded
        cases yielded
      | ready value =>
        have receipt := SourceCurrentAllocatedNativePhysicalCache.edge_ready request before.native chosen running handle
          value valid ready words selected demanded
        simp only [SourceEqualityNativeDemand.step, selected, demanded] at yielded
        cases yielded
        exact ⟨machine, rfl, Or.inl ⟨value, rfl, receipt.2.2⟩⟩
      | evaluate actual =>
        have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual before.native chosen running
          handle valid ready words selected demanded
        subst actual
        have owner := (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen running request demanded).2
        simp only [SourceEqualityNativeDemand.step, selected, demanded] at yielded
        cases yielded
        exact ⟨machine, rfl, Or.inr ⟨handle, rfl, owner⟩⟩

end MicroCFTA.SourceCurrentAllocatedRecursiveRequestStep
