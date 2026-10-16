import MicroCFTA.SourceCurrentAllocatedRecursiveRequestStep
import MicroCFTA.SourceCurrentHereditaryNativeCache

/-!
# Local native laws at actual yielded request transitions

Lookup and demand retain all earlier local returned-cell certificates.
Warm observations recover the law for the exact requested operands.
Started requests retain their literal evaluating owner and continuation.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativeTransition
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentHereditaryNativeCode (NodeLaw EdgeLaw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Control" => SourceEqualityNativeDemand.Control
local notation "Words" => SourceCurrentAllocatedNativeRequestBounds.Words
local notation "PhysicalValid" => SourceCurrentAllocatedNativePhysicalCache.Valid
variable {width : Nat} {A : Type}

/-- A yielded node demand is direct, ready, or evaluating its exact original request. -/
theorem node_yielded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : State Symbol Guard)
    (request : NodeRequest Symbol Guard) (next : Value Symbol Guard → Code Symbol Guard A)
    (before : Checked width) (control : Control A) (after : Checked width)
    (valid : PhysicalValid before.native)
    (stored : SourceCurrentHereditaryNativeCache.Stored annotation source before.native)
    (ready : NodeReady before.native.machine request)
    (words : Words width (.code (.node request next)))
    (yielded : SourceEqualityNativeDemand.step (.code (.node request next)) before = .yielded control after) :
    after.native.machine = before.native.machine ∧ after.operations = before.operations ∧
      SourceCurrentHereditaryNativeCache.Stored annotation source after.native ∧
      ((control = .code ((compileNode request).bind next) ∧ after = before) ∨
      (∃ value, control = .code (next value) ∧ Available after.native.machine.heap value ∧ NodeLaw annotation source request value) ∨
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
      exact ⟨rfl, rfl, stored, Or.inl ⟨rfl, rfl⟩⟩
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
          have receipt := SourceCurrentHereditaryNativeCache.node_observed_ready annotation source request before.native chosen running
            handle value valid stored ready safe selected demanded
          simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded,
            SourceEqualityNativeDemand.lift] at yielded
          cases yielded
          exact ⟨machine, rfl, receipt.2.1, Or.inr (Or.inl ⟨value, rfl, receipt.2.2.2, receipt.1⟩)⟩
        | evaluate actual =>
          have started := SourceCurrentHereditaryNativeCache.node_started annotation source request actual before.native chosen running
            handle valid stored ready safe selected demanded
          have same := started.1
          subst actual
          simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded,
            SourceEqualityNativeDemand.lift] at yielded
          cases yielded
          exact ⟨machine, rfl, started.2.2.1, Or.inr (Or.inr ⟨handle, rfl, started.2.2.2⟩)⟩

/-- A yielded edge demand is ready or enters its exact original checked body. -/
theorem edge_yielded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (next : EdgeValue Symbol Guard → Code Symbol Guard A)
    (before : Checked width) (control : Control A) (after : Checked width)
    (valid : PhysicalValid before.native)
    (stored : SourceCurrentHereditaryNativeCache.Stored annotation source before.native)
    (ready : EdgeReady before.native.machine request)
    (words : Words width (.code (.edge request next)))
    (yielded : SourceEqualityNativeDemand.step (.code (.edge request next)) before = .yielded control after) :
    after.native.machine = before.native.machine ∧ after.operations = before.operations ∧
      SourceCurrentHereditaryNativeCache.Stored annotation source after.native ∧
      ((∃ value, control = .code (next value) ∧ EdgeResident after.native.machine.heap value ∧ EdgeLaw annotation source request value) ∨
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
        have receipt := SourceCurrentHereditaryNativeCache.edge_observed_ready annotation source request before.native chosen running handle
          value valid stored ready words selected demanded
        simp only [SourceEqualityNativeDemand.step, selected, demanded] at yielded
        cases yielded
        exact ⟨machine, rfl, receipt.2.1, Or.inl ⟨value, rfl, receipt.2.2.2, receipt.1⟩⟩
      | evaluate actual =>
        have started := SourceCurrentHereditaryNativeCache.edge_started annotation source request actual before.native chosen running
          handle valid stored ready words selected demanded
        have same := started.1
        subst actual
        simp only [SourceEqualityNativeDemand.step, selected, demanded] at yielded
        cases yielded
        exact ⟨machine, rfl, started.2.2.1, Or.inr ⟨handle, rfl, started.2.2.2⟩⟩

end MicroCFTA.SourceCurrentHereditaryNativeTransition
