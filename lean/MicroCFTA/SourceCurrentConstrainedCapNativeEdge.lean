import MicroCFTA.SourceCurrentConstrainedCapNativeCode
import MicroCFTA.SourceCurrentUnconstrainedGuardClosure
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion

/-!
# Finite-cap certificates for actual checked native edge code

Accepted children use one smaller cap depth. At depth zero, actual plain
conjunction readback supplies the hereditary guard. Positive depths impose
no root-guard predicate. Rejected branches emit the literal Top sentinel.
These are local compiler certificates, not recursive completion theorems.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeEdge
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryNativeScope (Bindings)
open SourceCurrentConstrainedCapNativeCode
open SourceCurrentConstrainedCap (Cap Edge)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Accepted literal child code derives the same row cap from its actual ordered callbacks. -/
theorem children_certified [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (depth : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (representation : InternedConstructorTemplates.State Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (represented : representation state.heap) (ready : EdgeReady state request)
    (bindings : Bindings annotation source request.domain.key)
    (left : Edge annotation depth request.left)
    (right : Edge annotation depth request.right)
    (combinedValid : depth = 0 → annotation (SourceEqualityConjoinAllocation.readback combined)) :
    Certified annotation source representation
      (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
      (fun after value => EdgeResident after.heap value ∧ Edge annotation depth value) := by
  let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain current request.domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
  let output := fun (current : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Available current.heap value ∧ Cap annotation (depth - 1) value
  have inputStable : Stable input := by
    intro before after growth pair known
    exact ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
  have outputStable : Stable output := by
    intro before after growth value returned
    exact ⟨growth.available _ returned.1, returned.2⟩
  have inputs : ∀ pair ∈ request.left.children.zip request.right.children, input state pair := by
    intro pair member
    have inside := List.of_mem_zip member
    exact ⟨ready.1, valid.1.cached.edges request.left.entry.key request.left ready.2.1 pair.1 inside.1,
      valid.1.cached.edges request.right.entry.key request.right ready.2.2 pair.2 inside.2⟩
  have walked := certified_walk annotation source representation
    (fun pair : Value Symbol Guard × Value Symbol Guard => requestNode request.domain pair.1 pair.2)
    (request.left.children.zip request.right.children) input output inputStable outputStable
    (by
      intro pair member current _ _ _
      have annotated := SourceCurrentConstrainedCapNativeScope.edge_child annotation depth request.left request.right left right pair member
      exact request_node annotation source representation (depth - 1) ⟨request.domain, pair.1, pair.2⟩ current bindings annotated.1 annotated.2)
    state valid represented inputs
  unfold SourceEqualityNativeCheckedCode.children
  apply certified_bind annotation source representation _ _ state valid represented _ _ walked
  intro values after afterValid _ _ returned
  exact edge_work annotation source representation depth request.left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values after afterValid
      (fun value member => (returned value member).1) combinedValid (fun value member => (returned value member).2)

/-- The literal sentinel has every cap depth and makes no recursive child request. -/
theorem sentinel_certified [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (depth : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (representation : InternedConstructorTemplates.State Symbol Guard → Prop)
    (left : EdgeValue Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state)
    (topValid : annotation SourceEqualityConstraintConstructors.top) :
    Certified annotation source representation (SourceEqualityNativeCheckedCode.sentinel left) state
      (fun after value => EdgeResident after.heap value ∧ Edge annotation depth value) := by
  apply edge_work annotation source representation depth left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]
    state valid _ (fun _ => topValid)
  · intro value member
    exact (List.mem_singleton.mp member) ▸ Cap.plain (depth - 1) Annotated.empty
  · intro value member
    exact (List.mem_singleton.mp member) ▸ empty_available _

/-- The supplied checked body yield certifies its own emitted code and returned machine. -/
theorem body_certified [DecidableEq (EdgeKey Symbol Guard)]
    (depth : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (representation : InternedConstructorTemplates.State Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (represented : representation before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (bindings : Bindings (fun guard => SourceMemoGate.plain guard = true) source request.domain.key)
    (left : Edge (fun guard => SourceMemoGate.plain guard = true) depth request.left)
    (right : Edge (fun guard => SourceMemoGate.plain guard = true) depth request.right)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    Certified (fun guard => SourceMemoGate.plain guard = true) source representation code after.native.machine
      (fun final value => EdgeResident final.heap value ∧
        Edge (fun guard => SourceMemoGate.plain guard = true) depth value) := by
  have same : after.native = before.native := by
    simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using
      SourceEqualityNativeDemandOperations.body_native request .pure before
  rw [same]
  by_cases arity : request.left.children.length = request.right.children.length
  · have matched : ¬ request.left.children.length ≠ request.right.children.length := by omega
    simp only [SourceEqualityNativeDemand.body, ite_eq_right matched] at yielded
    cases firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints with
    | error message => simp only [firstLoaded] at yielded; cases yielded
    | ok first =>
        cases first with
        | none => simp only [firstLoaded] at yielded; cases yielded
        | some first =>
            simp only [firstLoaded] at yielded
            cases secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints with
            | error message => simp only [secondLoaded] at yielded; cases yielded
            | ok second =>
                cases second with
                | none => simp only [secondLoaded] at yielded; cases yielded
                | some second =>
                    simp only [secondLoaded] at yielded
                    have firstCached := (good.fields _ _ ready.2.1).1
                    have secondCached := (good.fields _ _ ready.2.2).1
                    have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
                      firstCached first firstLoaded).1
                    have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
                      secondCached second secondLoaded).1
                    obtain ⟨branch, done, _, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct
                      GuardStructuralOrder.le first second request.left.children.length request.right.children.length
                      before.operations good.operations firstReady secondReady
                    cases branch with
                    | mismatch | rejected =>
                        simp only [done, SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
                        cases yielded
                        exact sentinel_certified _ depth source representation request.left _ good.native.machine
                          SourceCurrentUnconstrainedGuardClosure.top_plain
                    | ready combined =>
                        have combinedPlain : depth = 0 → SourceMemoGate.plain (SourceEqualityConjoinAllocation.readback combined) = true := by
                          intro zero
                          subst depth
                          exact SourceCurrentUnconstrainedGuardClosure.loaded_ready_plain
                            GuardStructuralOrder.le request.left.entry.key.constraint request.right.entry.key.constraint
                            first second request.left.children.length request.right.children.length before.operations good.operations
                            firstCached secondCached firstLoaded secondLoaded left.1 right.1 combined done
                        simp only [done, SourceEqualityNativeDemand.code_bind_pure] at yielded
                        cases yielded
                        exact children_certified _ depth source representation request combined _ good.native.machine represented ready
                          bindings left right combinedPlain
  · simp only [SourceEqualityNativeDemand.body, ite_eq_left arity, SourceEqualityNativeDemand.sentinel,
      SourceEqualityNativeDemand.code_bind_pure] at yielded
    cases yielded
    exact sentinel_certified _ depth source representation request.left _ good.native.machine
      SourceCurrentUnconstrainedGuardClosure.top_plain

end MicroCFTA.SourceCurrentConstrainedCapNativeEdge
