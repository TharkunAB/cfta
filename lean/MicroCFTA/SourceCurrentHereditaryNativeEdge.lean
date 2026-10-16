import MicroCFTA.SourceCurrentHereditaryNativeCode
import MicroCFTA.SourceCurrentUnconstrainedGuardClosure
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion

/-!
# Local annotations of actual checked edge code

Accepted child code uses the two original annotated rows and their bindings.
The final edge uses the actual allocated conjunction readback. Stopped branches
emit the literal Top sentinel. No unrelated heap annotation is required.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativeEdge
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage SourceCurrentHereditaryNativeScope
open SourceCurrentHereditaryNativeCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Accepted literal child code derives its complete result annotation from the two queried rows. -/
theorem children_certified [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (representation : InternedConstructorTemplates.State Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (represented : representation state.heap) (ready : EdgeReady state request)
    (bindings : Bindings annotation source request.domain.key)
    (left : SourceCurrentHereditaryConstructors.Edge annotation request.left)
    (right : SourceCurrentHereditaryConstructors.Edge annotation request.right)
    (combinedValid : annotation (SourceEqualityConjoinAllocation.readback combined)) :
    Certified annotation source representation
      (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) state
      (fun after value => EdgeResident after.heap value ∧ SourceCurrentHereditaryConstructors.Edge annotation value) := by
  let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain current request.domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
  let output := fun (current : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Available current.heap value ∧ Annotated annotation value
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
      have annotated := edge_child annotation request.left request.right left right pair member
      exact request_node annotation source representation ⟨request.domain, pair.1, pair.2⟩ current bindings annotated.1 annotated.2)
    state valid represented inputs
  unfold SourceEqualityNativeCheckedCode.children
  apply certified_bind annotation source representation _ _ state valid represented _ _ walked
  intro values after afterValid _ _ returned
  exact edge_work annotation source representation request.left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values after afterValid
      (fun value member => (returned value member).1) combinedValid (fun value member => (returned value member).2)

/-- The literal sentinel constructs its annotation without a recursive child request. -/
theorem sentinel_certified [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (representation : InternedConstructorTemplates.State Symbol Guard → Prop)
    (left : EdgeValue Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state)
    (topValid : annotation SourceEqualityConstraintConstructors.top) :
    Certified annotation source representation (SourceEqualityNativeCheckedCode.sentinel left) state
      (fun after value => EdgeResident after.heap value ∧ SourceCurrentHereditaryConstructors.Edge annotation value) := by
  apply edge_work annotation source representation left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]
    state valid _ topValid
  · intro value member
    exact (List.mem_singleton.mp member) ▸ Annotated.empty
  · intro value member
    exact (List.mem_singleton.mp member) ▸ empty_available _

/-- The supplied checked body yield certifies its own emitted code and returned machine. -/
theorem body_certified [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard)
    (representation : InternedConstructorTemplates.State Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (represented : representation before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (bindings : Bindings (fun guard => SourceMemoGate.plain guard = true) source request.domain.key)
    (left : SourceCurrentHereditaryConstructors.Edge (fun guard => SourceMemoGate.plain guard = true) request.left)
    (right : SourceCurrentHereditaryConstructors.Edge (fun guard => SourceMemoGate.plain guard = true) request.right)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    Certified (fun guard => SourceMemoGate.plain guard = true) source representation code after.native.machine
      (fun final value => EdgeResident final.heap value ∧
        SourceCurrentHereditaryConstructors.Edge (fun guard => SourceMemoGate.plain guard = true) value) := by
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
                        exact sentinel_certified _ source representation request.left _ good.native.machine
                          SourceCurrentUnconstrainedGuardClosure.top_plain
                    | ready combined =>
                        have combinedPlain := SourceCurrentUnconstrainedGuardClosure.loaded_ready_plain
                          GuardStructuralOrder.le request.left.entry.key.constraint request.right.entry.key.constraint
                          first second request.left.children.length request.right.children.length before.operations good.operations
                          firstCached secondCached firstLoaded secondLoaded left.1 right.1 combined done
                        simp only [done, SourceEqualityNativeDemand.code_bind_pure] at yielded
                        cases yielded
                        exact children_certified _ source representation request combined _ good.native.machine represented ready
                          bindings left right combinedPlain
  · simp only [SourceEqualityNativeDemand.body, ite_eq_left arity, SourceEqualityNativeDemand.sentinel,
      SourceEqualityNativeDemand.code_bind_pure] at yielded
    cases yielded
    exact sentinel_certified _ source representation request.left _ good.native.machine
      SourceCurrentUnconstrainedGuardClosure.top_plain

end MicroCFTA.SourceCurrentHereditaryNativeEdge
