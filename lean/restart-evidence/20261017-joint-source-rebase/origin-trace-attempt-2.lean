import MicroCFTA.SourceCurrentConstrainedCapCheckedJointOrigins
import MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery

/-!
# Captured source origins through actual checked traces

The existing source admission certificate supplies each literal request.
Complete old input records derive the reads for every enclosing pair.
Lookup records these origins before publication. All other instructions
retain them. No returned-result law is an input to this trace proof.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointOriginTrace
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentConstrainedCapCheckedJointOrigins
open SourceCurrentAllocatedNativeContextRebase (NameCovered SeenCovered)
open SourceCurrentAllocatedNativeAdmissionTrace (ControlCertified)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} {A : Type}
variable (source : InternedConstructorTemplates.State Symbol Guard)
  (holds : Guard → Term Symbol → Bool) (inputs : FiniteInput (view source holds))

/-- A covered name has an original successful old payload read, including recursive references. -/
theorem name_read (facts : Facts source) (originals : ∀ input, inputs.valid input → OriginalInput source input)
    (name : Nat) (covered : NameCovered inputs name) :
    ∃ value, Original value ∧ SourcePreparedSharedRows.read source name = some value := by
  obtain ⟨input, valid, nonempty, same⟩ := covered
  subst name
  cases input with
  | empty => exact False.elim (nonempty rfl)
  | ref name =>
      obtain ⟨value, original, available, complete⟩ := originals (.mu name) (inputs.reference_valid name valid)
      cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input,
        Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
      case mu entry body depth ordinary original =>
        cases complete
        exact ⟨.mu entry body depth ordinary, .mu _ _ _ _ original,
          SourcePreparedSharedRows.read_identity source facts _ available entry.identity rfl⟩
  | node name | mu name | union name =>
      obtain ⟨value, original, available, complete⟩ := originals _ valid
      cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input,
        Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
      all_goals
        cases complete
        refine ⟨_, ?_, SourcePreparedSharedRows.read_identity source facts _ available _ rfl⟩
        constructor
        assumption

/-- Finite old input admission supplies complete original reads for every captured pair. -/
theorem seen (facts : Facts source) (originals : ∀ input, inputs.valid input → OriginalInput source input)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (covered : SeenCovered inputs domain) : Seen source domain := by
  intro pair member
  obtain ⟨left, leftOriginal, leftRead⟩ := name_read source holds inputs facts originals pair.1 (covered pair member).1
  obtain ⟨right, rightOriginal, rightRead⟩ := name_read source holds inputs facts originals pair.2 (covered pair member).2
  exact ⟨left, right, leftOriginal, rightOriginal, leftRead, rightRead⟩

/-- Only an instruction that can publish a cell needs a new captured origin. -/
def RequestOrigin : Control A → Prop
  | .code (.node request _) => NodeOrigin source request
  | .code (.edge request _) => EdgeOrigin source request
  | _ => True

/-- The source certificate derives the origin before its actual lookup publishes a request. -/
theorem current [DecidableEq (EdgeKey Symbol Guard)]
    (facts : Facts source) (originals : ∀ input, inputs.valid input → OriginalInput source input)
    (control : Control A) (machine : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop)
    (certificate : ControlCertified source holds inputs control machine post) : RequestOrigin source control := by
  cases control with
  | edgeBody => trivial
  | code code =>
      cases code with
      | node request next | edge request next =>
          exact ⟨certificate.1, seen source holds inputs facts originals request.domain.key certificate.2.1.2⟩
      | pure | fail | work | enter | read | optionalBinder | finishNode | finishEdge => trivial

/-- Every actual instruction retains origins for all allocated memo phases. -/
theorem step_stored [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (control : Control A) (state : Checked width) (origins : Stored source state.native)
    (current : RequestOrigin source control) : Stored source (step control state).state.native := by
  cases control with
  | edgeBody request next =>
      change Stored source (body request next state).state.native
      rw [SourceEqualityNativeDemandOperations.body_native]
      exact origins
  | code code =>
      cases code with
      | pure | fail | read => exact origins
      | work job next | enter domain left right first second next => exact advance_stored source state.native _ origins
      | optionalBinder pair value next =>
          cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair value state.native.machine.heap with
          | done result heap | pending key heap =>
              simpa only [step, SourceRecursiveIntersectionNative.step, actual, lift, Outcome.state] using
                advance_stored source state.native {state.native.machine with heap := heap} origins
      | node request next =>
          have chosenOrigins := lookupNode_stored source state.native request origins current
          cases lookup : lookupNode width request state.native with
          | mk selection chosen =>
              simp only [lookup] at chosenOrigins
              cases selection with
              | direct actual =>
                  simpa only [step, SourceRecursiveIntersectionNative.step, lookup, lift, Outcome.state] using chosenOrigins
              | memoized handle =>
                  have retained := demandNode_stored source chosen handle chosenOrigins
                  cases demand : demandNode handle chosen with
                  | mk observation after =>
                      simp only [demand] at retained
                      cases observation <;>
                        simpa only [step, SourceRecursiveIntersectionNative.step, lookup, demand, lift, Outcome.state] using retained
      | edge request next =>
          have chosenOrigins := lookupEdge_stored source state.native request origins current
          cases lookup : lookupEdge width request state.native with
          | mk handle chosen =>
              simp only [lookup] at chosenOrigins
              have retained := demandEdge_stored source chosen handle chosenOrigins
              cases demand : demandEdge handle chosen with
              | mk observation after =>
                  simp only [demand] at retained
                  cases observation <;> simpa only [step, lookup, demand, Outcome.state] using retained
      | finishNode handle value next => exact finishNode_stored source state.native handle value origins
      | finishEdge handle value next => exact finishEdge_stored source state.native handle value origins

/-- The same physical trace derives all final request origins from initial origins and source admission. -/
theorem Trace.origins [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (facts : Facts source) (originals : ∀ input, inputs.valid input → OriginalInput source input)
    {fuel : Nat} {control next : Control A} {before after : Checked width}
    (trace : Trace fuel control before next after) (post : Machine Symbol Guard → A → Prop)
    (good : Good before) (semantic : SemanticReady before.native.machine.heap)
    (growth : Grows source before.native.machine.heap)
    (history : Extends source.nodes.issued before.native.machine.heap.nodes.issued)
    (fields : Fields control before) (stored : Stored source before.native)
    (certificate : ControlCertified source holds inputs control before.native.machine post) :
    Stored source after.native ∧ ControlCertified source holds inputs next after.native.machine post := by
  induction trace with
  | refl => exact ⟨stored, certificate⟩
  | cons control before resume reached final result fuel physical one tail ih =>
      have actual := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good physical fields
      have effects : Good reached ∧ Extension before.native.machine reached.native.machine ∧
          SourceEqualityRequiredCache.Keeps before.native.machine.heap reached.native.machine.heap ∧
          SourceEqualityConstraintMemoAllocation.Grows before.operations reached.operations ∧
          SourceCurrentConjunctionEquality.Fields reached.operations reached.native.machine.heap ∧ Fields resume reached := by
        simpa only [one, Outcome.state, SourceCurrentAllocatedNativeFieldClosure.OutcomeFields] using actual
      have ready := SourceCurrentAllocatedNativeSemanticHeap.step_semantic control before semantic
        (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before physical)
      have reachedSemantic : SemanticReady reached.native.machine.heap := by simpa only [one, Outcome.state] using ready
      have retained := step_stored source control before stored
        (current source holds inputs facts originals control before.native.machine post certificate)
      have reachedOrigins : Stored source reached.native := by simpa only [one, Outcome.state] using retained
      have nextCertificate := SourceCurrentAllocatedNativeAdmissionTrace.yielded_certified source holds inputs
        (SourceCurrentAllocatedNativeCoveredQuery.branches source facts holds inputs) control resume before reached post
        good semantic growth history physical fields certificate one
      exact ih effects.1 reachedSemantic (grows_trans growth effects.2.1.heap)
        (extends_trans history effects.2.1.history) effects.2.2.2.2.2 reachedOrigins nextCertificate

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointOriginTrace
