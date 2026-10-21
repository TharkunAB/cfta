import MicroCFTA.SourceCurrentConstrainedCapKernelJointExecution
import MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCompile

/-!
# Joint structural laws at actual checked code continuations

Each local request supplies its complete conditional result law. Primitive
continuations use the same actual returned machine and its joint context.
These certificates do not assert that a native request completes.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapCheckedJointCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs EdgeInputs edgeBudget)
open SourceCurrentConstrainedCapPairOccurrences (Classified FreeLE sourceWeight)
open SourceCurrentConstrainedCapNonplainRank (pairRank)
open SourceCurrentConstrainedCap (Cap Edge)
variable {Symbol Guard : Type}

/-- A returned node retains each supported finite cap, occurrence bound, and incoming scope. -/
def NodeLaw (annotation : Guard → Prop) (source : State Symbol Guard)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∀ depth, OriginalBindings annotation source request.domain.key → NodeInputs source request →
    Cap annotation depth request.left → Cap annotation depth request.right →
    Cap annotation depth value ∧
      Classified (sourceWeight annotation source) (pairRank annotation request.left request.right) value ∧
      SourceRecursiveIntersectionResultScope.Scope request.domain.key.seen value

/-- A returned row retains each supported cap, literal child budget, and incoming scope. -/
def EdgeLaw (annotation : Guard → Prop) (source : State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard) : Prop :=
  ∀ depth, OriginalBindings annotation source request.domain.key → EdgeInputs source request →
    Edge annotation depth request.left → Edge annotation depth request.right →
    Edge annotation depth value ∧
      (∀ child ∈ value.children, FreeLE (sourceWeight annotation source) (edgeBudget annotation request) child) ∧
      SourceRecursiveIntersectionResultScope.EdgeScope request.domain.key.seen value

variable (annotation : Guard → Prop) (source : State Symbol Guard)

/-- Literal source continuations consume actual primitive effects and exact smaller request laws. -/
def Certified [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A)
    (state : Machine Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match code with
  | .pure value => post state value
  | .fail _ => True
  | .work job next => ∀ value after,
      SourceRecursiveIntersectionKernel.work job state = .done value after →
      Extension state after → Context annotation source after → Certified (next value) after post
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      let after : Machine Symbol Guard := {state with domains := actual.2}
      Extension state after → Context annotation source after → Certified (next actual.1) after post
  | .read name next => Certified (next (SourcePreparedSharedRows.read state.heap name)) state post
  | .optionalBinder key body next => ∀ value after,
      construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state = .done value after →
      Extension state after → Context annotation source after → Certified (next value) after post
  | .node request next => ∀ value after, Extension state after → Context annotation source after →
      Available after.heap value → NodeLaw annotation source request value → Certified (next value) after post
  | .edge request next => ∀ value after, Extension state after → Context annotation source after →
      EdgeResident after.heap value → EdgeLaw annotation source request value → Certified (next value) after post
  | .finishNode .. | .finishEdge .. => False

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Ordered sequencing retains each exact earlier machine extension. -/
theorem certified_bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (context : Context annotation source state)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (certificate : Certified annotation source code state intermediate)
    (continuation : ∀ value after, Extension state after → Context annotation source after →
      intermediate after value → Certified annotation source (next value) after post) :
    Certified annotation source (code.bind next) state post := by
  induction code generalizing state with
  | pure value => exact continuation value state (.refl _) context certificate
  | fail => trivial
  | work job resume ih | optionalBinder key body resume ih =>
      intro value after actual growth afterContext
      exact ih value after afterContext (certificate value after actual growth afterContext)
        (fun result final later finalContext middle => continuation result final (growth.trans later) finalContext middle)
  | enter domain left right first second resume ih =>
      intro growth afterContext
      exact ih _ _ afterContext (certificate growth afterContext)
        (fun result final later finalContext middle => continuation result final (growth.trans later) finalContext middle)
  | read name resume ih => exact ih _ state context certificate continuation
  | node request resume ih | edge request resume ih =>
      intro value after growth afterContext physical law
      exact ih value after afterContext (certificate value after growth afterContext physical law)
        (fun result final later finalContext middle => continuation result final (growth.trans later) finalContext middle)
  | finishNode | finishEdge => cases certificate

/-- One literal code certificate can retain every conditional local postcondition. -/
theorem certified_forall {Index : Sort u} (code : Code Symbol Guard A) (state : Machine Symbol Guard)
    (post : Index → Machine Symbol Guard → A → Prop)
    (clean : BodyCode code)
    (certificates : ∀ index, Certified annotation source code state (post index)) :
    Certified annotation source code state (fun after value => ∀ index, post index after value) := by
  induction code generalizing state with
  | pure => exact certificates
  | fail => trivial
  | work job resume ih | optionalBinder key body resume ih =>
      intro value after actual growth context
      exact ih value after (clean value) (fun index => certificates index value after actual growth context)
  | enter domain left right first second resume ih =>
      intro growth context
      exact ih _ _ (clean _) (fun index => certificates index growth context)
  | read name resume ih => exact ih _ state (clean _) certificates
  | node request resume ih | edge request resume ih =>
      intro value after growth context physical law
      exact ih value after (clean value) (fun index => certificates index value after growth context physical law)
  | finishNode | finishEdge => cases clean

/-- A stronger postcondition retains the same literal continuation certificate. -/
theorem certified_mono (code : Code Symbol Guard A) (state : Machine Symbol Guard)
    (before after : Machine Symbol Guard → A → Prop)
    (certificate : Certified annotation source code state before)
    (implies : ∀ state value, before state value → after state value) :
    Certified annotation source code state after := by
  induction code generalizing state with
  | pure value => exact implies state value certificate
  | fail => trivial
  | work job resume ih | optionalBinder key body resume ih =>
      intro value final actual growth context
      exact ih value final (certificate value final actual growth context)
  | enter domain left right first second resume ih =>
      intro growth context
      exact ih _ _ (certificate growth context)
  | read name resume ih => exact ih _ state certificate
  | node request resume ih | edge request resume ih =>
      intro value final growth context physical law
      exact ih value final (certificate value final growth context physical law)
  | finishNode | finishEdge => cases certificate

end MicroCFTA.SourceCurrentConstrainedCapCheckedJointCode
