import MicroCFTA.InternedRecordDepthShape
import MicroCFTA.InternedFreeNameInputSubset

/-!
# Actual source free and profile observations from captured records

The lexical inputs can contain arbitrary available records. Their decoded
shapes retain actual profiles and free-name membership. Existing repaired
source proofs supply the corresponding returned observations.
-/
namespace MicroCFTA.InternedRecordDepthSource
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedRecordDepthShape
open InternedDepthSemantics
open InternedBinderProtocol (Reference)

/-- The richer free-name interpretation agrees with the original actual-record input interpretation. -/
theorem evaluate_free (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (available : ∀ value ∈ environment, Available state value)
    (name : Reference) :
    name ∈ (evaluate expression (environment.map shape)).free ↔
      name ∈ InternedFreeNameSemantics.evaluate expression (environment.map InternedRootProfile.profile) (environment.map Value.free) := by
  have projected := InternedDepthFreeProjection.evaluate_member expression (environment.map shape) (input_coherent environment) name
  rw [input_profiles] at projected
  apply projected.trans
  constructor
  · exact InternedFreeNameInputSubset.evaluate_included expression _ _ _
      (fun index name member => (input_free environment state coherent available index name).mp member) name
  · exact InternedFreeNameInputSubset.evaluate_included expression _ _ _
      (fun index name member => (input_free environment state coherent available index name).mpr member) name

/-- Full repaired source returns the richer shape's exact free-name membership for arbitrary captured records. -/
theorem source_free [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : build expression environment state = .done value after) (name : Reference) :
    name ∈ value.free ↔ name ∈ (evaluate expression (environment.map shape)).free :=
  ((InternedFreshOrdinaryFreeNames.build_free expression environment state context.normal context.inputs context.freeNames context.profiles).result
    value after done name).trans (evaluate_free expression environment state context.normal.facts.coherent context.inputs name).symm

/-- Full repaired source returns the richer shape's exact empty decision for arbitrary captured records. -/
theorem source_empty [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : build expression environment state = .done value after) :
    (value.referenceOf == .empty) = (evaluate expression (environment.map shape)).isEmpty := by
  have verified := InternedFreshOrdinaryFacts.build_verified expression environment state context.normal.facts context.inputs
  have afterContext : Context after environment := by simpa only [done, Outcome.state] using context.build expression
  have actual := (InternedFreshOrdinaryProfiles.build_profile expression environment state context.normal context.inputs context.profiles).result value after done
  have projected := InternedDepthSemanticProjections.evaluate_profile expression (environment.map shape) (input_coherent environment)
  rw [input_profiles] at projected
  rw [← InternedRootProfileNode.isEmpty_profile value after afterContext.normal.proper (verified.result _ _ done),
    InternedProfileComposition.isEmpty_same actual, ← projected]
  exact InternedDepthSemanticProjections.profile_empty _

/-- An actual ordinary source root has the richer shape's exact deep names with arbitrary nested children and captured records. -/
theorem source_node_deep [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : build (.node edges) environment state = .done value after) (name : Reference) :
    name ∈ InternedDeepFreeDepth.deepNames value ↔ name ∈ (evaluate (.node edges) (environment.map shape)).deep := by
  rw [InternedDepthFreeProjectionSource.node_deep_eq_free edges environment state context value after done]
  have free := source_free (.node edges) environment state context value after done name
  simpa only [evaluate, Shape.free, InternedDepthSemanticProjections.edges_roots, List.nil_append] using free

end MicroCFTA.InternedRecordDepthSource
