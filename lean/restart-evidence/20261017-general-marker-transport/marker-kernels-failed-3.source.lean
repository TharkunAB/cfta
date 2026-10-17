import MicroCFTA.SourceCurrentConstrainedCapMarkerTransport
import MicroCFTA.SourceEqualityRequiredSemanticCache
import MicroCFTA.InternedStoredRawIdentityBoundary

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

namespace MicroCFTA.GeneralMarkerKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol (Reference)
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitutionRebind (replacement)
open SourceCurrentConstrainedCapPairOccurrences (Classified)
open SourceCurrentConstrainedCapPairOccurrenceCallbacks (mark)
local notation "Heap" => InternedConstructorTemplates.State Nat Unit
local notation "V" => Value Nat Unit
private def old := Reference.intersection 7 9
private def weights (name : Reference) := if name = old then 1 else 0
private def expression := InternedStoredRawIdentityBoundary.expression
private def observation : Option (Bool × Nat × Nat × Bool × Bool) :=
  match InternedFreshOrdinaryConstruction.build expression [] (empty : Heap) with
  | .done (.mu _ body _ _) state =>
      match InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference .depth)) state with
      | .done value _ => some (body.referenceOf == value.referenceOf, body.depth, value.depth,
          decide (old ∈ body.free), decide (Reference.depth ∈ body.free))
      | .pending .. => none
  | _ => none

set_option cbv.maxSteps 100000000 in
private theorem observed : observation = some (false, 1, 0, false, false) := by cbv

/-- An actual open raw Mu reconstructs to a different record while general marker transport derives its classifier. -/
theorem constructed_open_mu_reconstruction :
    ∃ (root body value : V) (before after : Heap),
      InternedFreshOrdinaryConstruction.build expression [] (empty : Heap) = .done root before ∧
      Available before body ∧ body.depth = 1 ∧ value.depth = 0 ∧ body.referenceOf ≠ value.referenceOf ∧
      InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference .depth)) before = .done value after ∧
      Classified weights 1 body ∧ Classified (mark weights .depth 1) 1 value := by
  have computed := observed
  cases completed : InternedFreshOrdinaryConstruction.build expression [] (empty : Heap) with
  | pending key stopped => simp [observation, completed] at computed
  | done root before =>
      cases root with
      | empty | reference | node | union => simp [observation, completed] at computed
      | mu entry body depth ordinary =>
          cases executed : InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference .depth)) before with
          | pending key stopped => simp [observation, completed, executed] at computed
          | done value after =>
              simp only [observation, completed, executed, Option.some.injEq, Prod.mk.injEq] at computed
              have semantic := SourceEqualityRequiredSemanticCache.constructed expression (.mu entry body depth ordinary) before completed
              have rootAvailable := (InternedFreshOrdinaryFacts.build_verified expression [] (empty : Heap) empty_facts
                (by intro item member; cases member)).result _ _ completed
              have bodyAvailable := rootAvailable.children body (by simp [children])
              have absent : old ∉ body.free := of_decide_eq_false computed.2.2.2.1
              have fresh : Reference.depth ∉ body.free := of_decide_eq_false computed.2.2.2.2
              have classified : Classified weights 1 body := by
                have free : ∀ name ∈ body.free, weights name = 0 := by
                  intro name member
                  have different : name ≠ old := fun same => absent (same ▸ member)
                  simp [weights, different]
                refine ⟨fun name member => by rw [free name member]; omega, ?_⟩
                intro name member
                have named := InternedDeepFreeNormalization.deep_free body before semantic.ready.semantic.1.normal.facts.coherent
                  bodyAvailable name member
                rw [free name named]
                exact .inl (by omega)
              have result := SourceCurrentConstrainedCapMarkerTransport.transport body before semantic.ready.semantic.1
                semantic.ready.semantic.2 bodyAvailable old .depth (InternedNestedProvenance.depth_available before)
                weights 1 (by simp [weights]) classified fresh value after executed
              refine ⟨.mu entry body depth ordinary, body, value, before, after, rfl, bodyAvailable,
                computed.2.1, computed.2.2.1, ?_, executed, classified, result⟩
              intro same
              have contrary : (body.referenceOf == value.referenceOf) = true := by simp [same]
              rw [computed.1] at contrary
              cases contrary

#print axioms constructed_open_mu_reconstruction
#check @constructed_open_mu_reconstruction

/-- One actual general stored return constructs an unchanged-heap warm replay with its classifier derived again at that entry. -/
theorem general_warm_replay {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (body : Value Symbol Guard) (before : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context before captures)
    (depthHeap : InternedFreshOrdinaryDepthHeap.Heap before) (available : Available before body)
    (old marker : Reference) (markerAvailable : Available before (.reference marker))
    (weight : Reference → Nat) (bound : Nat) (oldWeight : weight old = bound)
    (classified : Classified weight bound body) (fresh : marker ∉ body.free)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference marker)) before = .done value after) :
    Classified (mark weight marker bound) bound value ∧
      InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference marker)) after = .done value after ∧
      InternedFreshOrdinaryContext.Context after
        ((InternedStoredSubstitution.leaves body).map (InternedStoredSubstitution.input (replacement old (.reference marker)))) ∧
      InternedFreshOrdinaryDepthHeap.Heap after := by
  have replacements : InternedStoredSubstitution.Replacements before (replacement old (.reference marker)) := by
    intro name result found
    by_cases same : name = old
    · simp only [replacement, same, ↓reduceIte, Option.some.injEq] at found
      exact found ▸ markerAvailable
    · simp [replacement, same] at found
  have inputs := InternedStoredSubstitution.inputs_available body (replacement old (.reference marker)) before available replacements
  have inputContext : InternedFreshOrdinaryContext.Context before
      ((InternedStoredSubstitution.leaves body).map (InternedStoredSubstitution.input (replacement old (.reference marker)))) :=
    ⟨context.normal, inputs, context.profiles, context.freeNames⟩
  let code := InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves body) [] body
  have physical := InternedFreshOrdinaryFacts.build_verified code _ before context.normal.facts inputs
  have afterContext : InternedFreshOrdinaryContext.Context after
      ((InternedStoredSubstitution.leaves body).map (InternedStoredSubstitution.input (replacement old (.reference marker)))) := by
    have retained := inputContext.build code
    change InternedFreshOrdinaryContext.Context
      (InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference marker)) before).state _ at retained
    simpa only [actual, Outcome.state] using retained
  have afterHeap : InternedFreshOrdinaryDepthHeap.Heap after := by
    have retained := (InternedRecordDepthExecution.build_depth code _ before inputContext depthHeap).heap
    change InternedFreshOrdinaryDepthHeap.Heap
      (InternedFreshOrdinaryStoredSubstitution.execute body (replacement old (.reference marker)) before).state at retained
    simpa only [actual, Outcome.state] using retained
  have bodyAfter : Available after body := by simpa only [actual, Outcome.state] using physical.available body available
  have markerAfter : Available after (.reference marker) := by
    simpa only [actual, Outcome.state] using physical.available (.reference marker) markerAvailable
  have replay := InternedFreshOrdinaryReplay.build_replay code _ before after value after context.normal.facts.coherent.valid actual (grows_refl after)
  exact ⟨SourceCurrentConstrainedCapMarkerTransport.transport body after afterContext afterHeap bodyAfter old marker markerAfter
    weight bound oldWeight classified fresh value after replay, replay, afterContext, afterHeap⟩

#print axioms general_warm_replay
#check @general_warm_replay
end MicroCFTA.GeneralMarkerKernels
