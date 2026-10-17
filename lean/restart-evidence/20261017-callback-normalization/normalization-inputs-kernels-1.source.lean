import MicroCFTA.SourceCurrentNativeNormalizationInputs
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 200000000

namespace MicroCFTA.NativeNormalizationInputKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreshOrdinaryLiveInputs (input)
open SourceCurrentNativeNormalizationInputs

private def valueOf (outcome : Outcome Nat Unit (Value Nat Unit)) : Value Nat Unit :=
  match outcome with
  | .done value _ => value
  | .pending _ _ => .empty

private def firstInputs : List (Sum (Value Nat Unit) Unit) := [.inl (.reference (.uninterned 0)), .inr ()]
private def firstNames (_ : Unit) : Reference := .intersection 2 3
private def firstBody : Syntax Nat Unit :=
  .union [.var 0, .node [.mk 0 () [.empty, .var 1]], .node [.mk 1 () [.var 2]]]
private def firstCall := callback firstBody (firstInputs.map (input firstNames)) .depth empty

private theorem first_context : Context (empty : State Nat Unit) (firstInputs.map (input firstNames)) := by
  apply SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap
  intro value member
  change value ∈ [.reference (.uninterned 0), .reference (.intersection 2 3)] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact InternedNestedProvenance.ordinary_available empty 0
  · rcases List.mem_cons.mp member with rfl | impossible
    · exact reference_available empty (.intersection 2 3) (by intro identity impossible; cases impossible)
    · cases impossible

private theorem first_done :
    callback firstBody (firstInputs.map (input firstNames)) .depth empty =
      .done (valueOf firstCall) firstCall.state := by cbv

/-- A discarded fixed capture can equal the chosen ordinary name while live fixed support remains fresh. -/
theorem discarded_fixed_capture :
    ∃ depth after,
      callback firstBody (firstInputs.map (input firstNames)) .depth empty = .done depth after ∧
      .inl (.reference (.uninterned (ordinaryLevel depth))) ∈ firstInputs ∧
      .inl (.uninterned (ordinaryLevel depth)) ∉ support (.binder true firstBody) firstInputs ∧
      .inr () ∈ support (.binder true firstBody) firstInputs := by
  have fresh := ordinary_fresh_fixed firstBody firstInputs firstNames empty firstCall.state
    first_context (valueOf firstCall) first_done
  exact ⟨valueOf firstCall, firstCall.state, first_done, by cbv; simp, fresh, by cbv; simp⟩

private def original : Syntax Nat Unit := .binder false (.node [.mk 3 () [.var 0, .var 1]])
private def originalInputs : List (Value Nat Unit) := [.reference (.uninterned 7)]
private def originalCall := build original originalInputs empty
private def originalValue := valueOf originalCall
private def originalHeap := originalCall.state

private theorem original_done : build original originalInputs empty = .done originalValue originalHeap := by cbv

private theorem original_values : InternedNestedProvenance.Values (empty : State Nat Unit) originalInputs := by
  intro value member
  have same : value = .reference (.uninterned 7) := List.mem_singleton.mp member
  subst value
  exact InternedNestedProvenance.ordinary_available empty 7

private theorem original_available : Available originalHeap originalValue :=
  (build_verified original originalInputs empty InternedStoredMuOrigins.empty_normal.facts original_values).result
    _ _ original_done

private theorem original_semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap originalHeap := by
  have retained := SourceRecursiveIntersectionSemanticHeap.source original originalInputs empty
    SourceRecursiveIntersectionSemanticHeap.empty_heap original_values
  simpa only [original_done, Outcome.state] using retained

private def secondInputs : List (Sum (Value Nat Unit) Unit) := [.inl originalValue, .inr ()]
private def secondNames (_ : Unit) : Reference := .uninterned 20
private def secondBody : Syntax Nat Unit := .union [.var 0, .var 1, .node [.mk 4 () [.empty, .var 2]]]
private def depthCall := callback secondBody (secondInputs.map (input secondNames)) .depth originalHeap
private def ordinaryCall := callback secondBody (secondInputs.map (input secondNames))
  (.uninterned (ordinaryLevel (valueOf depthCall))) depthCall.state
private def freshKey := muKey (valueOf depthCall) (valueOf ordinaryCall)

private theorem second_context : Context originalHeap (secondInputs.map (input secondNames)) := by
  apply SourceRecursiveIntersectionSemanticHeap.context originalHeap original_semantic
  intro value member
  change value ∈ [originalValue, .reference (.uninterned 20)] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact original_available
  · rcases List.mem_cons.mp member with rfl | impossible
    · exact InternedNestedProvenance.ordinary_available originalHeap 20
    · cases impossible

private theorem depth_done :
    callback secondBody (secondInputs.map (input secondNames)) .depth originalHeap =
      .done (valueOf depthCall) depthCall.state := by cbv

private theorem ordinary_done :
    callback secondBody (secondInputs.map (input secondNames))
      (.uninterned (ordinaryLevel (valueOf depthCall))) depthCall.state =
      .done (valueOf ordinaryCall) ordinaryCall.state := by cbv

/-- Actual probes beside a live open raw Mu derive both ordinary and reserved-name freshness. -/
theorem open_mu_probe_freshness :
    build original originalInputs empty = .done originalValue originalHeap ∧
    (∃ entry body depth ordinary, originalValue = .mu entry body depth ordinary ∧ originalValue.free = [.uninterned 7]) ∧
    callback secondBody (secondInputs.map (input secondNames)) .depth originalHeap =
      .done (valueOf depthCall) depthCall.state ∧
    callback secondBody (secondInputs.map (input secondNames))
      (.uninterned (ordinaryLevel (valueOf depthCall))) depthCall.state =
      .done (valueOf ordinaryCall) ordinaryCall.state ∧
    .inl (.uninterned 7) ∈ support (.binder true secondBody) secondInputs ∧
    .inl (.uninterned (ordinaryLevel (valueOf depthCall))) ∉ support (.binder true secondBody) secondInputs ∧
    ordinaryCall.state.nodes.table freshKey = none ∧
    .inl (.interned (Cache.intern ordinaryCall.state.nodes freshKey).1.identity) ∉
      support (.binder true secondBody) secondInputs := by
  have depthContext : Context depthCall.state (secondInputs.map (input secondNames)) := by
    simpa only [depth_done, Outcome.state] using second_context.callback secondBody .depth
      (InternedNestedProvenance.depth_available originalHeap)
  have ordinaryContext : Context ordinaryCall.state (secondInputs.map (input secondNames)) := by
    simpa only [ordinary_done, Outcome.state] using depthContext.callback secondBody
      (.uninterned (ordinaryLevel (valueOf depthCall)))
      (InternedNestedProvenance.ordinary_available depthCall.state (ordinaryLevel (valueOf depthCall)))
  have missing : ordinaryCall.state.nodes.table freshKey = none := by cbv
  have ordinaryFresh := ordinary_fresh_fixed secondBody secondInputs secondNames originalHeap depthCall.state
    second_context (valueOf depthCall) depth_done
  have reservedFresh := reserved_fresh_fixed (.binder true secondBody) secondInputs secondNames ordinaryCall.state
    ordinaryContext freshKey missing
  exact ⟨original_done, ⟨_, _, _, _, by cbv, by cbv⟩, depth_done, ordinary_done,
    by cbv; simp, ordinaryFresh, missing, reservedFresh⟩

#check @discarded_fixed_capture
#print axioms discarded_fixed_capture
#check @open_mu_probe_freshness
#print axioms open_mu_probe_freshness
end MicroCFTA.NativeNormalizationInputKernels
