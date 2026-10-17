import MicroCFTA.SourceCurrentConstrainedCapStoredSubstitution

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.StoredCapKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference)
open InternedStoredSubstitution (Environment Replacements)
open SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentConstrainedCapConstruction (Typed ManyTyped EdgesTyped)
open SourceCurrentConstrainedCapStoredSubstitution

private def original : Reference := .uninterned 42
private def environment : Environment Nat Bool := fun name => if name = original then some (.reference .depth) else none
private def plan : Syntax Nat Bool :=
  .node [.mk 3 false [.var 0, .binder false (.node [.mk 4 true [.var 0, .var 1]])]]

private def badRoot : Value Nat Bool → Bool
  | .node _ (edge :: _) _ _ => !edge.entry.key.constraint
  | _ => false

private theorem annotated_not_bad (value : Value Nat Bool) (annotated : Annotated (fun guard => guard = true) value) :
    badRoot value = false := by
  cases annotated with
  | empty | reference | union | mu => rfl
  | node entry edges level free guards children =>
      cases edges with
      | nil => rfl
      | cons edge rest => simp only [badRoot, guards edge List.mem_cons_self, Bool.not_true]

private def observation : Option (Bool × Bool × Bool) :=
  match InternedFreshOrdinaryConstruction.build plan [.reference original] empty with
  | .done value before =>
      match InternedFreshOrdinaryStoredSubstitution.execute value environment before with
      | .done result _ => some (badRoot value, value.free.isEmpty, value.referenceOf == result.referenceOf)
      | .pending .. => none
  | .pending .. => none

set_option cbv.maxSteps 100000000 in
private theorem observed : observation = some (true, false, false) := by cbv

/-- Initial open construction produces a nonhereditary cap with a nested Mu and its own changed substitution return. -/
theorem open_nested_mu_cap_transport :
    ∃ value before result after,
      InternedFreshOrdinaryConstruction.build plan [.reference original] empty = .done value before ∧
      value.free ≠ [] ∧ ¬Annotated (fun guard : Bool => guard = true) value ∧
      Cap (fun guard : Bool => guard = true) 1 value ∧
      InternedFreshOrdinaryStoredSubstitution.execute value environment before = .done result after ∧
      value.referenceOf ≠ result.referenceOf ∧ Cap (fun guard : Bool => guard = true) 1 result ∧
      MuStored (fun guard : Bool => guard = true) after ∧ Available after result ∧
      SourceEqualityRequiredCache.Ready after ∧ Grows before after ∧ Extends before.nodes.issued after.nodes.issued := by
  have computed := observed
  cases built : InternedFreshOrdinaryConstruction.build plan [.reference original] empty with
  | pending key after => simp [observation, built] at computed
  | done value before =>
      have inputAvailable : InternedNestedProvenance.Values (empty : State Nat Bool) [.reference original] := by
        intro item member
        cases List.mem_singleton.mp member
        exact InternedNestedProvenance.ordinary_available empty 42
      have context : InternedFreshOrdinaryContext.Context (empty : State Nat Bool) [.reference original] :=
        ⟨InternedFreshOrdinaryContext.empty_context.normal, inputAvailable,
          InternedFreshOrdinaryContext.empty_context.profiles, InternedFreshOrdinaryContext.empty_context.freeNames⟩
      have reference (name : Reference) : Cap (fun guard : Bool => guard = true) 0 (.reference name : Value Nat Bool) :=
        .plain 0 (.reference name)
      have typed : Typed (fun guard : Bool => guard = true) 1 plan [.reference original] := by
        simp [plan, Typed, EdgesTyped, ManyTyped, reference]
      have checked := SourceCurrentConstrainedCapConstruction.build (fun guard : Bool => guard = true) 1 plan _ empty
        empty_facts inputAvailable typed (MuStored.empty _)
      have bounded := checked.result value before built
      have stored : MuStored (fun guard : Bool => guard = true) before := by
        simpa only [built, Outcome.state] using checked.stored
      have physical := InternedFreshOrdinaryFacts.build_verified plan _ empty empty_facts inputAvailable
      have available := physical.result value before built
      have finalContext : InternedFreshOrdinaryContext.Context before [.reference original] := by
        simpa only [built, Outcome.state] using context.build plan
      have depth := InternedRecordDepthExecution.build_depth plan _ empty context InternedFreshOrdinaryDepthHeap.empty_heap
      have heap : InternedFreshOrdinaryDepthHeap.Heap before := by simpa only [built, Outcome.state] using depth.heap
      have covered : Covered [] before := InternedFreshOrdinaryCoverage.build_covered plan _ empty empty_facts.coherent.valid
        empty_correct.2 value before built
      have openDepth := InternedOpenDepthExecution.build_depth plan _ empty context InternedFreshOrdinaryDepthHeap.empty_heap
        (SourceEqualityRequiredCache.constructed (.empty : Syntax Nat Bool) .empty empty rfl).depth
      have retainedDepth : InternedOpenDepthReadback.Heap before := by
        simpa only [built, Outcome.state] using openDepth.heap
      have ready : SourceEqualityRequiredCache.Ready before :=
        ⟨⟨⟨finalContext.normal, by intro _ member; cases member, finalContext.profiles, finalContext.freeNames⟩, heap⟩,
          covered, retainedDepth⟩
      have replacements : Replacements before environment := by
        intro name replacement found
        simp only [environment] at found
        split at found
        · cases found
          exact InternedNestedProvenance.depth_available before
        · cases found
      have annotations : ∀ name replacement, environment name = some replacement → Annotated (fun guard : Bool => guard = true) replacement := by
        intro name replacement found
        simp only [environment] at found
        split at found
        · cases found
          exact .reference .depth
        · cases found
      obtain ⟨result, after, done, resultBound, resultStore, resultAvailable, resultReady, growth, history⟩ :=
        complete (fun guard : Bool => guard = true) 1 value environment before ready available bounded replacements annotations stored
      simp only [observation, built, done, Option.some.injEq, Prod.mk.injEq] at computed
      refine ⟨value, before, result, after, built, ?_, ?_, bounded, done, ?_, resultBound, resultStore, resultAvailable,
        resultReady, growth, history⟩
      · intro emptyFree
        simp only [emptyFree, List.isEmpty_nil, Bool.true_eq_false] at computed
      · intro annotated
        rw [annotated_not_bad value annotated] at computed
        cases computed.1
      · intro same
        have opposite : (value.referenceOf == result.referenceOf) = true := by simp [same]
        rw [computed.2.2] at opposite
        cases opposite

#print axioms open_nested_mu_cap_transport
#check @open_nested_mu_cap_transport
end MicroCFTA.StoredCapKernels
