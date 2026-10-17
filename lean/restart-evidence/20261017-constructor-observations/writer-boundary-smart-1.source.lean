import MicroCFTA.SourceCurrentOpenObservationSurvival
import MicroCFTA.SourceCurrentOpenObservationLists
import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.WriterSmartBoundary
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (Reference)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentOpenObservations
open SourceCurrentOpenObservationConstructors
open SourceCurrentOpenObservationLists
open SourceCurrentOpenObservationSurvival (Related)

private def firstBody : Syntax Nat Bool := .union [.binder false .empty,.var 0]
private def secondBody : Syntax Nat Bool := .var 0
private def firstExpression : Syntax Nat Bool := .binder true firstBody
private def secondExpression : Syntax Nat Bool := .binder true secondBody
private def firstRun := build firstExpression [] empty
private def firstValue : Value Nat Bool := match firstRun with | .done value _ => value | .pending .. => .empty
private def middle := firstRun.state
private def secondRun := build secondExpression [] middle
private def secondValue : Value Nat Bool := match secondRun with | .done value _ => value | .pending .. => .empty
private def after := secondRun.state
private def raw (name : Reference) := run (makeUnion [firstValue,.reference name]) middle
private def entry : Interned InternedBinderProtocol.NodeKey := ⟨0,muKey (.empty : Value Nat Bool) .empty⟩
private theorem first_done : firstRun = .done firstValue middle := by cbv
private theorem second_done : secondRun = .done secondValue after := by cbv
private theorem first_literal : firstValue = .mu entry .empty .empty .empty := by cbv
private theorem second_literal : secondValue = .empty := by cbv
private theorem middle_ready : Ready middle :=
  SourceEqualityRequiredCache.constructed firstExpression firstValue middle first_done
private theorem first_available : Available middle firstValue :=
  (InternedFreshOrdinaryFacts.build_verified firstExpression [] empty
    (SourceEqualityRequiredCache.constructed .empty .empty empty (by rw [build])).semantic.1.normal.facts
    (by intro value impossible; cases impossible)).result firstValue middle first_done
private theorem same_empty (depth : Nat) (view : State Nat Bool) : Same depth view [firstValue] [Value.empty] := by
  rw [first_literal]
  exact SourceCurrentOpenObservations.unfold depth view entry .empty .empty .empty .empty view (by cbv)

private theorem raw_done (name : Reference) :
    build firstBody [.reference name] middle = .done (raw name).1 (raw name).2 := by rfl
private theorem second_body_done (name : Reference) :
    build secondBody [.reference name] middle = .done (.reference name) middle := by rfl
private theorem raw_related (name : Reference) (available : Available middle (.reference name)) :
    Related (raw name).1 (.reference name) := by
  have inputs : Values middle [firstValue,.reference name] := by
    intro value member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact first_available
    · exact available
  have otherInputs : Values middle [.empty,.reference name] := by
    intro value member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact empty_available
    · exact available
  constructor
  · have nonempty : (raw name).1.referenceOf ≠ .empty := by
      intro impossible
      have all := (InternedEmptyNormalization.makeUnion_empty_iff [firstValue,.reference name] middle
        middle_ready.semantic.1.normal.facts.coherent middle_ready.semantic.1.normal.facts.linked
        middle_ready.semantic.1.normal.live middle_ready.semantic.1.normal.proper inputs).mp impossible
      have contradict := all (.reference name) (by simp)
      cases contradict
    simp only [Value.referenceOf, nonempty, reduceCtorEq]
  · intro depth view
    have normalized := makeUnion_normalize depth middle view middle_ready.semantic.1.normal.facts
      middle_ready.semantic.1.normal.live [firstValue,.reference name] inputs
    have roots := SourceCurrentOpenObservationLists.append depth view _ _ _ _
      (same_empty depth view) (Same.refl depth view [.reference name])
    have other := makeUnion_normalize depth middle view middle_ready.semantic.1.normal.facts
      middle_ready.semantic.1.normal.live [.empty,.reference name] otherInputs
    have exactOther : run (makeUnion [.empty,.reference name]) middle = (.reference name,middle) := by rfl
    exact normalized.trans (roots.trans (by simpa only [exactOther] using other.symm))

private theorem second_keeps : Keeps middle after ∧ Available after secondValue := by
  let context : InternedFreshOrdinaryContext.Context middle [] :=
    ⟨middle_ready.semantic.1.normal, (by intro value impossible; cases impossible),
      middle_ready.semantic.1.profiles, middle_ready.semantic.1.freeNames⟩
  have checked := InternedFreshOrdinaryFacts.build_verified secondExpression [] middle
    context.normal.facts context.available
  have semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap after := by
    simpa only [second_done,Outcome.state] using
      SourceRecursiveIntersectionSemanticHeap.source secondExpression [] middle middle_ready.semantic context.available
  have openDepth : InternedOpenDepthReadback.Heap after := by
    simpa only [second_done,Outcome.state] using
      (InternedOpenDepthExecution.build_depth secondExpression [] middle context middle_ready.semantic.2 middle_ready.depth).heap
  refine ⟨⟨⟨semantic,?_,openDepth⟩,?_,?_⟩,checked.result _ _ second_done⟩
  · exact InternedFreshOrdinaryCoverage.build_covered secondExpression [] middle
      context.normal.facts.coherent.valid middle_ready.covered _ _ second_done
  · simpa only [second_done,Outcome.state] using checked.growth
  · simpa only [second_done,Outcome.state] using checked.history

/-- Related raw bodies need not give related results after actual smart binder construction. -/
theorem actual_smart_boundary :
    build firstExpression [] empty = .done firstValue middle ∧ Ready middle ∧
    build secondExpression [] middle = .done secondValue after ∧ Keeps middle after ∧
    Available after firstValue ∧ Available after secondValue ∧
    (∀ name, Available middle (.reference name) →
      build firstBody [.reference name] middle = .done (raw name).1 (raw name).2 ∧
      build secondBody [.reference name] middle = .done (.reference name) middle ∧
      Related (raw name).1 (.reference name)) ∧
    firstValue = .mu entry .empty .empty .empty ∧ secondValue = .empty ∧
    (∀ depth view, Same depth view [firstValue] [secondValue]) ∧
    ¬ Related firstValue secondValue := by
  refine ⟨first_done,middle_ready,second_done,second_keeps.1,
    second_keeps.1.available _ first_available,second_keeps.2,?_,first_literal,second_literal,?_,?_⟩
  · intro name available
    exact ⟨raw_done name,second_body_done name,raw_related name available⟩
  · intro depth view
    simpa only [second_literal] using same_empty depth view
  · intro related
    have impossible := related.1.mpr (by rw [second_literal]; rfl)
    rw [first_literal] at impossible
    cases impossible

#check @actual_smart_boundary
#print axioms actual_smart_boundary
end MicroCFTA.WriterSmartBoundary
