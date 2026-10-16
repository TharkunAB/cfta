import MicroCFTA.SourceCurrentHereditaryExposure
import MicroCFTA.InternedFreshOrdinaryReplay
import MicroCFTA.InternedOrdinaryAbsenceReplay
import MicroCFTA.SourceRecursiveIntersectionMaybeMuCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.HereditaryConstructionIndependentChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open SourceEqualityAnnotationLanguage SourceEqualityAnnotationConstruction
open SourceCurrentHereditaryConstruction

/-- Actual closed construction retains its local invariant after an unrelated constrained cap. -/
theorem closed_then_constrained_cap [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (expression : Syntax Symbol Guard) (allowed : Allowed valid expression)
    (symbol : Symbol) (guard : Guard) (invalid : ¬valid guard) :
    ∃ value state, InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      let edge := run (makeEdge symbol guard []) state
      let cap := run (makeNode [edge.1]) edge.2
      SourceEqualityRequiredCache.Ready cap.2 ∧ Available cap.2 value ∧ MuStored valid cap.2 ∧
      ¬SourceEqualityAnnotationHeap.Heap valid cap.2 ∧
      ∃ result after, SourceEqualityRequiredHead.Head value cap.2 result after ∧
        MuStored valid after ∧ Annotated valid result := by
  obtain ⟨value, state, built, stored, annotated⟩ := SourceCurrentHereditaryConstruction.closed valid expression allowed
  have ready := SourceEqualityRequiredCache.constructed expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built
  let edge := run (makeEdge symbol guard []) state
  have first := SourceEqualityRequiredCache.edge symbol guard [] state ready (by intro _ member; cases member)
  have second := SourceEqualityRequiredCache.node [edge.1] edge.2 first.1.ready
    (fun candidate member => (List.mem_singleton.mp member) ▸ first.2.1)
    (by intro candidate member child childMember; obtain rfl := List.mem_singleton.mp member
        rw [first.2.2] at childMember; cases childMember)
  have nextStored := (stored.makeEdge symbol guard []).makeNode [edge.1]
  have nextAvailable := second.1.available value (first.1.available value available)
  have notHeap : ¬SourceEqualityAnnotationHeap.Heap valid (run (makeNode [edge.1]) edge.2).2 := by
    intro heap
    have resident := second.1.growth.edgeRecords edge.1.entry.key edge.1 first.2.1
    have validKey := heap edge.1.entry.key edge.1 resident
    have same := InternedOrdinaryAbsenceReplay.makeEdge_key symbol guard [] state ready.semantic.1.normal.facts.coherent
    apply invalid
    simpa only [edge, same] using validKey
  obtain ⟨result, after, head, _, _, _, _⟩ := SourceEqualityRequiredHead.complete value _ second.1.ready nextAvailable closed
  have localHead := SourceCurrentHereditaryExposure.head valid head second.1.ready nextAvailable closed annotated nextStored
  exact ⟨value, state, built, second.1.ready, nextAvailable, nextStored, notHeap, result, after, head, localHead⟩

/-- A completed recursive source program replays exactly and retains the causal store. -/
theorem exact_warm_build [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (expression : Syntax Symbol Guard) (allowed : Allowed valid expression) :
    ∃ value state, InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      InternedFreshOrdinaryConstruction.build expression [] state = .done value state ∧
      MuStored valid state ∧ Annotated valid value := by
  obtain ⟨value, state, built, stored, annotated⟩ := SourceCurrentHereditaryConstruction.closed valid expression allowed
  exact ⟨value, state, built, InternedFreshOrdinaryReplay.empty_replay expression value state state built (grows_refl _),
    stored, annotated⟩

/-- Actual optional binding constructs its own return before the local annotation is extracted. -/
theorem optional_binder_complete [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (key : Nat × Nat) (body : Value Symbol Guard) (state : State Symbol Guard)
    (ready : SourceEqualityRequiredCache.Ready state) (available : Available state body)
    (annotated : Annotated valid body) (stored : MuStored valid state) :
    ∃ value after, SourceRecursiveIntersectionMaybeMu.maybeMu key body state = .done value after ∧
      MuStored valid after ∧ Annotated valid value := by
  obtain ⟨value, after, done, _⟩ := SourceRecursiveIntersectionMaybeMu.complete_decoded key body state
    ready.semantic.1 available ready.semantic.2 ready.covered
  have checked := SourceCurrentHereditaryConstruction.optionalBinder valid key body state ready.semantic.1.normal.facts
    available annotated stored
  exact ⟨value, after, done, by simpa only [done, Outcome.state] using checked.stored, checked.result value after done⟩

/-- A concrete recursive family permits a later unrelated false-guard cap. -/
theorem recursive_boolean_cap (smart : Bool) :
    ∃ value state, InternedFreshOrdinaryConstruction.build
        (.binder smart (.union [.node [.mk 0 true [.var 0]], .node [.mk 1 true []]]) : Syntax Nat Bool)
        [] empty = .done value state ∧
      let edge := run (makeEdge 2 false []) state
      let cap := run (makeNode [edge.1]) edge.2
      SourceEqualityRequiredCache.Ready cap.2 ∧ Available cap.2 value ∧ MuStored (fun b => b = true) cap.2 ∧
      ¬SourceEqualityAnnotationHeap.Heap (fun b => b = true) cap.2 ∧
      ∃ result after, SourceEqualityRequiredHead.Head value cap.2 result after ∧
        MuStored (fun b => b = true) after ∧ Annotated (fun b => b = true) result := by
  apply closed_then_constrained_cap (fun b : Bool => b = true) _ _ 2 false (by decide)
  simp [Allowed, ManyAllowed, EdgesAllowed]

end MicroCFTA.HereditaryConstructionIndependentChecks

#print axioms MicroCFTA.HereditaryConstructionIndependentChecks.closed_then_constrained_cap
#check @MicroCFTA.HereditaryConstructionIndependentChecks.closed_then_constrained_cap
#print axioms MicroCFTA.HereditaryConstructionIndependentChecks.exact_warm_build
#check @MicroCFTA.HereditaryConstructionIndependentChecks.exact_warm_build
#print axioms MicroCFTA.HereditaryConstructionIndependentChecks.optional_binder_complete
#check @MicroCFTA.HereditaryConstructionIndependentChecks.optional_binder_complete
#print axioms MicroCFTA.HereditaryConstructionIndependentChecks.recursive_boolean_cap
#check @MicroCFTA.HereditaryConstructionIndependentChecks.recursive_boolean_cap
