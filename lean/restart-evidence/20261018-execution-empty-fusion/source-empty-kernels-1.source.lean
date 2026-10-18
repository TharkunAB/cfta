import MicroCFTA.SourceCurrentSourceEmptyAbstraction
import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

namespace MicroCFTA.SourceEmptyKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open SourceEqualityRequiredCache (Ready Keeps)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private theorem source_effect (expression : Syntax Nat Bool) (inputs : List (Value Nat Bool))
    (before : State Nat Bool) (ready : Ready before) (available : InternedNestedProvenance.Values before inputs) :
    build expression inputs before = .done (value (build expression inputs before)) (build expression inputs before).state ∧
      Keeps before (build expression inputs before).state ∧
      Available (build expression inputs before).state (value (build expression inputs before)) := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic inputs available
  obtain ⟨result,after,called⟩ := InternedRecordDepthCompletion.source_complete expression inputs before
    context ready.semantic.2 ready.covered
  have checked := InternedFreshOrdinaryFacts.build_verified expression inputs before ready.semantic.1.normal.facts available
  have kept : Keeps before after := by
    refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
    · simpa only [called,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source expression inputs before ready.semantic available
    · exact InternedFreshOrdinaryCoverage.build_covered expression inputs before ready.semantic.1.normal.facts.coherent.valid ready.covered result after called
    · simpa only [called,Outcome.state] using (InternedOpenDepthExecution.build_depth expression inputs before context ready.semantic.2 ready.depth).heap
    · simpa only [called,Outcome.state] using checked.growth
    · simpa only [called,Outcome.state] using checked.history
  rw [called]
  exact ⟨rfl,kept,checked.result result after called⟩

private def leaf : Syntax Nat Bool := .node [.mk 9 true []]
private def built := build leaf [] empty
private def capture := value built
private def before := built.state
private def expression : Syntax Nat Bool := .binder true (.node [.mk 5 false [.var 0,.var 1]])
private def firstRun := build expression [.reference .depth] before
private def first := value firstRun
private def middle := firstRun.state
private def secondRun := build expression [capture] middle
private def second := value secondRun
private def after := secondRun.state

private theorem base_call : build leaf [] empty = .done capture before := by cbv
private theorem base_ready : Ready before := SourceEqualityRequiredCache.constructed leaf capture before base_call
private theorem capture_available : Available before capture :=
  (InternedFreshOrdinaryFacts.build_verified leaf [] empty InternedNestedFacts.empty_facts
    (by intro child member; cases member)).result capture before base_call
private theorem first_inputs : InternedNestedProvenance.Values before [.reference .depth] := by
  intro child member
  obtain rfl := List.mem_singleton.mp member
  exact InternedNestedProvenance.depth_available before
private theorem first_effect : build expression [.reference .depth] before = .done first middle ∧
    Keeps before middle ∧ Available middle first := source_effect expression _ before base_ready first_inputs
private theorem second_inputs : InternedNestedProvenance.Values middle [capture] := by
  intro child member
  obtain rfl := List.mem_singleton.mp member
  exact first_effect.2.1.available _ capture_available
private theorem second_effect : build expression [capture] middle = .done second after ∧
    Keeps middle after ∧ Available after second := source_effect expression _ middle first_effect.2.1.ready second_inputs
private def used : Value Nat Bool → Prop
  | .mu entry body _ _ => .interned entry.identity ∈ body.free
  | _ => False

private theorem checked_witness :
    build leaf [] empty = .done capture before ∧ Ready before ∧
    build expression [.reference .depth] before = .done first middle ∧
    build expression [capture] middle = .done second after ∧
    Keeps before middle ∧ Keeps middle after ∧
    first ≠ second ∧ used first ∧ used second ∧
    (first.referenceOf == .empty) = (second.referenceOf == .empty) ∧
    first.referenceOf ≠ .empty ∧ second.referenceOf ≠ .empty ∧
    value (build expression [.empty] after) = .empty := by
  have agreement := SourceCurrentSourceEmptyAbstraction.source expression [.reference .depth] [capture]
    before middle middle after
    (SourceRecursiveIntersectionSemanticHeap.context before base_ready.semantic _ first_inputs)
    (SourceRecursiveIntersectionSemanticHeap.context middle first_effect.2.1.ready.semantic _ second_inputs)
    first second first_effect.1 second_effect.1 (by cbv)
  refine ⟨base_call,base_ready,first_effect.1,second_effect.1,first_effect.2.1,second_effect.2.1,
    ?_,?_,?_,agreement,?_,?_,?_⟩
  · intro equal
    have same := congrArg Value.referenceOf equal
    cbv at same
    cases same
  · cbv; exact List.mem_cons_self
  · cbv; exact List.mem_cons_self
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible
  · cbv

/-- Distinct used binders preserve lexical Empty agreement and an Empty capture removes their source row. -/
theorem witness :
    build leaf [] empty = .done capture before ∧ Ready before ∧
    build expression [.reference .depth] before = .done first middle ∧
    build expression [capture] middle = .done second after ∧
    Keeps before middle ∧ Keeps middle after ∧
    first ≠ second ∧ used first ∧ used second ∧
    (first.referenceOf == .empty) = (second.referenceOf == .empty) ∧
    first.referenceOf ≠ .empty ∧ second.referenceOf ≠ .empty ∧
    value (build expression [.empty] after) = .empty := checked_witness

end MicroCFTA.SourceEmptyKernels
