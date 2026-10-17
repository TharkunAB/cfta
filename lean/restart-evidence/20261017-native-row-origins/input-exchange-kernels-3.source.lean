import MicroCFTA.SourceCurrentNativeInputExchange
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap
import MicroCFTA.InternedFreshOrdinaryReplay

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

namespace MicroCFTA.NativeInputExchangeKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference NodeKey)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext SourceCurrentNativeInputExchange

private def firstName : Reference := .intersection 2 3
private def secondName : Reference := .intersection 4 5
private def capture : Reference := .uninterned 7
private def environment (name : Reference) : List (Value Nat Unit) := [.reference name, .reference capture]

private def program (smart : Bool) : Syntax Nat Unit :=
  .union [
    .node [.mk 0 () [.empty, .var 0]],
    .binder true (.node [
      .mk 1 () [.empty, .var 1],
      .mk 2 () [.var 0, .binder smart (.node [.mk 3 () [.var 0, .var 3]])]])]

private def built (smart : Bool) := build (program smart) (environment firstName) empty
private def valueOf (outcome : Outcome Nat Unit (Value Nat Unit)) : Value Nat Unit :=
  match outcome with
  | .done value _ => value
  | .pending _ _ => .empty
private def value (smart : Bool) := valueOf (built smart)
private def heap (smart : Bool) := (built smart).state

private theorem inputs (state : State Nat Unit) (name : Reference)
    (available : Available state (.reference name)) : InternedNestedProvenance.Values state (environment name) := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | member
  · exact available
  · rcases List.mem_cons.mp member with rfl | impossible
    · exact InternedNestedProvenance.ordinary_available state 7
    · cases impossible

private theorem first_available (state : State Nat Unit) : Available state (.reference firstName) :=
  reference_available state firstName (by intro identity impossible; simp [Value.free, firstName] at impossible)

private theorem second_available (state : State Nat Unit) : Available state (.reference secondName) :=
  reference_available state secondName (by intro identity impossible; simp [Value.free, secondName] at impossible)

private theorem built_done (smart : Bool) : built smart = .done (value smart) (heap smart) := by
  cases smart <;> cbv

private theorem initial_context : Context (empty : State Nat Unit) (environment firstName) :=
  SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap
    _ (inputs empty firstName (first_available empty))

private theorem initial (smart : Bool) :
    SourceRecursiveIntersectionSemanticHeap.SemanticHeap (heap smart) ∧ Covered [] (heap smart) := by
  have actual := built_done smart
  change build (program smart) (environment firstName) empty = .done (value smart) (heap smart) at actual
  refine ⟨?_, ?_⟩
  · simpa only [actual, Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source
      (program smart) (environment firstName) empty SourceRecursiveIntersectionSemanticHeap.empty_heap
      (inputs empty firstName (first_available empty))
  · exact InternedFreshOrdinaryCoverage.build_covered (program smart) (environment firstName) empty
      empty_valid empty_correct.2 _ _ actual

private theorem absent (smart : Bool) (name : Reference) (different : name ≠ capture) : name ∉ (value smart).free := by
  have exactFree : (value smart).free = [capture] := by cases smart <;> cbv
  simpa only [exactFree, List.mem_singleton] using different

/-- A changed original input is visited in discarded edges beside two nested recursive constructors. -/
theorem nested_original_input_exchange :
    ∃ result before after,
      build (program false) (environment firstName) empty = .done result before ∧
      build (program false) (environment secondName) before = .done result after ∧
      Grows before after ∧ Context after (environment secondName) ∧
      before.edges.next < after.edges.next ∧
      (∃ entry body depth ordinary,
        result = .mu entry body depth ordinary ∧ result.free = [capture]) := by
  have source := initial false
  have laterContext := SourceRecursiveIntersectionSemanticHeap.context (heap false) source.1
    (environment secondName) (inputs _ _ (second_available _))
  obtain ⟨after, changed, growth, finalContext⟩ := local_complete (program false) [.reference capture]
    firstName secondName empty (heap false) (heap false) initial_context laterContext source.1.2 source.2
    (value false) (built_done false) (absent false firstName (by intro same; cases same)) (grows_refl _)
  refine ⟨value false, heap false, after, built_done false, changed, growth, finalContext, ?_, ?_⟩
  · have sameState : after = (build (program false) (environment secondName) (heap false)).state :=
      (congrArg Outcome.state changed).symm
    rw [sameState]
    cbv
  · exact ⟨_, _, _, _, by cbv, by cbv⟩

/-- The changed-input producer returns the old populated Mu winner and the original plan then replays at that exact heap. -/
theorem warm_original_input_replay :
    ∃ result before after,
      build (program true) (environment firstName) empty = .done result before ∧
      build (program true) (environment secondName) before = .done result after ∧
      build (program true) (environment firstName) after = .done result after ∧
      (∃ entry body depth ordinary,
        result = .mu entry body depth ordinary ∧ result.free = [capture] ∧
        before.nodeRecords (muKey depth ordinary) = some result ∧
        after.nodeRecords (muKey depth ordinary) = some result ∧
        InternedNestedConstruction.request true depth ordinary
          (fun _ state => .pending (muKey depth ordinary) state) after = .done result after) := by
  have source := initial true
  have laterContext := SourceRecursiveIntersectionSemanticHeap.context (heap true) source.1
    (environment secondName) (inputs _ _ (second_available _))
  obtain ⟨after, changed, growth, finalContext⟩ := local_complete (program true) [.reference capture]
    firstName secondName empty (heap true) (heap true) initial_context laterContext source.1.2 source.2
    (value true) (built_done true) (absent true firstName (by intro same; cases same)) (grows_refl _)
  have replay := InternedFreshOrdinaryReplay.build_replay (program true) (environment firstName)
    empty after (value true) (heap true) empty_valid (built_done true) growth
  refine ⟨value true, heap true, after, built_done true, changed, replay, ?_⟩
  let parts : Interned NodeKey × Value Nat Unit × Value Nat Unit × Value Nat Unit :=
    match value true with
    | .mu entry body depth ordinary => (entry, body, depth, ordinary)
    | _ => (⟨0, .empty⟩, .empty, .empty, .empty)
  have shape : value true = .mu parts.1 parts.2.1 parts.2.2.1 parts.2.2.2 := by dsimp only [parts]; cbv
  have stored : (heap true).nodeRecords (muKey parts.2.2.1 parts.2.2.2) = some (value true) := by dsimp only [parts]; cbv
  have laterStored := growth.nodeRecords _ _ stored
  refine ⟨parts.1, parts.2.1, parts.2.2.1, parts.2.2.2, shape, ?_, stored, laterStored, ?_⟩
  · cbv
  · obtain ⟨winner, table, _⟩ := finalContext.normal.facts.coherent.nodes _ _ laterStored
    have finish : InternedNestedConstruction.finish true (value true) = value true := by cbv
    simp only [InternedNestedConstruction.request, table, laterStored, finish]

#check @nested_original_input_exchange
#print axioms nested_original_input_exchange
#check @warm_original_input_replay
#print axioms warm_original_input_replay
end MicroCFTA.NativeInputExchangeKernels
