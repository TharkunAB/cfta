import MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution
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

namespace MicroCFTA.NormalizedComparisonKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome finish request)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentNativeNormalizedComparisonExecution SourceCurrentNativeCallbackErasure

private def constantEdge := run (makeEdge 7 () []) (empty : State Nat Unit)
private def constantNode := run (makeNode [constantEdge.1]) constantEdge.2
private def constant : Value Nat Unit := constantNode.1
private def nested : Syntax Nat Unit :=
  .binder true (.union [
    .var 0,
    .binder true (.union [.var 1, .node [.mk 7 () []]])])
private def nestedBuilt := build nested [] empty
private def nestedHeap := nestedBuilt.state
private def selected : Value Nat Unit := (nestedHeap.nodeRecords (muKey constant constant)).getD .empty
private def parts : Interned NodeKey × Value Nat Unit × Value Nat Unit × Value Nat Unit :=
  match selected with
  | .mu entry body depth ordinary => (entry, body, depth, ordinary)
  | _ => (⟨0, .empty⟩, .empty, .empty, .empty)

/-- Nested callbacks produce the stored law before an exact old-winner request and full replay. -/
theorem nested_normalization_and_warm_winner :
    ∃ entry body depth ordinary after,
      build nested [] empty = .done constant after ∧
      after.nodes.next > 1 ∧
      after.nodeRecords (muKey constant constant) = some (.mu entry body depth ordinary) ∧
      ordinary = constant ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false ∧
      finish true (.mu entry body depth ordinary) = eraseSelf (.uninterned (ordinaryLevel depth)) ordinary ∧
      request true depth ordinary (fun _ state => .pending (muKey depth ordinary) state) after = .done constant after ∧
      build nested [] after = .done constant after := by
  have actual : build nested [] empty = .done constant nestedHeap := by cbv
  have stored : nestedHeap.nodeRecords (muKey constant constant) =
      some (.mu parts.1 parts.2.1 parts.2.2.1 parts.2.2.2) := by dsimp only [parts]; cbv
  have unused : InternedFreshOrdinaryDepthHeap.usesLocal parts.2.2.1 parts.2.2.2 = false := by cbv
  have law := closed_unused nested (muKey constant constant) parts.1 parts.2.1 parts.2.2.1 parts.2.2.2 stored unused
  have current := SourceCurrentConstrainedCapSourceHistory.empty_context.build nested
  have atHeap : SourceCurrentConstrainedCapSourceHistory.Context nestedHeap [] := current
  have sameKey : muKey parts.2.2.1 parts.2.2.2 = muKey constant constant := by cbv
  have readback : nestedHeap.nodeRecords (muKey parts.2.2.1 parts.2.2.2) =
      some (.mu parts.1 parts.2.1 parts.2.2.1 parts.2.2.2) := by rw [sameKey]; exact stored
  obtain ⟨owner, cached, _⟩ := atHeap.base.normal.facts.coherent.nodes _ _ readback
  have returned : finish true (.mu parts.1 parts.2.1 parts.2.2.1 parts.2.2.2) = constant := by
    rw [law]
    cbv
  refine ⟨parts.1, parts.2.1, parts.2.2.1, parts.2.2.2, nestedHeap, actual, ?_, stored, ?_, unused, law, ?_, ?_⟩
  · cbv
  · cbv
  · simp only [request, cached, readback, returned]
  · exact InternedFreshOrdinaryReplay.build_replay nested [] empty nestedHeap constant nestedHeap
      empty_valid actual (grows_refl _)

private def self : Syntax Nat Unit := .binder true (.var 0)
private def selfBuilt := build self [] empty
private def selfHeap := selfBuilt.state
private def selfDepth : Value Nat Unit := .reference .depth
private def selfOrdinary : Value Nat Unit := .reference (.uninterned 0)
private def selfEntry : Interned NodeKey := ⟨0, muKey selfDepth selfOrdinary⟩
private def selfBody : Value Nat Unit := .reference (.interned selfEntry.identity)

/-- Bare self is present in the actual raw callback and erases to empty on both cold and warm completion. -/
theorem bare_self_normalization_and_warm_winner :
    build self [] empty = .done .empty selfHeap ∧
    selfHeap.nodeRecords (muKey selfDepth selfOrdinary) = some (.mu selfEntry selfBody selfDepth selfOrdinary) ∧
    (.uninterned (ordinaryLevel selfDepth)) ∈ selfOrdinary.free ∧
    InternedFreshOrdinaryDepthHeap.usesLocal selfDepth selfOrdinary = false ∧
    finish true (.mu selfEntry selfBody selfDepth selfOrdinary) =
      eraseSelf (.uninterned (ordinaryLevel selfDepth)) selfOrdinary ∧
    request true selfDepth selfOrdinary (fun _ state => .pending (muKey selfDepth selfOrdinary) state) selfHeap =
      .done .empty selfHeap ∧
    build self [] selfHeap = .done .empty selfHeap := by
  have actual : build self [] empty = .done .empty selfHeap := by cbv
  have stored : selfHeap.nodeRecords (muKey selfDepth selfOrdinary) =
      some (.mu selfEntry selfBody selfDepth selfOrdinary) := by cbv
  have unused : InternedFreshOrdinaryDepthHeap.usesLocal selfDepth selfOrdinary = false := by cbv
  have law := closed_unused self (muKey selfDepth selfOrdinary) selfEntry selfBody selfDepth selfOrdinary stored unused
  have context := SourceCurrentConstrainedCapSourceHistory.empty_context.build self
  have atHeap : SourceCurrentConstrainedCapSourceHistory.Context selfHeap [] := context
  obtain ⟨owner, cached, _⟩ := atHeap.base.normal.facts.coherent.nodes _ _ stored
  refine ⟨actual, stored, ?_, unused, law, ?_, ?_⟩
  · simp only [selfDepth, selfOrdinary, ordinaryLevel, freeBound, Value.depth, Value.free,
      Nat.max_self, List.mem_singleton]
  · have returned : finish true (.mu selfEntry selfBody selfDepth selfOrdinary) = (.empty : Value Nat Unit) := by
      rw [law]
      cbv
    simp only [request, cached, stored, returned]
  · exact InternedFreshOrdinaryReplay.build_replay self [] empty selfHeap .empty selfHeap empty_valid actual (grows_refl _)

#check @nested_normalization_and_warm_winner
#print axioms nested_normalization_and_warm_winner
#check @bare_self_normalization_and_warm_winner
#print axioms bare_self_normalization_and_warm_winner
end MicroCFTA.NormalizedComparisonKernels
