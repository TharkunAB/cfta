import MicroCFTA.SourceCurrentHereditaryConstruction
import MicroCFTA.SourceRecursiveIntersectionCompile
import MicroCFTA.SourceCurrentConstrainedCap

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.GeneralNativeCapPairProbe
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionControl
local notation "Heap" => InternedConstructorTemplates.State Nat Bool
local notation "V" => Value Nat Bool

private def loopKey : InternedBinderProtocol.NodeKey := muKey (.reference .depth : V) (.reference (.uninterned 0))
private def loop : V := .mu ⟨0, loopKey⟩ (.reference (.interned 0)) (.reference .depth) (.reference (.uninterned 0))
private def loopHeap : Heap :=
  { empty with
    nodes := (Cache.intern Cache.emptyState loopKey).2
    nodeRecords := Cache.put (fun _ => none) loopKey loop }
private def rawEdge := run (makeEdge 7 false []) loopHeap
private def rawNode := run (makeNode [rawEdge.1]) rawEdge.2

/-- The uncleaned source constructor builds the recursive record used by the branch test. -/
theorem constructed_loop :
    InternedFreshOrdinaryConstruction.build (.binder false (.var 0)) [] (empty : Heap) = .done loop loopHeap := by
  simp [InternedFreshOrdinaryConstruction.build, InternedFreshOrdinaryConstruction.ordinaryLevel,
    InternedFreshOrdinaryConstruction.freeBound, InternedNestedConstruction.Outcome.bind,
    InternedNestedConstruction.work, InternedNestedConstruction.request, InternedNestedConstruction.finish,
    withoutSelfReference, run, loopKey, loop, loopHeap, empty, muKey, Value.referenceOf, Value.depth, Value.free,
    Cache.intern, Cache.emptyState, Cache.reserve, Cache.install, Cache.keepFirst, Cache.put]
  rfl

/-- The source ordinary operand is built in that same actual returned constructor heap. -/
theorem constructed_ordinary :
    InternedFreshOrdinaryConstruction.build (.node [.mk 7 false []]) [] loopHeap = .done rawNode.1 rawNode.2 := by
  simp [InternedFreshOrdinaryConstruction.build, InternedFreshOrdinaryConstruction.buildEdges,
    InternedFreshOrdinaryConstruction.buildMany, InternedNestedConstruction.Outcome.bind,
    InternedNestedConstruction.work, rawNode, rawEdge]

private theorem rawNode_value : rawNode.1 =
    .node ⟨1, .node [0]⟩ [.mk ⟨0, ⟨7, [], false⟩⟩ []] 0 [] := by
  simp [rawNode, rawEdge, run, makeNode, makeEdge, canonicalEdges, surviving,
    EnumerationBuilderCaches.canonicalIds, List.eraseDups_cons, nodeStep, edgeStep, identifyNode,
    maximumDepth, childFree, canonicalFree, EdgeValue.children, EdgeValue.entry, loopHeap, loopKey, loop, empty, muKey, Value.referenceOf,
    Cache.intern, Cache.emptyState, Cache.reserve, Cache.install, Cache.keepFirst, Cache.put]

/-- The numeric repeated-pair cutoff can recur while a nonhereditary ordinary operand stays fixed. -/
theorem mixed_pair_repeats :
    SourceEqualityAnnotationLanguage.Annotated (fun guard : Bool => guard = true) loop ∧
      SourceCurrentConstrainedCap.Cap (fun guard : Bool => guard = true) 1 rawNode.1 ∧
      ¬ SourceEqualityAnnotationLanguage.Annotated (fun guard : Bool => guard = true) rawNode.1 ∧
      rawNode.1.free = [] ∧ loop.free = [] ∧
      SourceRecursiveIntersectionControl.decision IntersectionEmptyDomain.emptyKey rawNode.1 loop = .rightMu ∧
      SourceRecursiveIntersectionControl.decision
        (SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey [0] (pair 1 0))
        rawNode.1 (.reference (.interned 0)) = .repeated (pair 1 0) := by
  rw [rawNode_value]
  refine ⟨.mu _ _ _ _ (.reference _), ?_, ?_, ?_, rfl, ?_, ?_⟩
  · apply SourceCurrentConstrainedCap.Cap.node 0
    intro child impossible
    cases impossible
  · intro annotated
    cases annotated with
    | node entry edges depth free guards children =>
        have impossible := guards (.mk ⟨0, ⟨7, [], false⟩⟩ []) (by simp)
        change false = true at impossible
        cases impossible
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms constructed_loop
#check @constructed_loop
#print axioms constructed_ordinary
#check @constructed_ordinary
#print axioms mixed_pair_repeats
#check @mixed_pair_repeats
end MicroCFTA.GeneralNativeCapPairProbe
