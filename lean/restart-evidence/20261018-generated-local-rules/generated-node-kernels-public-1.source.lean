import MicroCFTA.SourceCurrentGeneratedNodeCases
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.GeneratedNodeKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentOpenPreorderSimulation (Mutual)

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

private def nested : Syntax Nat Bool := .binder true (.node [.mk 7 true [],.mk 9 false [.var 0]])
private def built := build nested [] empty
private def capture := value built
private def base := built.state
private theorem base_done : build nested [] empty = .done capture base := by cbv
private theorem base_ready : Ready base := SourceEqualityRequiredCache.constructed nested capture base base_done
private theorem capture_available : Available base capture :=
  (InternedFreshOrdinaryFacts.build_verified nested [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result capture base base_done
private def q : Reference := .uninterned 10
private def r : Reference := .uninterned 11
private def child : Syntax Nat Bool := .union [.var 0,.var 1]
private def children : List (Syntax Nat Bool) := [child,.var 1]
private def deadChild : Syntax Nat Bool := .union [.var 0,.var 2]
private def rows : List (EdgeSyntax Nat Bool) :=
  [.mk 8 false children,.mk 99 true [.empty,deadChild]]
private def pack : Syntax Nat Bool := .node [.mk 0 true
  [.union [.var 0,.var 2],.union [.var 1,.var 2],
    .node [.mk 8 false [.union [.var 0,.var 2],.var 2],.mk 99 true [.empty,.union [.var 0,.var 3]]],
    .node [.mk 8 false [.union [.var 1,.var 2],.var 2],.mk 99 true [.empty,.union [.var 1,.var 3]]]]]
private def packInputs : List (Value Nat Bool) := [.reference q,.reference r,capture,.reference q]
private theorem pack_available : InternedNestedProvenance.Values base packInputs := by
  intro value member
  simp only [packInputs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact reference_available base q (InternedFreshProbeKeys.sentinel_references_issued base.nodes 10).2
  · exact reference_available base r (InternedFreshProbeKeys.sentinel_references_issued base.nodes 11).2
  · exact capture_available
  · exact reference_available base q (InternedFreshProbeKeys.sentinel_references_issued base.nodes 10).2
private def packed := build pack packInputs base
private def packedValue := value packed
private def reader := packed.state
private theorem packed_effect : build pack packInputs base = .done packedValue reader ∧
    Keeps base reader ∧ Available reader packedValue := source_effect pack packInputs base base_ready pack_available
private def rawFirst : Value Nat Bool := (InternedProbeProvenance.children packedValue)[0]?.getD .empty
private def rawSecond : Value Nat Bool := (InternedProbeProvenance.children packedValue)[1]?.getD .empty
private def firstNode : Value Nat Bool := (InternedProbeProvenance.children packedValue)[2]?.getD .empty
private def secondNode : Value Nat Bool := (InternedProbeProvenance.children packedValue)[3]?.getD .empty
private def symbolic : List (Sum (Value Nat Bool) Unit) := [.inr (),.inl capture,.inl (.reference q)]
private def firstNames : Unit → Reference := fun _ => q
private def secondNames : Unit → Reference := fun _ => r
private def firstInputs := symbolic.map (input firstNames)
private def secondInputs := symbolic.map (input secondNames)
private def environment : Environment Nat Bool := fun name => if name = q ∨ name = r then some capture else none
private theorem inputs_available (name : Reference) (available : Available reader (.reference name)) :
    InternedNestedProvenance.Values reader [.reference name,capture,.reference q] := by
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact available
  · exact packed_effect.2.1.available _ capture_available
  · exact reference_available reader q (InternedFreshProbeKeys.sentinel_references_issued reader.nodes 10).2
private theorem first_available : InternedNestedProvenance.Values reader firstInputs :=
  inputs_available q (reference_available reader q (InternedFreshProbeKeys.sentinel_references_issued reader.nodes 10).2)
private theorem second_available : InternedNestedProvenance.Values reader secondInputs :=
  inputs_available r (reference_available reader r (InternedFreshProbeKeys.sentinel_references_issued reader.nodes 11).2)
private theorem replacements : Replacements reader environment := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found; exact packed_effect.2.1.available _ capture_available
  · cases found
private theorem scope_shape : Scope (.node rows) symbolic = [.inl .depth,.inr ()] := by cbv
private theorem aliases : Aliases (.node rows) symbolic firstNames secondNames := by
  intro a aMember b bMember
  rw [scope_shape] at aMember bMember
  simp only [List.mem_cons,List.not_mem_nil,or_false] at aMember bMember
  rcases aMember with rfl | rfl <;> rcases bMember with rfl | rfl <;>
    simp [firstNames,secondNames,q,r]
private theorem paired : Inputs reader environment environment firstInputs secondInputs := by
  change Inputs reader environment environment [.reference q,capture,.reference q] [.reference r,capture,.reference q]
  refine .reference ?_ ?_ (.fixed capture (fun _ _ => rfl) (.fixed (.reference q) (fun _ _ => rfl) (.nil _ _)))
  · change Generated reader capture capture
    exact .refl capture
  · change Generated reader capture capture
    exact .refl capture
private theorem first_children : buildMany children firstInputs reader = .done [rawFirst,capture] reader := by cbv
private theorem second_children : buildMany children secondInputs reader = .done [rawSecond,capture] reader := by cbv
private theorem first_raw : build child firstInputs reader = .done rawFirst reader := by cbv
private theorem second_raw : build child secondInputs reader = .done rawSecond reader := by cbv
private theorem first_done : execute rawFirst environment reader = .done capture reader := by cbv
private theorem second_done : execute rawSecond environment reader = .done capture reader := by cbv
private theorem alive : [rawFirst,capture].any (fun value => value.referenceOf == .empty) = false := by cbv
private theorem generated_union : Mutual (Generated reader) capture capture := by
  exact SourceCurrentGeneratedNodeCases.live_child rows symbolic firstNames secondNames environment environment
    reader packed_effect.2.1.ready first_available second_available aliases paired replacements replacements
    8 false children List.mem_cons_self [rawFirst,capture] first_children alive child List.mem_cons_self
    rawFirst rawSecond capture capture first_raw second_raw first_done second_done
private theorem generated_fixed : Mutual (Generated reader) capture capture := by
  apply SourceCurrentGeneratedNodeCases.live_child rows symbolic firstNames secondNames environment environment
    reader packed_effect.2.1.ready first_available second_available aliases paired replacements replacements
    8 false children List.mem_cons_self [rawFirst,capture] first_children alive (.var 1) (by simp [children])
    capture capture capture capture
  · cbv
  · cbv
  · exact SourceCurrentStoredUnionObservations.closed capture _ reader (by cbv)
  · exact SourceCurrentStoredUnionObservations.closed capture _ reader (by cbv)

private theorem checked_witness :
    build nested [] empty = .done capture base ∧
    build pack packInputs base = .done packedValue reader ∧ Ready reader ∧
    Available reader capture ∧
    build (.node rows) firstInputs reader = .done firstNode reader ∧
    build (.node rows) secondInputs reader = .done secondNode reader ∧
    Aliases (.node rows) symbolic firstNames secondNames ∧
    Inputs reader environment environment firstInputs secondInputs ∧
    buildMany children firstInputs reader = .done [rawFirst,capture] reader ∧
    buildMany children secondInputs reader = .done [rawSecond,capture] reader ∧
    run (withoutSelfReference q rawFirst) reader = (capture,reader) ∧ rawFirst ≠ capture ∧
    run (withoutSelfReference (.interned reader.nodes.next) rawFirst) reader = (rawFirst,reader) ∧
    execute rawFirst environment reader = .done capture reader ∧
    execute rawSecond environment reader = .done capture reader ∧
    All₂ (Mutual (Generated reader)) [capture,capture] [capture,capture] := by
  refine ⟨base_done,packed_effect.1,packed_effect.2.1.ready,packed_effect.2.1.available _ capture_available,
    by cbv,by cbv,aliases,paired,first_children,second_children,by cbv,?_,by cbv,first_done,second_done,
    .cons generated_union (.cons generated_fixed .nil)⟩
  intro equal
  have same := congrArg Value.referenceOf equal
  cbv at same
  cases same

/-- An actual live union child needs its own absent filter and derives both generated directions. -/
theorem witness :
    build nested [] empty = .done capture base ∧
    build pack packInputs base = .done packedValue reader ∧ Ready reader ∧
    Available reader capture ∧
    build (.node rows) firstInputs reader = .done firstNode reader ∧
    build (.node rows) secondInputs reader = .done secondNode reader ∧
    Aliases (.node rows) symbolic firstNames secondNames ∧
    Inputs reader environment environment firstInputs secondInputs ∧
    buildMany children firstInputs reader = .done [rawFirst,capture] reader ∧
    buildMany children secondInputs reader = .done [rawSecond,capture] reader ∧
    run (withoutSelfReference q rawFirst) reader = (capture,reader) ∧ rawFirst ≠ capture ∧
    run (withoutSelfReference (.interned reader.nodes.next) rawFirst) reader = (rawFirst,reader) ∧
    execute rawFirst environment reader = .done capture reader ∧
    execute rawSecond environment reader = .done capture reader ∧
    All₂ (Mutual (Generated reader)) [capture,capture] [capture,capture] := checked_witness

end MicroCFTA.GeneratedNodeKernels

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.GeneratedNodeKernels.witness
#print MicroCFTA.GeneratedNodeKernels.witness
#print axioms MicroCFTA.GeneratedNodeKernels.witness
