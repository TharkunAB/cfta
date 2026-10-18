import MicroCFTA.SourceCurrentGeneratedNodeSchedules
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.NodeSchedulesKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open InternedEdgeResidency (nodeEdges)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentStoredNodeExpansion (RowCalls)
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
private def symbolic : List (Sum (Value Nat Bool) Unit) := [.inr (),.inl capture,.inl (.reference q)]
private def firstNames : Unit → Reference := fun _ => q
private def secondNames : Unit → Reference := fun _ => r
private def firstInputs := symbolic.map (input firstNames)
private def secondInputs := symbolic.map (input secondNames)
private def environment : Environment Nat Bool := fun name => if name = q ∨ name = r then some capture else none
private theorem inputs_available (state : State Nat Bool) (available : Available state capture) (name : Reference)
    (nameAvailable : Available state (.reference name)) :
    InternedNestedProvenance.Values state [.reference name,capture,.reference q] := by
  intro value member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact nameAvailable
  · exact available
  · exact reference_available state q (InternedFreshProbeKeys.sentinel_references_issued state.nodes 10).2
private theorem replacements (state : State Nat Bool) (available : Available state capture) : Replacements state environment := by
  intro name value found
  dsimp only [environment] at found
  split at found
  · cases found; exact available
  · cases found
private theorem first_inputs : InternedNestedProvenance.Values base firstInputs :=
  inputs_available base capture_available q
    (reference_available base q (InternedFreshProbeKeys.sentinel_references_issued base.nodes 10).2)
private def firstSource := build (.node rows) firstInputs base
private def firstNode := value firstSource
private def firstHeap := firstSource.state
private theorem first_effect : build (.node rows) firstInputs base = .done firstNode firstHeap ∧
    Keeps base firstHeap ∧ Available firstHeap firstNode :=
  source_effect (.node rows) firstInputs base base_ready first_inputs
private theorem second_inputs : InternedNestedProvenance.Values firstHeap secondInputs :=
  inputs_available firstHeap (first_effect.2.1.available _ capture_available) r
    (reference_available firstHeap r (InternedFreshProbeKeys.sentinel_references_issued firstHeap.nodes 11).2)
private def secondSource := build (.node rows) secondInputs firstHeap
private def secondNode := value secondSource
private def secondHeap := secondSource.state
private theorem second_effect : build (.node rows) secondInputs firstHeap = .done secondNode secondHeap ∧
    Keeps firstHeap secondHeap ∧ Available secondHeap secondNode :=
  source_effect (.node rows) secondInputs firstHeap first_effect.2.1.ready second_inputs
private theorem stored_effect (input : Value Nat Bool) (before : State Nat Bool) (ready : Ready before)
    (available : Available before input) (substitutions : Replacements before environment) :
    execute input environment before = .done (value (execute input environment before)) (execute input environment before).state ∧
      Keeps before (execute input environment before).state := by
  obtain ⟨result,after,called,kept,_,_⟩ := SourceCurrentStoredReconstruction.execute input environment before ready available substitutions
  rw [called]
  exact ⟨rfl,kept⟩
private def firstStored := execute firstNode environment secondHeap
private def firstResult := value firstStored
private def middle := firstStored.state
private theorem first_stored : execute firstNode environment secondHeap = .done firstResult middle ∧ Keeps secondHeap middle :=
  stored_effect firstNode secondHeap second_effect.2.1.ready (second_effect.2.1.available _ first_effect.2.2)
    (replacements secondHeap (second_effect.2.1.available _ (first_effect.2.1.available _ capture_available)))
private def secondStored := execute secondNode environment middle
private def secondResult := value secondStored
private def reader := secondStored.state
private theorem second_stored : execute secondNode environment middle = .done secondResult reader ∧ Keeps middle reader :=
  stored_effect secondNode middle first_stored.2.ready (first_stored.2.available _ second_effect.2.2)
    (replacements middle (first_stored.2.available _ (second_effect.2.1.available _ (first_effect.2.1.available _ capture_available))))
private theorem later : Keeps secondHeap reader := first_stored.2.trans second_stored.2
private theorem all_kept : Keeps base reader := first_effect.2.1.trans (second_effect.2.1.trans later)
private theorem first_current : Keeps firstHeap reader := second_effect.2.1.trans later
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
private theorem first_context : SourceCurrentConstrainedCapSourceHistory.Context base firstInputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context base base_ready.semantic firstInputs first_inputs,base_ready.semantic.2⟩
private theorem second_context : SourceCurrentConstrainedCapSourceHistory.Context firstHeap secondInputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context firstHeap first_effect.2.1.ready.semantic secondInputs second_inputs,
    first_effect.2.1.ready.semantic.2⟩
private theorem first_warm : execute firstNode environment reader = .done firstResult reader :=
  InternedFreshOrdinaryReplay.build_replay _ _ secondHeap reader firstResult middle
    second_effect.2.1.ready.semantic.1.normal.facts.coherent.valid first_stored.1 second_stored.2.growth
private theorem second_warm : execute secondNode environment reader = .done secondResult reader :=
  InternedFreshOrdinaryReplay.build_replay _ _ middle reader secondResult reader
    first_stored.2.ready.semantic.1.normal.facts.coherent.valid second_stored.1 (grows_refl _)
private def rawUnion := value (build child firstInputs base)
private def selectedRow := (run (makeEdge 8 false [rawUnion,capture]) firstHeap).1
private theorem selected : selectedRow ∈ InternedEdgeResidency.nodeEdges firstNode := by
  cbv
  exact List.mem_cons_self

private theorem checked_witness :
    build nested [] empty = .done capture base ∧
    build (.node rows) firstInputs base = .done firstNode firstHeap ∧
    build (.node rows) secondInputs firstHeap = .done secondNode secondHeap ∧
    execute firstNode environment secondHeap = .done firstResult middle ∧
    execute secondNode environment middle = .done secondResult reader ∧
    Ready reader ∧ base.nodes.next < reader.nodes.next ∧
    selectedRow.entry.key.symbol = 8 ∧ selectedRow.entry.key.constraint = false ∧
    firstResult = secondResult ∧
    (∃ firstRows firstAfter secondRows secondAfter index symbol guard children,
      ∃ (firstRow : RowCall rows (symbolic.map (input firstNames)) base firstRows firstAfter reader index symbol guard children)
        (secondRow : RowCall rows (symbolic.map (input secondNames)) firstHeap secondRows secondAfter reader index symbol guard children),
      buildEdges rows (symbolic.map (input firstNames)) base = .done firstRows firstAfter ∧
      run (makeNode firstRows) firstAfter = (firstNode,firstHeap) ∧
      buildEdges rows (symbolic.map (input secondNames)) firstHeap = .done secondRows secondAfter ∧
      run (makeNode secondRows) secondAfter = (secondNode,secondHeap) ∧
      firstRow.output = selectedRow ∧ secondRow.output ∈ nodeEdges secondNode ∧
      buildMany children (symbolic.map (input firstNames)) reader = .done firstRow.values reader ∧
      buildMany children (symbolic.map (input secondNames)) reader = .done secondRow.values reader ∧
      ∃ firstOutput secondOutput,
        RowCalls environment reader selectedRow firstOutput ∧ RowCalls environment reader secondRow.output secondOutput ∧
        All₂ (Mutual (Generated reader)) firstOutput.children secondOutput.children) := by
  refine ⟨base_done,first_effect.1,second_effect.1,first_stored.1,second_stored.1,later.ready,by cbv,by cbv,by cbv,by cbv,?_⟩
  exact SourceCurrentGeneratedNodeSchedules.node rows symbolic firstNames secondNames environment environment
    reader base firstHeap firstHeap secondHeap later.ready first_context second_context aliases paired
    (replacements reader (all_kept.available _ capture_available))
    (replacements reader (all_kept.available _ capture_available))
    firstNode secondNode firstResult secondResult first_effect.1 second_effect.1
    first_current.growth later.growth (first_current.available _ first_effect.2.2)
    (later.available _ second_effect.2.2) first_warm second_warm selectedRow selected

/-- Actual sequential parent calls derive every ordered stored child generator from their histories. -/
theorem witness :
    build nested [] empty = .done capture base ∧
    build (.node rows) firstInputs base = .done firstNode firstHeap ∧
    build (.node rows) secondInputs firstHeap = .done secondNode secondHeap ∧
    execute firstNode environment secondHeap = .done firstResult middle ∧
    execute secondNode environment middle = .done secondResult reader ∧
    Ready reader ∧ base.nodes.next < reader.nodes.next ∧
    selectedRow.entry.key.symbol = 8 ∧ selectedRow.entry.key.constraint = false ∧
    firstResult = secondResult ∧
    (∃ firstRows firstAfter secondRows secondAfter index symbol guard children,
      ∃ (firstRow : RowCall rows (symbolic.map (input firstNames)) base firstRows firstAfter reader index symbol guard children)
        (secondRow : RowCall rows (symbolic.map (input secondNames)) firstHeap secondRows secondAfter reader index symbol guard children),
      buildEdges rows (symbolic.map (input firstNames)) base = .done firstRows firstAfter ∧
      run (makeNode firstRows) firstAfter = (firstNode,firstHeap) ∧
      buildEdges rows (symbolic.map (input secondNames)) firstHeap = .done secondRows secondAfter ∧
      run (makeNode secondRows) secondAfter = (secondNode,secondHeap) ∧
      firstRow.output = selectedRow ∧ secondRow.output ∈ nodeEdges secondNode ∧
      buildMany children (symbolic.map (input firstNames)) reader = .done firstRow.values reader ∧
      buildMany children (symbolic.map (input secondNames)) reader = .done secondRow.values reader ∧
      ∃ firstOutput secondOutput,
        RowCalls environment reader selectedRow firstOutput ∧ RowCalls environment reader secondRow.output secondOutput ∧
        All₂ (Mutual (Generated reader)) firstOutput.children secondOutput.children) := checked_witness

end MicroCFTA.NodeSchedulesKernels
