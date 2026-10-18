import MicroCFTA.SourceCurrentTrackedFilteredNodeFusion
import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.TrackedNodeKernels
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryLiveInputs (input)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentTrackedRootProfile (Related)
open SourceCurrentTrackedFilteredFusion (Fusion)
private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private theorem source_effect (term : Syntax Nat Bool) (names : List Reference)
    (before : State Nat Bool) (ready : Ready before)
    (available : InternedNestedProvenance.Values before (names.map Value.reference)) :
    build term (names.map Value.reference) before =
      .done (value (build term (names.map Value.reference) before)) (build term (names.map Value.reference) before).state ∧
      Keeps before (build term (names.map Value.reference) before).state ∧
      Available (build term (names.map Value.reference) before).state (value (build term (names.map Value.reference) before)) := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic _ available
  obtain ⟨result,after,called⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete term names before context ready.semantic.2 ready.covered
  have checked := InternedFreshOrdinaryFacts.build_verified term _ before ready.semantic.1.normal.facts available
  have kept : Keeps before after := by
    refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
    · simpa only [called,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source term _ before ready.semantic available
    · exact InternedFreshOrdinaryCoverage.build_covered term _ before ready.semantic.1.normal.facts.coherent.valid ready.covered result after called
    · simpa only [called,Outcome.state] using (InternedOpenDepthExecution.build_depth term _ before context ready.semantic.2 ready.depth).heap
    · simpa only [called,Outcome.state] using checked.growth
    · simpa only [called,Outcome.state] using checked.history
  rw [called]
  exact ⟨rfl,kept,checked.result result after called⟩


private theorem stored_keeps (raw : Value Nat Bool) (environment : Environment Nat Bool)
    (before : State Nat Bool) (ready : Ready before) (available : Available before raw)
    (replacements : Replacements before environment) : Keeps before (execute raw environment before).state := by
  obtain ⟨result,after,actual,kept,_,_⟩ := SourceCurrentStoredReconstruction.execute raw environment before ready available replacements
  simpa only [actual,Outcome.state] using kept

private def seed : Syntax Nat Bool := .node [.mk 2 true []]
private def seeded := build seed [] empty
private def leaf := value seeded
private def before := seeded.state
private def rows : List (EdgeSyntax Nat Bool) := [.mk 5 false [.var 0,.var 1]]
private def source : Syntax Nat Bool := .node rows
private def lexical : List (Sum (Value Nat Bool) Nat) := [.inr 0,.inr 1]
private def firstNames (index : Nat) : Reference := .uninterned (index+10)
private def secondNames (index : Nat) : Reference := .uninterned (index+20)
private def firstInputs := lexical.map (input firstNames)
private def secondInputs := lexical.map (input secondNames)
private def firstRun := build source firstInputs before
private def firstRaw := value firstRun
private def firstHeap := firstRun.state
private def secondRun := build source secondInputs firstHeap
private def secondRaw := value secondRun
private def secondHeap := secondRun.state
private def markers : List Reference := [.uninterned 99]
private def firstMap : Environment Nat Bool := fun name =>
  if name=firstNames 0 then some (.reference (.uninterned 99))
  else if name=firstNames 1 then some (.reference (.uninterned 98)) else none
private def secondMap : Environment Nat Bool := fun name =>
  if name=secondNames 0 then some (.reference (.uninterned 99))
  else if name=secondNames 1 then some leaf else none
private def firstCall := execute firstRaw firstMap secondHeap
private def left := value firstCall
private def firstAfter := firstCall.state
private def secondCall := execute secondRaw secondMap firstAfter
private def right := value secondCall
private def reader := secondCall.state
private def row := (nodeEdges left)[0]?.getD (.mk ⟨0,.mk 0 [] false⟩ [])

private theorem seed_done : build seed [] empty = .done leaf before := by cbv
private theorem initial_ready : Ready before := SourceEqualityRequiredCache.constructed seed leaf before seed_done
private theorem leaf_available : Available before leaf :=
  (InternedFreshOrdinaryFacts.build_verified seed [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result leaf before seed_done
private theorem first_available (state : State Nat Bool) : InternedNestedProvenance.Values state firstInputs := by
  intro value member
  have choices : value = .reference (firstNames 0) ∨ value = .reference (firstNames 1) := by
    simpa only [firstInputs,lexical,List.map_cons,List.map_nil,input,List.mem_cons,List.not_mem_nil,or_false] using member
  rcases choices with rfl | rfl <;> exact InternedNestedProvenance.ordinary_available state _
private theorem second_available (state : State Nat Bool) : InternedNestedProvenance.Values state secondInputs := by
  intro value member
  have choices : value = .reference (secondNames 0) ∨ value = .reference (secondNames 1) := by
    simpa only [secondInputs,lexical,List.map_cons,List.map_nil,input,List.mem_cons,List.not_mem_nil,or_false] using member
  rcases choices with rfl | rfl <;> exact InternedNestedProvenance.ordinary_available state _
private theorem first_effect : build source firstInputs before = .done firstRaw firstHeap ∧ Keeps before firstHeap ∧ Available firstHeap firstRaw :=
  source_effect source [firstNames 0,firstNames 1] before initial_ready (first_available before)
private theorem second_effect : build source secondInputs firstHeap = .done secondRaw secondHeap ∧ Keeps firstHeap secondHeap ∧ Available secondHeap secondRaw :=
  source_effect source [secondNames 0,secondNames 1] firstHeap first_effect.2.1.ready (second_available firstHeap)
private theorem first_replacements (state : State Nat Bool) : Replacements state firstMap := by
  intro name replacement found
  dsimp only [firstMap] at found
  split at found
  · cases found; exact InternedNestedProvenance.ordinary_available state _
  · split at found
    · cases found; exact InternedNestedProvenance.ordinary_available state _
    · cases found
private theorem first_kept : Keeps secondHeap firstAfter := stored_keeps firstRaw firstMap secondHeap
  second_effect.2.1.ready (second_effect.2.1.available firstRaw first_effect.2.2) (first_replacements secondHeap)
private theorem early : Keeps before firstAfter := first_effect.2.1.trans (second_effect.2.1.trans first_kept)
private theorem second_replacements : Replacements firstAfter secondMap := by
  intro name replacement found
  dsimp only [secondMap] at found
  split at found
  · cases found; exact InternedNestedProvenance.ordinary_available firstAfter _
  · split at found
    · cases found; exact early.available leaf leaf_available
    · cases found
private theorem second_kept : Keeps firstAfter reader := stored_keeps secondRaw secondMap firstAfter first_kept.ready
  (first_kept.available secondRaw second_effect.2.2) second_replacements
private theorem after_first : Keeps firstHeap reader := second_effect.2.1.trans (first_kept.trans second_kept)
private theorem after_second : Keeps secondHeap reader := first_kept.trans second_kept
private theorem ready : Ready reader := second_kept.ready
private theorem first_context : Context before firstInputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context before initial_ready.semantic firstInputs (first_available before),initial_ready.semantic.2⟩
private theorem second_context : Context firstHeap secondInputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context firstHeap first_effect.2.1.ready.semantic secondInputs (second_available firstHeap),first_effect.2.1.ready.semantic.2⟩
private theorem untracked : Related markers (.reference (.uninterned 98) : Value Nat Bool) leaf := by
  have first : SourceCurrentTrackedRootProfile.observe markers (.reference (.uninterned 98) : Value Nat Bool) = none := by cbv
  have second : SourceCurrentTrackedRootProfile.observe markers leaf = none := by cbv
  unfold Related
  rw [first,second]
  exact InternedProfileEquivalence.refl _
private theorem paired : SourceCurrentReaderReplacementSlots.Paired (Related markers) firstMap secondMap firstInputs secondInputs := by
  refine .cons ?_ (.cons ?_ .nil)
  · change Related markers (.reference (.uninterned 99) : Value Nat Bool) (.reference (.uninterned 99))
    exact Related.refl _ _
  · change Related markers (.reference (.uninterned 98) : Value Nat Bool) leaf
    exact untracked
private theorem children : ∀ symbol guard expressions, EdgeSyntax.mk symbol guard expressions ∈ rows →
    ∀ child ∈ expressions, Fusion 0 child := by
  intro symbol guard expressions member
  obtain equal := List.mem_singleton.mp member
  cases equal
  intro child member
  rcases List.mem_cons.mp member with rfl | member
  · exact SourceCurrentTrackedFilteredFusion.reference 0 0
  · obtain rfl := List.mem_singleton.mp member
    exact SourceCurrentTrackedFilteredFusion.reference 0 1

private theorem checked :
    Ready reader ∧ firstRaw ≠ secondRaw ∧ left ≠ right ∧
    (nodeEdges left)[0]?.map EdgeValue.children = some [.reference (.uninterned 99),.reference (.uninterned 98)] ∧
    (nodeEdges right)[0]?.map EdgeValue.children = some [.reference (.uninterned 99),leaf] ∧
    execute firstRaw firstMap reader = .done left reader ∧ execute secondRaw secondMap reader = .done right reader ∧
    Related markers (.reference (.uninterned 98) : Value Nat Bool) leaf ∧
    Related markers left right ∧
    ∃ other ∈ nodeEdges right,
      row.entry.key.symbol = other.entry.key.symbol ∧ row.entry.key.constraint = other.entry.key.constraint ∧
      All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) row.children other.children := by
  have aliases : SourceCurrentUsedBinderAliasTransport.Aliases source lexical firstNames secondNames := by
    intro a ha b hb
    have scope : SourceCurrentUsedBinderAliasTransport.Scope source lexical = [.inl .depth,.inr 0,.inr 1] := by cbv
    rw [scope] at ha hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> decide
  have tests : ∀ label ∈ SourceCurrentUsedBinderAliasTransport.Scope source lexical,
      Sum.elim id firstNames label = .depth ↔ Sum.elim id secondNames label = .depth := by
    intro label member
    have scope : SourceCurrentUsedBinderAliasTransport.Scope source lexical = [.inl .depth,.inr 0,.inr 1] := by cbv
    rw [scope] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  have firstStored : execute firstRaw firstMap reader = .done left reader := by cbv
  have secondStored : execute secondRaw secondMap reader = .done right reader := by cbv
  have firstReplacement := first_replacements reader
  have secondReplacement : Replacements reader secondMap := by
    intro name value found
    exact second_kept.available value (second_replacements name value found)
  have result := SourceCurrentTrackedFilteredNodeFusion.node 0 rows children markers reader ready lexical firstNames secondNames
    .depth .depth firstMap secondMap before firstHeap firstHeap secondHeap firstRaw secondRaw firstRaw secondRaw left right
    (by cbv) (by cbv) first_context second_context aliases tests paired firstReplacement secondReplacement
    (after_first.available firstRaw first_effect.2.2) (after_second.available secondRaw second_effect.2.2)
    first_effect.1 second_effect.1 after_first.growth after_second.growth (by cbv) (by cbv) firstStored secondStored
  have survivor := SourceCurrentTrackedFilteredNodeFusion.row 0 rows children lexical firstNames secondNames firstMap secondMap
    reader before firstHeap firstHeap secondHeap ready first_context second_context aliases paired firstReplacement secondReplacement
    firstRaw secondRaw left right (by cbv) (by cbv) first_effect.1 second_effect.1 after_first.growth after_second.growth
    (after_first.available firstRaw first_effect.2.2) (after_second.available secondRaw second_effect.2.2)
    firstStored secondStored row (by cbv; exact List.mem_cons_self)
  refine ⟨ready,?_,?_,?_,?_,firstStored,secondStored,untracked,result,survivor⟩
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible
  · cbv
  · cbv

/-- Tracked markers and an untracked reference versus an opaque node produce distinct related parent outputs. -/
theorem distinct_outputs :
    Ready reader ∧ firstRaw ≠ secondRaw ∧ left ≠ right ∧
    (nodeEdges left)[0]?.map EdgeValue.children = some [.reference (.uninterned 99),.reference (.uninterned 98)] ∧
    (nodeEdges right)[0]?.map EdgeValue.children = some [.reference (.uninterned 99),leaf] ∧
    execute firstRaw firstMap reader = .done left reader ∧ execute secondRaw secondMap reader = .done right reader ∧
    Related markers (.reference (.uninterned 98) : Value Nat Bool) leaf ∧
    Related markers left right ∧
    ∃ other ∈ nodeEdges right,
      row.entry.key.symbol = other.entry.key.symbol ∧ row.entry.key.constraint = other.entry.key.constraint ∧
      All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) row.children other.children := checked

end MicroCFTA.TrackedNodeKernels
