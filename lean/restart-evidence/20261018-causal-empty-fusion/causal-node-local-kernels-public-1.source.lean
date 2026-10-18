import MicroCFTA.SourceCurrentCausalGeneratedNodeLocal
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.CausalGeneratedNodeLocalIntegration
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryLiveInputs (input)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentSourceDirectedCases (Local)
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



private def leaf : Syntax Nat Bool := .node [.mk 1 true []]
private def retained : List (EdgeSyntax Nat Bool) := [.mk 10 false [leaf],.mk 11 true []]
private def seed : Syntax Nat Bool := .node (.mk 9 true [.empty] :: retained)
private def seeded := build seed [] empty
private def output := value seeded
private def before := seeded.state
private def rows : List (EdgeSyntax Nat Bool) := .mk 9 true [.var 0] :: retained
private def source : Syntax Nat Bool := .node rows
private def lexical : List (Sum (Value Nat Bool) Unit) := [.inr ()]
private def firstNames : Unit → Reference := fun _ => .uninterned 0
private def secondNames : Unit → Reference := fun _ => .uninterned 1
private def firstRun := build source (lexical.map (input firstNames)) before
private def firstRaw := value firstRun
private def middle := firstRun.state
private def secondRun := build source (lexical.map (input secondNames)) middle
private def secondRaw := value secondRun
private def reader := secondRun.state
private def environment : Environment Nat Bool := fun _ => some .empty
private theorem seed_done : build seed [] empty = .done output before := by cbv
private theorem before_ready : Ready before := SourceEqualityRequiredCache.constructed seed output before seed_done
private theorem first_effect : build source (lexical.map (input firstNames)) before = .done firstRaw middle ∧
    Keeps before middle ∧ Available middle firstRaw :=
  source_effect source [.uninterned 0] before before_ready (by
    intro supplied member
    obtain rfl := List.mem_singleton.mp member
    exact InternedNestedProvenance.ordinary_available before 0)
private theorem second_effect : build source (lexical.map (input secondNames)) middle = .done secondRaw reader ∧
    Keeps middle reader ∧ Available reader secondRaw :=
  source_effect source [.uninterned 1] middle first_effect.2.1.ready (by
    intro supplied member
    obtain rfl := List.mem_singleton.mp member
    exact InternedNestedProvenance.ordinary_available middle 1)
private theorem first_context : Context before (lexical.map (input firstNames)) :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context before before_ready.semantic _ (by
    intro supplied member
    obtain rfl := List.mem_singleton.mp member
    exact InternedNestedProvenance.ordinary_available before 0),before_ready.semantic.2⟩
private theorem second_context : Context middle (lexical.map (input secondNames)) :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context middle first_effect.2.1.ready.semantic _ (by
    intro supplied member
    obtain rfl := List.mem_singleton.mp member
    exact InternedNestedProvenance.ordinary_available middle 1),first_effect.2.1.ready.semantic.2⟩
private theorem replacements : Replacements reader environment := by
  intro name supplied found
  have same : supplied = .empty := Option.some.inj found.symm
  subst supplied
  exact empty_available reader
private theorem aliases : SourceCurrentUsedBinderAliasTransport.Aliases source lexical firstNames secondNames := by
  intro a ha b hb
  have scope : SourceCurrentUsedBinderAliasTransport.Scope source lexical = [.inl .depth,.inr ()] := by cbv
  rw [scope] at ha hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [firstNames,secondNames]
private theorem history : Nonempty (History empty reader) := by
  obtain ⟨seedHistory⟩ := SourceCurrentNativeMuPublication.build_history seed [] empty
    SourceCurrentConstrainedCapSourceHistory.empty_context
  obtain ⟨firstHistory⟩ := SourceCurrentNativeMuPublication.build_history source (lexical.map (input firstNames)) before first_context
  obtain ⟨secondHistory⟩ := SourceCurrentNativeMuPublication.build_history source (lexical.map (input secondNames)) middle second_context
  exact ⟨.trans seedHistory (.trans firstHistory secondHistory)⟩
private theorem paired : Inputs reader environment environment
    (lexical.map (input firstNames)) (lexical.map (input secondNames)) :=
  .reference (.refl .empty) (.refl .empty) (.nil environment environment)

private theorem checked :
    ∃ (rows : List (EdgeSyntax Nat Bool)) (inputs : List (Sum (Value Nat Bool) Unit))
      (firstNames secondNames : Unit → Reference) (environment : Environment Nat Bool)
      (before middle reader : State Nat Bool) (firstRaw secondRaw output : Value Nat Bool),
      rows = [.mk 9 true [.var 0],.mk 10 false [.node [.mk 1 true []]],.mk 11 true []] ∧
      inputs = [.inr ()] ∧ firstNames () = .uninterned 0 ∧ secondNames () = .uninterned 1 ∧
      Context before (inputs.map (input firstNames)) ∧ Context middle (inputs.map (input secondNames)) ∧
      build (.node rows) (inputs.map (input firstNames)) before = .done firstRaw middle ∧
      build (.node rows) (inputs.map (input secondNames)) middle = .done secondRaw reader ∧
      Ready reader ∧ Nonempty (History empty reader) ∧ firstRaw ≠ secondRaw ∧
      Grows middle reader ∧ Available reader firstRaw ∧ Available reader secondRaw ∧
      Inputs reader environment environment (inputs.map (input firstNames)) (inputs.map (input secondNames)) ∧
      Replacements reader environment ∧
      execute firstRaw environment reader = .done output reader ∧
      execute secondRaw environment reader = .done output reader ∧
      (nodeEdges firstRaw).length = 3 ∧
      (nodeEdges output).map (fun row => (row.entry.key.symbol,row.entry.key.constraint)) = [(10,false),(11,true)] ∧
      Local reader (Generated reader) output output ∧ Local reader (Generated reader) output output := by
  have firstDone : execute firstRaw environment reader = .done output reader := by cbv
  have secondDone : execute secondRaw environment reader = .done output reader := by cbv
  obtain ⟨history⟩ := history
  have clauses := SourceCurrentCausalGeneratedNodeLocal.node rows lexical firstNames secondNames environment environment
    reader before middle middle reader second_effect.2.1.ready history first_context second_context aliases paired
    replacements replacements firstRaw secondRaw output output first_effect.1 second_effect.1
    second_effect.2.1.growth (grows_refl _) (second_effect.2.1.available firstRaw first_effect.2.2)
    second_effect.2.2 firstDone secondDone
  refine ⟨rows,lexical,firstNames,secondNames,environment,before,middle,reader,firstRaw,secondRaw,output,
    rfl,rfl,rfl,rfl,first_context,second_context,first_effect.1,second_effect.1,second_effect.2.1.ready,
    ⟨history⟩,?_,second_effect.2.1.growth,second_effect.2.1.available firstRaw first_effect.2.2,
    second_effect.2.2,paired,replacements,firstDone,secondDone,by cbv,by cbv,clauses⟩
  intro impossible
  have refs := congrArg Value.referenceOf impossible
  cbv at refs
  cases refs

/-- Actual changed references kill one row and retain both full-guard local row clauses. -/
theorem changed_reference_rows :
    ∃ (rows : List (EdgeSyntax Nat Bool)) (inputs : List (Sum (Value Nat Bool) Unit))
      (firstNames secondNames : Unit → Reference) (environment : Environment Nat Bool)
      (before middle reader : State Nat Bool) (firstRaw secondRaw output : Value Nat Bool),
      rows = [.mk 9 true [.var 0],.mk 10 false [.node [.mk 1 true []]],.mk 11 true []] ∧
      inputs = [.inr ()] ∧ firstNames () = .uninterned 0 ∧ secondNames () = .uninterned 1 ∧
      Context before (inputs.map (input firstNames)) ∧ Context middle (inputs.map (input secondNames)) ∧
      build (.node rows) (inputs.map (input firstNames)) before = .done firstRaw middle ∧
      build (.node rows) (inputs.map (input secondNames)) middle = .done secondRaw reader ∧
      Ready reader ∧ Nonempty (History empty reader) ∧ firstRaw ≠ secondRaw ∧
      Grows middle reader ∧ Available reader firstRaw ∧ Available reader secondRaw ∧
      Inputs reader environment environment (inputs.map (input firstNames)) (inputs.map (input secondNames)) ∧
      Replacements reader environment ∧
      execute firstRaw environment reader = .done output reader ∧
      execute secondRaw environment reader = .done output reader ∧
      (nodeEdges firstRaw).length = 3 ∧
      (nodeEdges output).map (fun row => (row.entry.key.symbol,row.entry.key.constraint)) = [(10,false),(11,true)] ∧
      Local reader (Generated reader) output output ∧ Local reader (Generated reader) output output := checked

end MicroCFTA.CausalGeneratedNodeLocalIntegration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.CausalGeneratedNodeLocalIntegration.changed_reference_rows
#print MicroCFTA.CausalGeneratedNodeLocalIntegration.changed_reference_rows
#print axioms MicroCFTA.CausalGeneratedNodeLocalIntegration.changed_reference_rows
