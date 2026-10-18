import MicroCFTA.SourceCurrentFilteredNodeFusion
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.FilteredNodeFusionKernels
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
open SourceCurrentFilteredSourceFusion (Fusion)
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
private theorem child_fusion : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ rows →
    ∀ child ∈ children, Fusion child := by
  intro symbol guard children member
  rcases List.mem_cons.mp member with equal | member
  · cases equal
    intro child found
    obtain rfl := List.mem_singleton.mp found
    exact SourceCurrentFilteredSourceFusion.reference 0
  · rcases List.mem_cons.mp member with equal | member
    · cases equal
      intro child found
      obtain rfl := List.mem_singleton.mp found
      apply SourceCurrentFilteredNodeFusion.node
      intro own guard children member
      obtain equal := List.mem_singleton.mp member
      cases equal
      intro child impossible
      cases impossible
    · obtain equal := List.mem_singleton.mp member
      cases equal
      intro child impossible
      cases impossible
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
private theorem tests : ∀ label ∈ SourceCurrentUsedBinderAliasTransport.Scope source lexical,
    Sum.elim id firstNames label = .interned reader.nodes.next ↔
      Sum.elim id secondNames label = .interned reader.nodes.next := by
  intro label member
  have choices : label = .inl .depth ∨ label = .inr () := by
    have scope : SourceCurrentUsedBinderAliasTransport.Scope source lexical = [.inl .depth,.inr ()] := by cbv
    rw [scope] at member
    exact (List.mem_cons.mp member).elim Or.inl (fun rest => Or.inr (List.mem_singleton.mp rest))
  rcases choices with rfl | rfl <;> simp [firstNames,secondNames]

/-- Distinct source references resolve to Empty and remove the same row at one actual reader. -/
private theorem checked :
    build source (lexical.map (input firstNames)) before = .done firstRaw middle ∧
    build source (lexical.map (input secondNames)) middle = .done secondRaw reader ∧
    Ready reader ∧ firstRaw ≠ secondRaw ∧
    execute firstRaw environment reader = .done output reader ∧
    execute secondRaw environment reader = .done output reader ∧
    (nodeEdges firstRaw).length = 3 ∧ (nodeEdges output).length = 2 ∧
    (output.referenceOf == .empty) = (output.referenceOf == .empty) := by
  have firstDone : execute firstRaw environment reader = .done output reader := by cbv
  have secondDone : execute secondRaw environment reader = .done output reader := by cbv
  have paired : SourceCurrentReaderReplacementSlots.Paired
      (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) environment environment
      (lexical.map (input firstNames)) (lexical.map (input secondNames)) := by
    exact .cons rfl .nil
  have firstFilter : run (withoutSelfReference (.interned reader.nodes.next) firstRaw) reader = (firstRaw,reader) := by cbv
  have secondFilter : run (withoutSelfReference (.interned reader.nodes.next) secondRaw) reader = (secondRaw,reader) := by cbv
  have fused := SourceCurrentFilteredNodeFusion.node rows child_fusion reader second_effect.2.1.ready lexical firstNames secondNames
    (.interned reader.nodes.next) (.interned reader.nodes.next) environment environment before middle middle reader
    firstRaw secondRaw firstRaw secondRaw output output first_context second_context aliases tests paired replacements replacements
    (second_effect.2.1.available firstRaw first_effect.2.2) second_effect.2.2 first_effect.1 second_effect.1 second_effect.2.1.growth (grows_refl _)
    firstFilter secondFilter firstDone secondDone
  refine ⟨first_effect.1,second_effect.1,second_effect.2.1.ready,?_,firstDone,secondDone,by cbv,by cbv,fused⟩
  intro impossible
  have refs := congrArg Value.referenceOf impossible
  cbv at refs
  cases refs

/-- Distinct source references resolve to Empty and remove the same actual row. -/
theorem changing_reference :
    build source (lexical.map (input firstNames)) before = .done firstRaw middle ∧
    build source (lexical.map (input secondNames)) middle = .done secondRaw reader ∧
    Ready reader ∧ firstRaw ≠ secondRaw ∧
    execute firstRaw environment reader = .done output reader ∧
    execute secondRaw environment reader = .done output reader ∧
    (nodeEdges firstRaw).length = 3 ∧ (nodeEdges output).length = 2 ∧
    (output.referenceOf == .empty) = (output.referenceOf == .empty) := checked

end MicroCFTA.FilteredNodeFusionKernels
