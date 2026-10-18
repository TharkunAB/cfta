import MicroCFTA.SourceCurrentBoundedFilteredUnionFusion
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.BoundedUnionKernels
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryLiveInputs (input)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentUsedBinderAliasTransport (Scope Aliases)
open SourceCurrentBoundedFilteredFusion (Fusion)
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


private theorem filter_keeps (own : Reference) (raw : Value Nat Bool) (before : State Nat Bool)
    (ready : Ready before) (available : Available before raw) :
    Keeps before (run (withoutSelfReference own raw) before).2 := by
  cases raw with
  | empty | reference | node | mu => exact SourceEqualityRequiredCache.pure_keeps before ready
  | union entry members level free =>
      by_cases chosen : members.any (fun value => value.referenceOf == .ref own) = true
      · simp only [withoutSelfReference,chosen,↓reduceIte]
        exact (SourceEqualityNativeDemandHeapPrimitives.union _ before ready
          (fun value member => available.children value (List.mem_filter.mp member).1)).1
      · simp only [withoutSelfReference,chosen,Bool.false_eq_true,↓reduceIte,run]
        exact SourceEqualityRequiredCache.pure_keeps before ready

private def seed : Syntax Nat Bool :=
  .binder false (.node [.mk 7 false [.var 0,.binder false (.node [.mk 8 true [.var 0,.var 1]])]])
private def seeded := build seed [] empty
private def mu := value seeded
private def before := seeded.state
private def child : Syntax Nat Bool := .union [.var 0,.var 1,.var 2]
private def expressions : List (Syntax Nat Bool) := [child,.var 3,child,.empty]
private def source : Syntax Nat Bool := .union expressions
private def lexical : List (Sum (Value Nat Bool) Nat) := [.inr 0,.inr 1,.inr 2,.inr 3]
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
private def firstOwn := firstNames 0
private def secondOwn := secondNames 0
private def firstFilterRun := run (withoutSelfReference firstOwn firstRaw) secondHeap
private def firstFiltered := firstFilterRun.1
private def firstFilterHeap := firstFilterRun.2
private def secondFilterRun := run (withoutSelfReference secondOwn secondRaw) firstFilterHeap
private def secondFiltered := secondFilterRun.1
private def reader := secondFilterRun.2
private def firstMap : Environment Nat Bool := fun name => if name=firstOwn then some mu else some .empty
private def secondMap : Environment Nat Bool := fun name => if name=secondOwn then some mu else some .empty
private def firstChild := value (build child firstInputs reader)

private theorem seed_done : build seed [] empty = .done mu before := by cbv
private theorem initial_ready : Ready before := SourceEqualityRequiredCache.constructed seed mu before seed_done
private theorem mu_available : Available before mu :=
  (InternedFreshOrdinaryFacts.build_verified seed [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result mu before seed_done
private theorem first_available (state : State Nat Bool) : InternedNestedProvenance.Values state firstInputs := by
  intro value member
  have choices : value = .reference (firstNames 0) ∨ value = .reference (firstNames 1) ∨
      value = .reference (firstNames 2) ∨ value = .reference (firstNames 3) := by
    simpa only [firstInputs,lexical,List.map_cons,List.map_nil,input,List.mem_cons,List.not_mem_nil,or_false] using member
  rcases choices with rfl | rfl | rfl | rfl <;> exact InternedNestedProvenance.ordinary_available state _
private theorem second_available (state : State Nat Bool) : InternedNestedProvenance.Values state secondInputs := by
  intro value member
  have choices : value = .reference (secondNames 0) ∨ value = .reference (secondNames 1) ∨
      value = .reference (secondNames 2) ∨ value = .reference (secondNames 3) := by
    simpa only [secondInputs,lexical,List.map_cons,List.map_nil,input,List.mem_cons,List.not_mem_nil,or_false] using member
  rcases choices with rfl | rfl | rfl | rfl <;> exact InternedNestedProvenance.ordinary_available state _
private theorem first_effect : build source firstInputs before = .done firstRaw firstHeap ∧ Keeps before firstHeap ∧ Available firstHeap firstRaw :=
  source_effect source [firstNames 0,firstNames 1,firstNames 2,firstNames 3] before initial_ready (first_available before)
private theorem second_effect : build source secondInputs firstHeap = .done secondRaw secondHeap ∧ Keeps firstHeap secondHeap ∧ Available secondHeap secondRaw :=
  source_effect source [secondNames 0,secondNames 1,secondNames 2,secondNames 3] firstHeap first_effect.2.1.ready (second_available firstHeap)
private theorem first_filter_kept : Keeps secondHeap firstFilterHeap :=
  filter_keeps firstOwn firstRaw secondHeap second_effect.2.1.ready (second_effect.2.1.available firstRaw first_effect.2.2)
private theorem second_filter_kept : Keeps firstFilterHeap reader :=
  filter_keeps secondOwn secondRaw firstFilterHeap first_filter_kept.ready (first_filter_kept.available secondRaw second_effect.2.2)
private theorem after_first : Keeps firstHeap reader := second_effect.2.1.trans (first_filter_kept.trans second_filter_kept)
private theorem after_second : Keeps secondHeap reader := first_filter_kept.trans second_filter_kept
private theorem whole : Keeps before reader := first_effect.2.1.trans after_first
private theorem ready : Ready reader := whole.ready
private theorem first_context : Context before firstInputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context before initial_ready.semantic firstInputs (first_available before),initial_ready.semantic.2⟩
private theorem second_context : Context firstHeap secondInputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context firstHeap first_effect.2.1.ready.semantic secondInputs (second_available firstHeap),first_effect.2.1.ready.semantic.2⟩
private theorem first_replacements : Replacements reader firstMap := by
  intro name replacement found
  dsimp only [firstMap] at found
  split at found
  · cases found; exact whole.available mu mu_available
  · cases found; exact empty_available reader
private theorem second_replacements : Replacements reader secondMap := by
  intro name replacement found
  dsimp only [secondMap] at found
  split at found
  · cases found; exact whole.available mu mu_available
  · cases found; exact empty_available reader
private theorem scope : Scope source lexical = [.inl .depth,.inr 0,.inr 1,.inr 2,.inr 3,.inr 0,.inr 1,.inr 2] := by cbv
private theorem aliases : Aliases source lexical firstNames secondNames := by
  intro a ha b hb
  rw [scope] at ha hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem tests : ∀ label ∈ Scope source lexical,
    Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn := by
  intro label found
  rw [scope] at found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem paired : SourceCurrentReaderReplacementSlots.Paired
    (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) firstMap secondMap firstInputs secondInputs := by
  exact .cons (by cbv) (.cons (by cbv) (.cons (by cbv) (.cons (by cbv) .nil)))
private theorem child_fusion : Fusion 0 child := by
  apply SourceCurrentBoundedFilteredUnionFusion.union 0
  intro expression member
  rcases List.mem_cons.mp member with rfl | member
  · exact SourceCurrentBoundedFilteredFusion.reference 0 0
  · rcases List.mem_cons.mp member with rfl | member
    · exact SourceCurrentBoundedFilteredFusion.reference 0 1
    · obtain rfl := List.mem_singleton.mp member
      exact SourceCurrentBoundedFilteredFusion.reference 0 2
private theorem source_fusion : Fusion 0 source := by
  apply SourceCurrentBoundedFilteredUnionFusion.union 0
  intro expression member
  rcases List.mem_cons.mp member with rfl | member
  · exact child_fusion
  · rcases List.mem_cons.mp member with rfl | member
    · exact SourceCurrentBoundedFilteredFusion.reference 0 3
    · rcases List.mem_cons.mp member with rfl | member
      · exact child_fusion
      · obtain rfl := List.mem_singleton.mp member
        exact SourceCurrentBoundedFilteredFusion.empty 0
private theorem first_warm_filter : run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered,reader) := by cbv
private theorem second_warm_filter : run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered,reader) := by cbv
private theorem first_stored : execute firstFiltered firstMap reader = .done .empty reader := by cbv
private theorem second_stored : execute secondFiltered secondMap reader = .done .empty reader := by cbv

private def used : Value Nat Bool → Prop
  | .mu entry body _ _ => .interned entry.identity ∈ body.free
  | _ => False
private def nested_used : Value Nat Bool → Prop
  | .mu _ body _ _ => ∃ row ∈ InternedEdgeResidency.nodeEdges body, ∃ child ∈ row.children, used child
  | _ => False

private theorem checked :
    build seed [] empty = .done mu before ∧
    used mu ∧ nested_used mu ∧ 0 < mu.depth ∧
    expressions = [child,.var 3,child,.empty] ∧
    build source firstInputs before = .done firstRaw firstHeap ∧ build source secondInputs firstHeap = .done secondRaw secondHeap ∧
    firstRaw.depth = 0 ∧ secondRaw.depth = 0 ∧
    Ready reader ∧ firstRaw ≠ secondRaw ∧
    run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered,reader) ∧
    run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered,reader) ∧
    execute firstFiltered firstMap reader = .done .empty reader ∧ execute secondFiltered secondMap reader = .done .empty reader ∧
    execute (.reference firstOwn) firstMap reader = .done mu reader ∧
    ((Value.empty : Value Nat Bool).referenceOf == .empty) = ((Value.empty : Value Nat Bool).referenceOf == .empty) ∧
    reader.nodes.next < (run (withoutSelfReference firstOwn firstChild) reader).2.nodes.next := by
  have fused := source_fusion reader ready lexical firstNames secondNames firstOwn secondOwn firstMap secondMap
    before firstHeap firstHeap secondHeap firstRaw secondRaw firstFiltered secondFiltered .empty .empty
    (by cbv) (by cbv) first_context second_context aliases tests paired first_replacements second_replacements
    (after_first.available firstRaw first_effect.2.2) (after_second.available secondRaw second_effect.2.2)
    first_effect.1 second_effect.1 after_first.growth after_second.growth
    first_warm_filter second_warm_filter first_stored second_stored
  refine ⟨seed_done,?_,?_,?_,rfl,first_effect.1,second_effect.1,?_,?_,ready,?_,first_warm_filter,second_warm_filter,
    first_stored,second_stored,?_,fused,?_⟩
  · cbv
    exact List.mem_cons_self
  · cbv
    refine ⟨_,List.mem_cons_self,_,List.mem_cons_of_mem _ List.mem_cons_self,?_⟩
    cbv
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · cbv
  · cbv
  · cbv
  · cbv; intro impossible; cases impossible
  · cbv
  · cbv

/-- Duplicate and Empty union members retain original depth zero while a resolved member returns a nested used Mu of greater depth. -/
theorem witness :
    build seed [] empty = .done mu before ∧
    used mu ∧ nested_used mu ∧ 0 < mu.depth ∧
    expressions = [child,.var 3,child,.empty] ∧
    build source firstInputs before = .done firstRaw firstHeap ∧ build source secondInputs firstHeap = .done secondRaw secondHeap ∧
    firstRaw.depth = 0 ∧ secondRaw.depth = 0 ∧
    Ready reader ∧ firstRaw ≠ secondRaw ∧
    run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered,reader) ∧
    run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered,reader) ∧
    execute firstFiltered firstMap reader = .done .empty reader ∧ execute secondFiltered secondMap reader = .done .empty reader ∧
    execute (.reference firstOwn) firstMap reader = .done mu reader ∧
    ((Value.empty : Value Nat Bool).referenceOf == .empty) = ((Value.empty : Value Nat Bool).referenceOf == .empty) ∧
    reader.nodes.next < (run (withoutSelfReference firstOwn firstChild) reader).2.nodes.next := checked

end MicroCFTA.BoundedUnionKernels
