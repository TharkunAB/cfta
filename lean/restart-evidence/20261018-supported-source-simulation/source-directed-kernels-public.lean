import MicroCFTA.SourceCurrentSourceDirectedCases
import MicroCFTA.SourceCurrentReaderReplacementSlots
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.SourceDirectedKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves encode input)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentSourceDirectedCases (Below Local)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def nested : Syntax Nat Bool := .binder true (.node [.mk 7 true [],.mk 9 false [.var 0]])
private def leaf : Syntax Nat Bool := .node [.mk 3 true []]
private def source : Syntax Nat Bool := .node [.mk 0 false [nested,leaf,.union [nested,leaf]]]
private def built := build source [] empty
private def root := value built
private def base := built.state
private def capture : Value Nat Bool := (children root)[0]?.getD .empty
private def ordinary : Value Nat Bool := (children root)[1]?.getD .empty
private def group : Value Nat Bool := (children root)[2]?.getD .empty
private theorem built_done : build source [] empty = .done root base := by cbv
private theorem base_ready : Ready base := SourceEqualityRequiredCache.constructed source root base built_done
private theorem root_available : Available base root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro supplied member; cases member)).result root base built_done
private theorem capture_available : Available base capture := root_available.children capture
  (List.mem_of_getElem? (show (children root)[0]? = some capture by cbv))
private theorem ordinary_available : Available base ordinary := root_available.children ordinary
  (List.mem_of_getElem? (show (children root)[1]? = some ordinary by cbv))
private theorem group_available : Available base group := root_available.children group
  (List.mem_of_getElem? (show (children root)[2]? = some group by cbv))
private def fields : Value Nat Bool → Interned InternedBinderProtocol.NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private theorem capture_shape : capture = .mu (fields capture).1 (fields capture).2.1 (fields capture).2.2.1 (fields capture).2.2.2 := by cbv
private theorem capture_used : InternedFreshOrdinaryDepthHeap.usesLocal (fields capture).2.2.1 (fields capture).2.2.2 = true := by cbv
private theorem capture_closed : capture.free = [] := by cbv
private theorem group_closed : group.free = [] := by cbv
private theorem ordinary_closed : ordinary.free = [] := by cbv

private def q : Reference := .uninterned 10
private def r : Reference := .uninterned 11
private def first : Environment Nat Bool := fun name => if name = q then some capture else none
private def second : Environment Nat Bool := fun name => if name = r then some capture else none
private def expressions : List (EdgeSyntax Nat Bool) :=
  [.mk 8 false [.var 0,.var 1],.mk 2 true [],.mk 8 false [.var 0,.var 1]]
private def expression : Syntax Nat Bool := .node expressions

private theorem source_effect (term : Syntax Nat Bool) (inputs : List (Value Nat Bool))
    (before : State Nat Bool) (ready : Ready before) (available : InternedNestedProvenance.Values before inputs) :
    build term inputs before = .done (value (build term inputs before)) (build term inputs before).state ∧
      Keeps before (build term inputs before).state ∧
      Available (build term inputs before).state (value (build term inputs before)) := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic inputs available
  obtain ⟨result,after,actual⟩ := InternedRecordDepthCompletion.source_complete term inputs before context ready.semantic.2 ready.covered
  have checked := InternedFreshOrdinaryFacts.build_verified term inputs before ready.semantic.1.normal.facts available
  have kept : Keeps before after := by
    refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
    · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source term inputs before ready.semantic available
    · exact InternedFreshOrdinaryCoverage.build_covered term inputs before ready.semantic.1.normal.facts.coherent.valid ready.covered result after actual
    · simpa only [actual,Outcome.state] using (InternedOpenDepthExecution.build_depth term inputs before context ready.semantic.2 ready.depth).heap
    · simpa only [actual,Outcome.state] using checked.growth
    · simpa only [actual,Outcome.state] using checked.history
  rw [actual]
  exact ⟨rfl,kept,checked.result result after actual⟩
private theorem inputs (before : State Nat Bool) (captureAvailable : Available before capture) (name : Reference)
    (named : Available before (.reference name)) : InternedNestedProvenance.Values before [.reference name,capture] := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact named
  · exact (List.mem_singleton.mp member) ▸ captureAvailable
private def rawRun := build expression [.reference q,capture] base
private def rawFirst := value rawRun
private def rawMiddle := rawRun.state
private theorem raw_effect :
    build expression [.reference q,capture] base = .done rawFirst rawMiddle ∧ Keeps base rawMiddle ∧ Available rawMiddle rawFirst := source_effect expression [.reference q,capture] base base_ready
  (inputs base capture_available q (reference_available base q (InternedFreshProbeKeys.sentinel_references_issued base.nodes 10).2))
private def otherRun := build expression [.reference r,capture] rawMiddle
private def rawSecond := value otherRun
private def afterRaw := otherRun.state
private theorem other_effect :
    build expression [.reference r,capture] rawMiddle = .done rawSecond afterRaw ∧ Keeps rawMiddle afterRaw ∧ Available afterRaw rawSecond := source_effect expression [.reference r,capture] rawMiddle raw_effect.2.1.ready
  (inputs rawMiddle (raw_effect.2.1.available capture capture_available) r
    (reference_available rawMiddle r (InternedFreshProbeKeys.sentinel_references_issued rawMiddle.nodes 11).2))
private theorem raw_keeps : Keeps base afterRaw := raw_effect.2.1.trans other_effect.2.1
private theorem replacements (before : State Nat Bool) (available : Available before capture) (name : Reference) :
    Replacements before (fun candidate => if candidate = name then some capture else none) := by
  intro candidate replacement found
  dsimp only at found
  split at found
  · cases found; exact available
  · cases found
private theorem execute_effect (raw : Value Nat Bool) (environment : Environment Nat Bool)
    (before : State Nat Bool) (ready : Ready before) (available : Available before raw)
    (replacements : Replacements before environment) :
    execute raw environment before = .done (value (execute raw environment before)) (execute raw environment before).state ∧
      Keeps before (execute raw environment before).state := by
  obtain ⟨result,after,actual,kept,_,_⟩ := SourceCurrentStoredReconstruction.execute raw environment before ready available replacements
  rw [actual]
  exact ⟨rfl,kept⟩
private def firstRun := execute rawFirst first afterRaw
private def left := value firstRun
private def middle := firstRun.state
private theorem first_effect :
    execute rawFirst first afterRaw = .done left middle ∧ Keeps afterRaw middle := execute_effect rawFirst first afterRaw raw_keeps.ready
  (other_effect.2.1.available _ raw_effect.2.2) (replacements afterRaw (raw_keeps.available _ capture_available) q)
private def secondRun := execute rawSecond second middle
private def right := value secondRun
private def common := secondRun.state
private theorem second_effect :
    execute rawSecond second middle = .done right common ∧ Keeps middle common := execute_effect rawSecond second middle first_effect.2.ready
  (first_effect.2.available _ other_effect.2.2)
  (replacements middle (first_effect.2.available _ (raw_keeps.available _ capture_available)) r)
private theorem kept : Keeps base common := raw_keeps.trans (first_effect.2.trans second_effect.2)
private theorem ready : Ready common := second_effect.2.ready
private theorem first_raw : build expression [.reference q,capture] common = .done rawFirst common :=
  InternedFreshOrdinaryReplay.build_replay expression _ base common rawFirst rawMiddle
    base_ready.semantic.1.normal.facts.coherent.valid raw_effect.1 (other_effect.2.1.trans (first_effect.2.trans second_effect.2)).growth
private theorem second_raw : build expression [.reference r,capture] common = .done rawSecond common :=
  InternedFreshOrdinaryReplay.build_replay expression _ rawMiddle common rawSecond afterRaw
    raw_effect.2.1.ready.semantic.1.normal.facts.coherent.valid other_effect.1 (first_effect.2.trans second_effect.2).growth
private theorem first_done : execute rawFirst first common = .done left common :=
  InternedFreshOrdinaryReplay.build_replay (encode (leaves rawFirst) [] rawFirst) ((leaves rawFirst).map (input first))
    afterRaw common left middle raw_keeps.ready.semantic.1.normal.facts.coherent.valid first_effect.1 second_effect.2.growth
private theorem second_done : execute rawSecond second common = .done right common :=
  InternedFreshOrdinaryReplay.build_replay (encode (leaves rawSecond) [] rawSecond) ((leaves rawSecond).map (input second))
    middle common right common first_effect.2.ready.semantic.1.normal.facts.coherent.valid second_effect.1 (grows_refl _)
private theorem first_inputs :
    InternedNestedProvenance.Values common [.reference q,capture] := inputs common (kept.available _ capture_available) q
  (reference_available common q (InternedFreshProbeKeys.sentinel_references_issued common.nodes 10).2)
private theorem second_inputs :
    InternedNestedProvenance.Values common [.reference r,capture] := inputs common (kept.available _ capture_available) r
  (reference_available common r (InternedFreshProbeKeys.sentinel_references_issued common.nodes 11).2)
private theorem paired : SourceCurrentReaderReplacementSlots.Paired Eq first second [.reference q,capture] [.reference r,capture] := by
  refine .cons ?_ (.cons ?_ .nil)
  · simp [SourceCurrentReaderReplacementSlots.Slot,first,second]
  · cases shape : capture with
    | reference name => have impossible := capture_closed; simp only [shape,Value.free] at impossible; cases impossible
    | empty | node | union | mu =>
        refine ⟨rfl,?_⟩
        intro name member
        have impossible := capture_closed
        rw [←shape,impossible] at member
        cases member
private theorem child (index : Nat) (a b x y : Value Nat Bool)
    (firstRaw : build (.var index) [.reference q,capture] common = .done a common)
    (secondRaw : build (.var index) [.reference r,capture] common = .done b common)
    (firstDone : execute a first common = .done x common) (secondDone : execute b second common = .done y common) :
    (x.referenceOf = .empty ↔ y.referenceOf = .empty) ∧ SourceCurrentOpenPreorderSimulation.Mutual Eq x y := by
  have same := (SourceCurrentReaderReplacementSlots.reference Eq (fun _ => rfl) common
    ready.semantic.1.normal.facts.coherent first second _ _ paired first_inputs index x y common common
    (by simp only [firstRaw,Outcome.bind,firstDone]) (by simp only [secondRaw,Outcome.bind,secondDone])).1
  subst y
  exact ⟨Iff.rfl,rfl,rfl⟩

private theorem node_local (reader : State Nat Bool) : Local reader Eq left right ∧ Local reader Eq right left := by
  apply SourceCurrentSourceDirectedCases.node expressions [capture] q r reader common Eq first second ready
    first_inputs second_inputs (replacements common (kept.available _ capture_available) q)
    (replacements common (kept.available _ capture_available) r) _ rawFirst rawSecond left right first_raw second_raw first_done second_done
  intro index symbol guard originals found childIndex expression selected _ a b firstRaw secondRaw x y firstDone secondDone
  have member := List.mem_of_getElem? found
  simp only [expressions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same | same | same
  · cases same
    have member := List.mem_of_getElem? selected
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact child 0 a b x y firstRaw secondRaw firstDone secondDone
    · exact child 1 a b x y firstRaw secondRaw firstDone secondDone
  · cases same
    cases List.mem_of_getElem? selected
  · cases same
    have member := List.mem_of_getElem? selected
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact child 0 a b x y firstRaw secondRaw firstDone secondDone
    · exact child 1 a b x y firstRaw secondRaw firstDone secondDone

private theorem union_made : run (makeUnion [capture,.empty,ordinary,capture]) common = (group,common) := by cbv
private theorem union_fragment : Below capture group := by
  apply SourceCurrentSourceDirectedCases.union_reconstruction [capture,.empty,ordinary,capture]
    [capture,.empty,ordinary,capture] (fun _ => none) common group group ready _ _ _ union_made
    (SourceCurrentStoredUnionObservations.closed group _ common group_closed) capture List.mem_cons_self
  · intro value member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact kept.available _ capture_available
    · exact empty_available common
    · exact kept.available _ ordinary_available
    · exact kept.available _ capture_available
  · intro name value impossible; cases impossible
  · exact .cons (SourceCurrentStoredUnionObservations.closed capture _ common capture_closed)
      (.cons (SourceCurrentStoredUnionObservations.closed .empty _ common rfl)
        (.cons (SourceCurrentStoredUnionObservations.closed ordinary _ common ordinary_closed)
          (.cons (SourceCurrentStoredUnionObservations.closed capture _ common capture_closed) .nil)))

/-- Actual source and stored calls validate the node and normalized union clauses with recursive captures. -/
theorem witness :
    build source [] empty = .done root base ∧ Ready common ∧
    (∃ entry body depth ordinary, capture = .mu entry body depth ordinary ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) ∧
    build expression [.reference q,capture] common = .done rawFirst common ∧
    build expression [.reference r,capture] common = .done rawSecond common ∧
    execute rawFirst first common = .done left common ∧ execute rawSecond second common = .done right common ∧
    (∀ reader, Local reader Eq left right ∧ Local reader Eq right left) ∧
    run (makeUnion [capture,.empty,ordinary,capture]) common = (group,common) ∧ Below capture group := by
  refine ⟨built_done,ready,?_,first_raw,second_raw,first_done,second_done,node_local,union_made,union_fragment⟩
  exact ⟨(fields capture).1,(fields capture).2.1,(fields capture).2.2.1,(fields capture).2.2.2,capture_shape,capture_used⟩

end MicroCFTA.SourceDirectedKernels

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceDirectedKernels.witness
#print MicroCFTA.SourceDirectedKernels.witness
#print axioms MicroCFTA.SourceDirectedKernels.witness
