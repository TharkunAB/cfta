import MicroCFTA.SourceCurrentFiniteObservationExecution
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

/-!
# Ready readers still need the compared records

Both heaps come from actual source construction. They share the initial
capture records but allocate later records independently. Their identities
can overlap. An actual unfolding at the reader installs its own recursive
child. That child differs from an unavailable record at the execution heap.
This refutes Ready alone as a reader condition. It does not refute a law
that also retains the compared outputs and their observation support.
-/
namespace MicroCFTA.SourceCurrentReadyReaderObservationBoundary
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps Ordinary)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt)
open SourceCurrentReaderReplacementSlots (Paired)
open SourceCurrentFiniteObservationExecution (AlignedAt)
open SourceCurrentOpenObservations (ReferenceOrigin)

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def leaf (symbol : Nat) : Syntax Nat Bool := .node [.mk symbol false []]
private def expression : Syntax Nat Bool := .binder true (.node [.mk 2 false [.var 0,.var 1]])
private def capture (symbol : Nat) : Syntax Nat Bool := .node [.mk 5 false [leaf symbol]]
private def source : Syntax Nat Bool := .node [.mk 9 false [capture 0,capture 1]]
private def built := build source [] empty
private def root := value built
private def base := built.state
private def item (index : Nat) := (children root)[index]?.getD .empty
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private def firstName : Reference := .uninterned 0
private def secondName : Reference := .uninterned 1
private def first : Environment Nat Bool := fun name => if name = firstName then some (item 0) else none
private def second : Environment Nat Bool := fun name => if name = secondName then some (item 1) else none

private theorem actual : build source [] empty = .done root base := by
  obtain ⟨result,after,called⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete source
  change build source [] empty = .done (value (build source [] empty)) (build source [] empty).state
  rw [called]
  rfl
private theorem initial_ready : Ready base := SourceEqualityRequiredCache.constructed source root base actual
private theorem root_available : Available base root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro supplied member; cases member)).result root base actual
private theorem item_available (index : Nat) (bounded : index < 2) : Available base (item index) := by
  have bound : index < (children root).length := by simpa only [show (children root).length = 2 by cbv] using bounded
  have found : (children root)[index]? = some (item index) := by
    unfold item
    rw [List.getElem?_eq_getElem bound]
    rfl
  exact root_available.children _ (List.mem_of_getElem? found)
private theorem first_replacements : Replacements base first := by
  intro name output found
  unfold first at found
  split at found
  · cases found; exact item_available 0 (by omega)
  · cases found
private theorem second_replacements : Replacements base second := by
  intro name output found
  unfold second at found
  split at found
  · cases found; exact item_available 1 (by omega)
  · cases found

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
private def firstRawRun := build expression [.reference firstName] base
private def firstRaw := value firstRawRun
private def rawMiddle := firstRawRun.state
private theorem firstSourceEffect :
    build expression [.reference firstName] base = .done firstRaw rawMiddle ∧
      Keeps base rawMiddle ∧ Available rawMiddle firstRaw := source_effect expression [firstName] base initial_ready (by
  intro supplied member
  have same := List.mem_singleton.mp member
  subst supplied
  exact reference_available base _ (InternedFreshProbeKeys.sentinel_references_issued base.nodes 0).2)
private theorem first_source : build expression [.reference firstName] base = .done firstRaw rawMiddle := firstSourceEffect.1
private theorem firstSourceKeeps : Keeps base rawMiddle := firstSourceEffect.2.1
private def secondRawRun := build expression [.reference secondName] rawMiddle
private def secondRaw := value secondRawRun
private def afterRaw := secondRawRun.state
private theorem secondSourceEffect :
    build expression [.reference secondName] rawMiddle = .done secondRaw afterRaw ∧
      Keeps rawMiddle afterRaw ∧ Available afterRaw secondRaw := source_effect expression [secondName] rawMiddle firstSourceKeeps.ready (by
  intro supplied member
  have same := List.mem_singleton.mp member
  subst supplied
  exact reference_available rawMiddle _ (InternedFreshProbeKeys.sentinel_references_issued rawMiddle.nodes 1).2)
private theorem second_source : build expression [.reference secondName] rawMiddle = .done secondRaw afterRaw := secondSourceEffect.1
private theorem secondSourceKeeps : Keeps rawMiddle afterRaw := secondSourceEffect.2.1
private theorem rawKeeps : Keeps base afterRaw := firstSourceKeeps.trans secondSourceKeeps
private theorem first_available : Available afterRaw firstRaw := secondSourceKeeps.available _ firstSourceEffect.2.2
private theorem second_available : Available afterRaw secondRaw := secondSourceEffect.2.2

private theorem execute_effect (raw : Value Nat Bool) (environment : Environment Nat Bool)
    (before : State Nat Bool) (ready : Ready before) (available : Available before raw)
    (replacements : Replacements before environment) :
    execute raw environment before = .done (value (execute raw environment before)) (execute raw environment before).state ∧
      Keeps before (execute raw environment before).state ∧
      Available (execute raw environment before).state (value (execute raw environment before)) := by
  obtain ⟨result,after,done,kept,output,_⟩ := SourceCurrentStoredReconstruction.execute raw environment before ready available replacements
  rw [done]
  exact ⟨rfl,kept,output⟩

private def firstRun := execute firstRaw first afterRaw
private def firstResult := value firstRun
private def middle := firstRun.state
private theorem first_cold : execute firstRaw first afterRaw = .done firstResult middle :=
  (execute_effect firstRaw first afterRaw rawKeeps.ready first_available (fun name output found => rawKeeps.available _ (first_replacements name output found))).1
private theorem first_keeps : Keeps afterRaw middle :=
  (execute_effect firstRaw first afterRaw rawKeeps.ready first_available (fun name output found => rawKeeps.available _ (first_replacements name output found))).2.1
private theorem first_output : Available middle firstResult :=
  (execute_effect firstRaw first afterRaw rawKeeps.ready first_available (fun name output found => rawKeeps.available _ (first_replacements name output found))).2.2
private def secondRun := execute secondRaw second middle
private def secondResult := value secondRun
private def afterSecond := secondRun.state
private theorem second_effect :
    execute secondRaw second middle = .done secondResult afterSecond ∧
      Keeps middle afterSecond ∧ Available afterSecond secondResult := execute_effect secondRaw second middle first_keeps.ready
  (first_keeps.available _ second_available)
  (fun name output found => first_keeps.available _ (rawKeeps.available _ (second_replacements name output found)))
private theorem second_cold : execute secondRaw second middle = .done secondResult afterSecond := second_effect.1
private theorem second_keeps : Keeps middle afterSecond := second_effect.2.1
private theorem second_output : Available afterSecond secondResult := second_effect.2.2

private theorem unfold_effect (before : State Nat Bool) (ready : Ready before)
    (input : Value Nat Bool) (available : Available before input) :
    unfold input before = .done (value (unfold input before)) (unfold input before).state ∧
      Keeps before (unfold input before).state := by
  cases input with
  | empty | reference | node | union => exact ⟨rfl,SourceEqualityRequiredCache.pure_keeps before ready⟩
  | mu entry body depth ordinary =>
      have replacements : Replacements before (fun name => if name = .interned entry.identity then
          some (.mu entry body depth ordinary) else none) := by
        intro name output found
        dsimp only at found
        split at found
        · cases found; exact available
        · cases found
      have checked := execute_effect body _ before ready (available.children body List.mem_cons_self) replacements
      exact ⟨checked.1,checked.2.1⟩
private def firstUnfold := unfold firstResult afterSecond
private def firstLayer := value firstUnfold
private def common := firstUnfold.state
private theorem unfolded : unfold firstResult afterSecond = .done firstLayer common :=
  (unfold_effect afterSecond second_keeps.ready firstResult (second_keeps.available _ first_output)).1
private theorem unfolded_keeps : Keeps afterSecond common :=
  (unfold_effect afterSecond second_keeps.ready firstResult (second_keeps.available _ first_output)).2
private theorem all_keeps : Keeps base common := rawKeeps.trans ((first_keeps.trans second_keeps).trans unfolded_keeps)
private theorem common_ready : Ready common := unfolded_keeps.ready

private def marker : Reference := .uninterned 99
private def fillers : Nat → State Nat Bool → State Nat Bool
  | 0, before => before
  | count + 1, before => fillers count (build (leaf (100 + count)) [] before).state
private theorem fillers_keeps (count : Nat) (before : State Nat Bool) (ready : Ready before) :
    Keeps before (fillers count before) := by
  induction count generalizing before with
  | zero => exact SourceEqualityRequiredCache.pure_keeps before ready
  | succ count ih =>
      have kept := (source_effect (leaf (100 + count)) [] before ready (by intro supplied member; cases member)).2.1
      exact kept.trans (ih _ kept.ready)
private def foreignExpression : Syntax Nat Bool :=
  .binder true (.union [.var 1,.node [.mk 2 false [.var 0,capture 0]]])
private def foreignRun := build foreignExpression [.reference marker] (fillers 6 base)
private def foreignMu := value foreignRun
private def beforeReader := foreignRun.state
private theorem foreign_effect :
    build foreignExpression [.reference marker] (fillers 6 base) = .done foreignMu beforeReader ∧
      Keeps (fillers 6 base) beforeReader ∧ Available beforeReader foreignMu :=
  source_effect foreignExpression [marker] (fillers 6 base) (fillers_keeps 6 base initial_ready).ready (by
    intro supplied member
    have same := List.mem_singleton.mp member
    subst supplied
    exact reference_available _ _ (InternedFreshProbeKeys.sentinel_references_issued _ 99).2)
private def foreignUnfold := unfold foreignMu beforeReader
private def foreignLayer := value foreignUnfold
private def reader := foreignUnfold.state
private theorem foreign_unfolded : unfold foreignMu beforeReader = .done foreignLayer reader :=
  (unfold_effect beforeReader foreign_effect.2.1.ready foreignMu foreign_effect.2.2).1
private theorem foreign_keeps : Keeps beforeReader reader :=
  (unfold_effect beforeReader foreign_effect.2.1.ready foreignMu foreign_effect.2.2).2
private theorem reader_keeps : Keeps base reader :=
  (fillers_keeps 6 base initial_ready).trans (foreign_effect.2.1.trans foreign_keeps)
private theorem reader_ready : Ready reader := foreign_keeps.ready
private theorem foreign_available : Available reader foreignMu := foreign_keeps.available _ foreign_effect.2.2

private theorem first_shape : firstResult = .mu (fields firstResult).1 (fields firstResult).2.1
    (fields firstResult).2.2.1 (fields firstResult).2.2.2 := by cbv
private theorem second_shape : secondResult = .mu (fields secondResult).1 (fields secondResult).2.1
    (fields secondResult).2.2.1 (fields secondResult).2.2.2 := by cbv
private theorem foreign_shape : foreignMu = .mu (fields foreignMu).1 (fields foreignMu).2.1
    (fields foreignMu).2.2.1 (fields foreignMu).2.2.2 := by cbv
private def finished (outcome : Outcome Nat Bool (Value Nat Bool)) : Bool :=
  match outcome with | .done .. => true | .pending .. => false
private theorem finished_done (outcome : Outcome Nat Bool (Value Nat Bool)) (done : finished outcome = true) :
    outcome = .done (value outcome) outcome.state := by
  cases outcome with
  | done result after => rfl
  | pending key after => cases done
private def leftLayer := value (unfold firstResult reader)
private def rightLayer := value (unfold secondResult reader)
private theorem left_unfolded : unfold firstResult reader = .done leftLayer (unfold firstResult reader).state :=
  finished_done _ (by cbv)
private theorem right_unfolded : unfold secondResult reader = .done rightLayer (unfold secondResult reader).state :=
  finished_done _ (by cbv)
private def rowOf (supplied : Value Nat Bool) : EdgeValue Nat Bool :=
  (InternedEdgeResidency.nodeEdges supplied)[0]?.getD (.mk ⟨0,⟨0,[],false⟩⟩ [])
private def nodeFields : Value Nat Bool → Interned NodeKey × List (EdgeValue Nat Bool) × Nat × List Reference
  | .node entry rows level free => (entry,rows,level,free)
  | _ => (⟨0,.node []⟩,[],0,[])
private def capLeaf (index : Nat) := (children (item index))[0]?.getD .empty
private theorem left_node : leftLayer = .node (nodeFields leftLayer).1 [rowOf leftLayer]
    (nodeFields leftLayer).2.2.1 (nodeFields leftLayer).2.2.2 := by cbv
private theorem right_node : rightLayer = .node (nodeFields rightLayer).1 [rowOf rightLayer]
    (nodeFields rightLayer).2.2.1 (nodeFields rightLayer).2.2.2 := by cbv
private theorem left_children : (rowOf leftLayer).children = [foreignMu,item 0] := by cbv
private theorem right_children : (rowOf rightLayer).children = [secondResult,item 1] := by cbv
private theorem foreign_reference : ReferenceOrigin reader [foreignMu] marker := by
  have replay := InternedFreshOrdinaryStoredSubstitution.unfold_replay foreignMu beforeReader reader foreignLayer reader
    foreign_effect.2.1.ready.semantic.1.normal.facts.coherent.valid foreign_unfolded (grows_refl _)
  rw [foreign_shape] at replay
  have same := SourceCurrentOpenObservations.unfold 0 reader _ _ _ _ _ _ replay
  have present : ReferenceOrigin reader [foreignLayer] marker :=
    .step (.seed List.mem_cons_self) (by cbv; exact List.mem_cons_self)
  rw [foreign_shape]
  exact (same marker).mpr present
private theorem ordinary_reference (supplied : Value Nat Bool) (plain : Ordinary supplied) (name : Reference) :
    ¬ ReferenceOrigin reader [supplied] name := by
  have separate : ∀ reference, supplied ≠ .reference reference := by
    cases supplied <;> try cases plain <;> intro reference impossible <;> cases impossible
  have noNext : MergedFreshOrdinaryGraph.successors reader supplied = [] := by
    cases supplied <;> try cases plain <;> rfl
  intro present
  have later := (SourceCurrentOpenObservations.reference_expand reader supplied separate name).mp present
  rw [noNext] at later
  obtain ⟨_,member,_⟩ := (SourceCurrentOpenObservations.reference_seeds reader [] name).mp later
  cases member
private theorem second_no_reference : ¬ ReferenceOrigin reader [secondResult] marker := by
  have actual := right_unfolded
  rw [second_shape] at actual
  have same := SourceCurrentOpenObservations.unfold 0 reader _ _ _ _ _ _ actual
  rw [second_shape]
  exact fun present => ordinary_reference rightLayer (by rw [right_node]; trivial) marker ((same marker).mp present)
private theorem not_related : ¬ RelatedAt 1 reader firstResult secondResult := by
  intro related
  have left := left_unfolded
  have right := right_unfolded
  rw [first_shape] at left
  rw [second_shape] at right
  have one := SourceCurrentOpenObservations.unfold 1 reader _ _ _ _ _ _ left
  have two := SourceCurrentOpenObservations.unfold 1 reader _ _ _ _ _ _ right
  rw [← first_shape] at one
  rw [← second_shape] at two
  have observed := one.symm.trans (related.2.trans two)
  have origin : MergedFreshOrdinaryGraph.Origin reader [leftLayer] (rowOf leftLayer) := by
    refine ⟨_,.seed List.mem_cons_self,?_⟩
    rw [left_node]
    exact List.mem_cons_self
  obtain ⟨other,present,matched⟩ := observed.2.1 _ origin
  rw [right_node] at present
  have identical : other = rowOf rightLayer := List.mem_singleton.mp
    ((MergedFreshOrdinaryGraph.origin_node reader _ _ _ _ other).mp present)
  subst other
  have ordered := matched.2.2
  rw [left_children,right_children] at ordered
  cases ordered with
  | cons head tail => exact second_no_reference ((head marker).mp foreign_reference)
private theorem not_available : ¬ Available reader firstResult := by
  intro available
  have same : firstResult.referenceOf = foreignMu.referenceOf := by cbv
  have equal := InternedFreshProbeKeys.resident_reference_injective reader
    reader_ready.semantic.1.normal.facts.coherent firstResult foreignMu available.resident foreign_available.resident same
  have unequal : firstResult.free ≠ foreignMu.free := by cbv; intro impossible; cases impossible
  exact unequal (congrArg Value.free equal)
private theorem capture_related : RelatedAt 1 reader (item 0) (item 1) := by
  have firstNode : item 0 = .node (nodeFields (item 0)).1 [rowOf (item 0)]
      (nodeFields (item 0)).2.2.1 (nodeFields (item 0)).2.2.2 := by cbv
  have secondNode : item 1 = .node (nodeFields (item 1)).1 [rowOf (item 1)]
      (nodeFields (item 1)).2.2.1 (nodeFields (item 1)).2.2.2 := by cbv
  have children : SourceCurrentOpenObservations.RowMatch (fun a b => SourceCurrentOpenObservations.Same 0 reader [a] [b])
      (rowOf (item 0)) (rowOf (item 1)) := by
    refine ⟨by cbv,by cbv,?_⟩
    rw [show (rowOf (item 0)).children = [capLeaf 0] by cbv,
      show (rowOf (item 1)).children = [capLeaf 1] by cbv]
    exact .cons (fun name => iff_of_false (ordinary_reference _ (by cbv) name)
      (ordinary_reference _ (by cbv) name)) .nil
  constructor
  · have a : (item 0).referenceOf ≠ .empty := by cbv; intro impossible; cases impossible
    have b : (item 1).referenceOf ≠ .empty := by cbv; intro impossible; cases impossible
    exact iff_of_false a b
  · rw [firstNode,secondNode]
    apply SourceCurrentOpenObservationConstructors.node 0
    · intro row member
      have equal := List.mem_singleton.mp member
      subst row
      exact ⟨_,List.mem_cons_self,children⟩
    · intro row member
      have equal := List.mem_singleton.mp member
      subst row
      refine ⟨_,List.mem_cons_self,by cbv,by cbv,?_⟩
      rw [show (rowOf (item 1)).children = [capLeaf 1] by cbv,
        show (rowOf (item 0)).children = [capLeaf 0] by cbv]
      exact .cons (fun name => iff_of_false (ordinary_reference _ (by cbv) name)
        (ordinary_reference _ (by cbv) name)) .nil
private theorem first_raw : build expression [.reference firstName] common = .done firstRaw common :=
  InternedFreshOrdinaryReplay.build_replay expression _ base common firstRaw rawMiddle
    initial_ready.semantic.1.normal.facts.coherent.valid first_source
    (secondSourceKeeps.trans ((first_keeps.trans second_keeps).trans unfolded_keeps)).growth
private theorem second_raw : build expression [.reference secondName] common = .done secondRaw common :=
  InternedFreshOrdinaryReplay.build_replay expression _ rawMiddle common secondRaw afterRaw
    firstSourceKeeps.ready.semantic.1.normal.facts.coherent.valid second_source
    ((first_keeps.trans second_keeps).trans unfolded_keeps).growth
private theorem first_done : execute firstRaw first common = .done firstResult common :=
  InternedFreshOrdinaryReplay.build_replay (encode (leaves firstRaw) [] firstRaw) ((leaves firstRaw).map (input first))
    afterRaw common firstResult middle rawKeeps.ready.semantic.1.normal.facts.coherent.valid first_cold
    (second_keeps.trans unfolded_keeps).growth
private theorem second_done : execute secondRaw second common = .done secondResult common :=
  InternedFreshOrdinaryReplay.build_replay (encode (leaves secondRaw) [] secondRaw) ((leaves secondRaw).map (input second))
    middle common secondResult afterSecond first_keeps.ready.semantic.1.normal.facts.coherent.valid second_cold unfolded_keeps.growth

private theorem first_inputs : InternedNestedProvenance.Values common [.reference firstName] := by
  intro supplied member
  have same := List.mem_singleton.mp member
  subst supplied
  exact reference_available common _ (InternedFreshProbeKeys.sentinel_references_issued common.nodes 0).2
private theorem second_inputs : InternedNestedProvenance.Values common [.reference secondName] := by
  intro supplied member
  have same := List.mem_singleton.mp member
  subst supplied
  exact reference_available common _ (InternedFreshProbeKeys.sentinel_references_issued common.nodes 1).2
private theorem paired_inputs : Paired (RelatedAt 1 reader) first second [.reference firstName] [.reference secondName] := by
  refine .cons ?_ .nil
  change RelatedAt 1 reader ((first firstName).getD (.reference firstName)) ((second secondName).getD (.reference secondName))
  simpa only [first,second,ite_true,Option.getD_some] using capture_related

/-- Ready and available inputs do not suffice when a separate reader lacks a compared output. -/
private theorem checked_witness :
    ∃ (execution view : State Nat Bool) (term : Syntax Nat Bool)
      (firstMap secondMap : Environment Nat Bool) (firstInputs secondInputs : List (Value Nat Bool))
      (rawFirst rawSecond left right : Value Nat Bool),
      Ready execution ∧ Ready view ∧
      term = .binder true (.node [.mk 2 false [.var 0,.var 1]]) ∧
      InternedNestedConstruction.Scoped 1 term ∧ ¬ InternedNestedConstruction.Scoped 0 term ∧
      Paired (RelatedAt 1 view) firstMap secondMap firstInputs secondInputs ∧
      InternedNestedProvenance.Values execution firstInputs ∧ InternedNestedProvenance.Values execution secondInputs ∧
      Replacements execution firstMap ∧ Replacements execution secondMap ∧
      InternedNestedProvenance.Values view firstInputs ∧ InternedNestedProvenance.Values view secondInputs ∧
      Replacements view firstMap ∧ Replacements view secondMap ∧
      build term firstInputs execution = .done rawFirst execution ∧
      build term secondInputs execution = .done rawSecond execution ∧
      execute rawFirst firstMap execution = .done left execution ∧
      execute rawSecond secondMap execution = .done right execution ∧
      (∃ (entry : Interned NodeKey) (body depth ordinary : Value Nat Bool),
        left = .mu entry body depth ordinary ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) ∧
      (∃ (entry : Interned NodeKey) (body depth ordinary : Value Nat Bool),
        right = .mu entry body depth ordinary ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) ∧
      ¬ Available view left ∧ ¬ RelatedAt 1 view left right ∧ ¬ AlignedAt 1 view execution term := by
  refine ⟨common,reader,expression,first,second,[.reference firstName],[.reference secondName],
    firstRaw,secondRaw,firstResult,secondResult,common_ready,reader_ready,rfl,?_,?_,paired_inputs,first_inputs,second_inputs,
    (fun name output found => all_keeps.available _ (first_replacements name output found)),
    (fun name output found => all_keeps.available _ (second_replacements name output found)),?_,?_,
    (fun name output found => reader_keeps.available _ (first_replacements name output found)),
    (fun name output found => reader_keeps.available _ (second_replacements name output found)),
    first_raw,second_raw,first_done,second_done,
    ⟨(fields firstResult).1,(fields firstResult).2.1,(fields firstResult).2.2.1,(fields firstResult).2.2.2,first_shape,by cbv⟩,
    ⟨(fields secondResult).1,(fields secondResult).2.1,(fields secondResult).2.2.1,(fields secondResult).2.2.2,second_shape,by cbv⟩,
    not_available,not_related,?_⟩
  · simp [expression,InternedNestedConstruction.Scoped,InternedNestedConstruction.EdgesScoped,InternedNestedConstruction.ManyScoped]
  · simp [expression,InternedNestedConstruction.Scoped,InternedNestedConstruction.EdgesScoped,InternedNestedConstruction.ManyScoped]
  · intro supplied member
    have same := List.mem_singleton.mp member
    subst supplied
    exact reference_available reader _ (InternedFreshProbeKeys.sentinel_references_issued reader.nodes 0).2
  · intro supplied member
    have same := List.mem_singleton.mp member
    subst supplied
    exact reference_available reader _ (InternedFreshProbeKeys.sentinel_references_issued reader.nodes 1).2
  · intro aligned
    exact not_related (aligned _ _ first second paired_inputs common_ready first_inputs second_inputs
      (fun name output found => all_keeps.available _ (first_replacements name output found))
      (fun name output found => all_keeps.available _ (second_replacements name output found))
      firstRaw secondRaw first_raw second_raw firstResult secondResult first_done second_done)

/-- A source-built Ready reader can select a different same-identity Mu when an output is unavailable. -/
theorem arbitrary_reader :
    ∃ (execution view : State Nat Bool) (term : Syntax Nat Bool)
      (firstMap secondMap : Environment Nat Bool) (firstInputs secondInputs : List (Value Nat Bool))
      (rawFirst rawSecond left right : Value Nat Bool),
      Ready execution ∧ Ready view ∧
      term = .binder true (.node [.mk 2 false [.var 0,.var 1]]) ∧
      InternedNestedConstruction.Scoped 1 term ∧ ¬ InternedNestedConstruction.Scoped 0 term ∧
      Paired (RelatedAt 1 view) firstMap secondMap firstInputs secondInputs ∧
      InternedNestedProvenance.Values execution firstInputs ∧ InternedNestedProvenance.Values execution secondInputs ∧
      Replacements execution firstMap ∧ Replacements execution secondMap ∧
      InternedNestedProvenance.Values view firstInputs ∧ InternedNestedProvenance.Values view secondInputs ∧
      Replacements view firstMap ∧ Replacements view secondMap ∧
      build term firstInputs execution = .done rawFirst execution ∧
      build term secondInputs execution = .done rawSecond execution ∧
      execute rawFirst firstMap execution = .done left execution ∧
      execute rawSecond secondMap execution = .done right execution ∧
      (∃ (entry : Interned NodeKey) (body depth ordinary : Value Nat Bool),
        left = .mu entry body depth ordinary ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) ∧
      (∃ (entry : Interned NodeKey) (body depth ordinary : Value Nat Bool),
        right = .mu entry body depth ordinary ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) ∧
      ¬ Available view left ∧ ¬ RelatedAt 1 view left right ∧ ¬ AlignedAt 1 view execution term := checked_witness

end MicroCFTA.SourceCurrentReadyReaderObservationBoundary
