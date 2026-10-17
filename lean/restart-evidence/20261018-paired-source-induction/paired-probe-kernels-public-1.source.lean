import MicroCFTA.SourceCurrentStoredProbeCompatibility

set_option linter.all true
set_option maxHeartbeats 2000000
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.PairedProbeKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext InternedFreshOrdinaryFacts
open InternedStoredSubstitution (Environment)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentStoredMuBinderChildLineage (Paired Slot)
open SourceCurrentStoredProbeCompatibility
open InternedBinderProtocol (Reference)

private def leafSource : Syntax Nat Bool := .node [.mk 3 true []]
private def leafBuilt := build leafSource [] empty
private def value (outcome : Outcome Nat Bool (Value Nat Bool)) := match outcome with | .done result _ => result | .pending .. => .empty
private def leaf := value leafBuilt
private def base := leafBuilt.state
private def body : Syntax Nat Bool := .node [.mk 8 false [.var 0,.var 1]]
private def ignoredName : Reference :=
  .uninterned (ordinaryLevel (value (callback body [.reference (.uninterned 0)] .depth base)))
private def inputs (name : Reference) : List (Value Nat Bool) := [.reference name,.reference ignoredName]
private def depthCall (name : Reference) (before : State Nat Bool) := callback body (inputs name) .depth before
private def ordinaryCall (name : Reference) (before : State Nat Bool) :=
  callback body (inputs name) (.uninterned (ordinaryLevel (value (depthCall name before)))) (depthCall name before).state
private def key (name : Reference) (before : State Nat Bool) :=
  muKey (value (depthCall name before)) (value (ordinaryCall name before))
private def entry (name : Reference) (before : State Nat Bool) := Cache.intern (ordinaryCall name before).state.nodes (key name before)
private def allocated (name : Reference) (before : State Nat Bool) :=
  {(ordinaryCall name before).state with nodes := (entry name before).2}
private def bodyCall (name : Reference) (before : State Nat Bool) :=
  callback body (inputs name) (.interned (entry name before).1.identity) (allocated name before)
private def firstBuilt := build (.binder true body) (inputs (.uninterned 0)) base
private def firstHeap := firstBuilt.state
private def secondBuilt := build (.binder true body) (inputs (.uninterned 9)) firstHeap
private def common := secondBuilt.state
private def environment : Environment Nat Bool := fun _ => some leaf

private theorem leafActual : leafBuilt = .done leaf base := by cbv
private theorem firstActual : firstBuilt = .done (value firstBuilt) firstHeap := by cbv
private theorem secondActual : secondBuilt = .done (value secondBuilt) common := by cbv
private theorem baseReady : Ready base := SourceEqualityRequiredCache.constructed leafSource leaf base leafActual

private theorem sourceReady (source : Syntax Nat Bool) (environment : List (Value Nat Bool))
    (before : State Nat Bool) (ready : Ready before)
    (available : InternedNestedProvenance.Values before environment)
    (value : Value Nat Bool) (after : State Nat Bool)
    (actual : build source environment before = .done value after) : Ready after := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic environment available
  refine ⟨?_,
    InternedFreshOrdinaryCoverage.build_covered source environment before
      ready.semantic.1.normal.facts.coherent.valid ready.covered value after actual,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source source environment before ready.semantic available
  · simpa only [actual,Outcome.state] using (InternedOpenDepthExecution.build_depth source environment before context ready.semantic.2 ready.depth).heap



private theorem inputAvailable (state : State Nat Bool) (level : Nat) :
    InternedNestedProvenance.Values state (inputs (.uninterned level)) := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | later
  · exact InternedNestedProvenance.ordinary_available _ _
  · have same := List.mem_singleton.mp later
    subst selected
    exact InternedNestedProvenance.ordinary_available _ _
private theorem firstInputs : InternedNestedProvenance.Values base (inputs (.uninterned 0)) := inputAvailable base 0
private theorem firstReady : Ready firstHeap := sourceReady (.binder true body) _ base baseReady firstInputs _ firstHeap firstActual
private theorem secondInputs : InternedNestedProvenance.Values firstHeap (inputs (.uninterned 9)) := inputAvailable firstHeap 9
private theorem commonReady : Ready common := sourceReady (.binder true body) _ firstHeap firstReady secondInputs _ common secondActual

private def firstEvent : Publication (Symbol := Nat) (Guard := Bool) where
  smart := true
  expression := body
  environment := inputs (.uninterned 0)
  before := base
  afterDepth := (depthCall (.uninterned 0) base).state
  cut := (ordinaryCall (.uninterned 0) base).state
  afterBody := (bodyCall (.uninterned 0) base).state
  depth := value (depthCall (.uninterned 0) base)
  ordinary := value (ordinaryCall (.uninterned 0) base)
  body := value (bodyCall (.uninterned 0) base)
  context := ⟨SourceRecursiveIntersectionSemanticHeap.context base baseReady.semantic _ firstInputs,baseReady.semantic.2⟩
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv

private def secondEvent : Publication (Symbol := Nat) (Guard := Bool) where
  smart := true
  expression := body
  environment := inputs (.uninterned 9)
  before := firstHeap
  afterDepth := (depthCall (.uninterned 9) firstHeap).state
  cut := (ordinaryCall (.uninterned 9) firstHeap).state
  afterBody := (bodyCall (.uninterned 9) firstHeap).state
  depth := value (depthCall (.uninterned 9) firstHeap)
  ordinary := value (ordinaryCall (.uninterned 9) firstHeap)
  body := value (bodyCall (.uninterned 9) firstHeap)
  context := ⟨SourceRecursiveIntersectionSemanticHeap.context firstHeap firstReady.semantic _ secondInputs,firstReady.semantic.2⟩
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv


private def descriptors : List (Sum (Value Nat Bool) (Reference × Reference)) :=
  [.inr (.uninterned 0,.uninterned 9),.inr (ignoredName,ignoredName)]
private def firstMarker : Reference := .uninterned (ordinaryLevel firstEvent.depth)
private def secondMarker : Reference := .uninterned (ordinaryLevel secondEvent.depth)
private def firstMap := SourceCurrentStoredMuBinderChildLineage.bind firstMarker (.empty : Value Nat Bool) environment
private def secondMap := SourceCurrentStoredMuBinderChildLineage.bind secondMarker (.empty : Value Nat Bool) environment

/-- Actual ordinary probes extend live compatibility although an unused capture aliases only the first marker. -/
theorem ordinary_ignores_capture_alias :
    firstBuilt = .done firstEvent.result firstEvent.after ∧
    secondBuilt = .done secondEvent.result secondEvent.after ∧
    secondEvent.before = firstEvent.after ∧
    firstMarker = ignoredName ∧ secondMarker ≠ ignoredName ∧
    (.reference ignoredName : Value Nat Bool) ∈ firstEvent.environment ∧
    ¬ Paired firstMap secondMap firstEvent.environment secondEvent.environment ∧
    Compatible body (.inr (.inl ()) :: descriptors.map InternedFreshOrdinaryLiveInputs.liftInput)
      (Sum.elim (fun _ => firstMarker) Prod.fst) (Sum.elim (fun _ => secondMarker) Prod.snd)
      firstMap secondMap := by
  have compatible : Compatible (.binder true body) descriptors Prod.fst Prod.snd environment environment :=
    ⟨fun _ _ => rfl,fun _ _ => rfl⟩
  have extended := publication_ordinary firstEvent secondEvent rfl descriptors Prod.fst Prod.snd
    rfl rfl environment environment compatible (.empty : Value Nat Bool)
  refine ⟨by cbv,by cbv,by cbv,by cbv,by cbv; decide,by simp [firstEvent,inputs],?_,extended⟩
  have firstName : firstMarker = ignoredName := by cbv
  have secondName : secondMarker ≠ ignoredName := by cbv; decide
  have firstValue : firstMap ignoredName = some (.empty : Value Nat Bool) := by
    change (if ignoredName = firstMarker then some .empty else environment ignoredName) = some .empty
    exact ite_eq_left firstName.symm
  have secondValue : secondMap ignoredName = some leaf := by
    change (if ignoredName = secondMarker then some .empty else environment ignoredName) = some leaf
    rw [ite_eq_right (Ne.symm secondName)]
    rfl
  intro paired
  cases paired with
  | cons _ rest =>
      cases rest with
      | cons captured _ =>
          change (firstMap ignoredName).getD _ = (secondMap ignoredName).getD _ at captured
          rw [firstValue,secondValue] at captured
          simp only [Option.getD_some] at captured
          cbv at captured
          cases captured

private def depthDescriptors : List (Sum (Value Nat Bool) (Reference × Reference)) :=
  [.inr (.depth,.uninterned 9),.inr (ignoredName,ignoredName)]
private def depthMap := SourceCurrentStoredMuBinderChildLineage.bind .depth (.empty : Value Nat Bool) environment

/-- A live one-sided Depth alias breaks compatibility despite paired initial inputs and actual Depth execution. -/
theorem depth_live_alias_boundary :
    Paired environment environment (inputs .depth) (inputs (.uninterned 9)) ∧
    Compatible (.binder true body) depthDescriptors Prod.fst Prod.snd environment environment ∧
    depthCall .depth base = .done (value (depthCall .depth base)) (depthCall .depth base).state ∧
    (build (.var 1) (.reference (.depth : Reference) :: inputs .depth) base).bind
      (fun result state => execute result depthMap state) = .done .empty base ∧
    (build (.var 1) (.reference (.depth : Reference) :: inputs (.uninterned 9)) base).bind
      (fun result state => execute result depthMap state) = .done leaf base ∧
    ¬ Compatible body (.inr (.inl ()) :: depthDescriptors.map InternedFreshOrdinaryLiveInputs.liftInput)
      (Sum.elim (fun _ => .depth) Prod.fst) (Sum.elim (fun _ => .depth) Prod.snd) depthMap depthMap := by
  refine ⟨.cons rfl (.cons rfl .nil),⟨fun _ _ => rfl,fun _ _ => rfl⟩,by cbv,by cbv,by cbv,?_⟩
  intro compatible
  have member : Sum.inr (Sum.inr (Reference.depth,Reference.uninterned 9)) ∈
      SourceCurrentNativeNormalizationInputs.support body
        (.inr (.inl ()) :: depthDescriptors.map InternedFreshOrdinaryLiveInputs.liftInput) := by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self
  have impossible := compatible.2 (.inr (.depth,.uninterned 9)) member
  change (.empty : Value Nat Bool) = leaf at impossible
  cbv at impossible
  cases impossible

end MicroCFTA.PairedProbeKernels

#check @MicroCFTA.PairedProbeKernels.ordinary_ignores_capture_alias
#print axioms MicroCFTA.PairedProbeKernels.ordinary_ignores_capture_alias

#check @MicroCFTA.PairedProbeKernels.depth_live_alias_boundary
#print axioms MicroCFTA.PairedProbeKernels.depth_live_alias_boundary
