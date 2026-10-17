import MicroCFTA.SourceCurrentStoredLiveSourceLineage

set_option linter.all true
set_option maxHeartbeats 2000000
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.LiveSourceKernels
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
private def environment : Environment Nat Bool := fun name => if name = ignoredName then some .empty else some leaf

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
private def firstMap := SourceCurrentStoredMuBinderChildLineage.bind firstMarker leaf environment
private def secondMap := SourceCurrentStoredMuBinderChildLineage.bind secondMarker leaf environment


private def localInputs := Sum.inr (Sum.inl ()) :: descriptors.map InternedFreshOrdinaryLiveInputs.liftInput
private def firstNames : Sum Unit (Reference × Reference) → Reference := Sum.elim (fun _ => firstMarker) Prod.fst
private def secondNames : Sum Unit (Reference × Reference) → Reference := Sum.elim (fun _ => secondMarker) Prod.snd
private def leftInputs := localInputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)
private def rightInputs := localInputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)
private def expression : Syntax Nat Bool := .node [.mk 8 false [.var 0,.var 1],.mk 6 true [.empty,.var 2]]
private def firstRaw := build expression leftInputs common
private def rawHeap := firstRaw.state
private def secondRaw := build expression rightInputs rawHeap
private def entryHeap := secondRaw.state
private def expected := execute (value firstRaw) firstMap entryHeap

private theorem allOrdinary (state : State Nat Bool) (a b c : Nat) :
    InternedNestedProvenance.Values state [.reference (.uninterned a),.reference (.uninterned b),.reference (.uninterned c)] := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | rest
  · exact InternedNestedProvenance.ordinary_available _ _
  rcases List.mem_cons.mp rest with rfl | rest
  · exact InternedNestedProvenance.ordinary_available _ _
  have same := List.mem_singleton.mp rest
  subst selected
  exact InternedNestedProvenance.ordinary_available _ _
private theorem leftAvailable (state : State Nat Bool) : InternedNestedProvenance.Values state leftInputs :=
  allOrdinary state _ _ _
private theorem rightAvailable (state : State Nat Bool) : InternedNestedProvenance.Values state rightInputs :=
  allOrdinary state _ _ _
private theorem rawFirstDone : firstRaw = .done (value firstRaw) rawHeap := by cbv
private theorem rawReady : Ready rawHeap := sourceReady expression leftInputs common commonReady
  (leftAvailable common) _ rawHeap rawFirstDone
private theorem rawSecondDone : secondRaw = .done (value secondRaw) entryHeap := by cbv
private theorem entryReady : Ready entryHeap := sourceReady expression rightInputs rawHeap rawReady
  (rightAvailable rawHeap) _ entryHeap rawSecondDone

private theorem laterAvailable (source : Syntax Nat Bool) (captured : List (Value Nat Bool))
    (before : State Nat Bool) (ready : Ready before) (inputsAvailable : InternedNestedProvenance.Values before captured)
    (result : Value Nat Bool) (after : State Nat Bool) (actual : build source captured before = .done result after)
    (selected : Value Nat Bool) (known : Available before selected) : Available after selected := by
  simpa only [actual,Outcome.state] using
    (InternedFreshOrdinaryFacts.build_verified source captured before ready.semantic.1.normal.facts inputsAvailable).available selected known

private theorem leafAvailable : Available entryHeap leaf := by
  have start := (InternedFreshOrdinaryFacts.closed_verified leafSource).result leaf base leafActual
  have first := laterAvailable (.binder true body) _ base baseReady firstInputs _ firstHeap firstActual leaf start
  have second := laterAvailable (.binder true body) _ firstHeap firstReady secondInputs _ common secondActual leaf first
  have raw := laterAvailable expression leftInputs common commonReady (leftAvailable common) _ rawHeap rawFirstDone leaf second
  exact laterAvailable expression rightInputs rawHeap rawReady (rightAvailable rawHeap) _ entryHeap rawSecondDone leaf raw

private theorem replacements (name : Reference) : InternedStoredSubstitution.Replacements entryHeap
    (SourceCurrentStoredMuBinderChildLineage.bind name leaf environment) := by
  intro queried selected found
  dsimp [SourceCurrentStoredMuBinderChildLineage.bind,environment] at found
  split at found
  · cases found
    exact leafAvailable
  · split at found
    · cases found
      exact InternedProbeProvenance.empty_available _
    · cases found
      exact leafAvailable

private theorem compatible : Compatible expression localInputs firstNames secondNames firstMap secondMap := by
  have sourceSupport : SourceCurrentNativeNormalizationInputs.support expression localInputs =
      [.inr (.inl ()),.inr (.inr (.uninterned 0,.uninterned 9))] := by cbv
  constructor
  · intro name member
    rw [sourceSupport] at member
    simp only [List.mem_cons,Sum.inl_ne_inr,List.not_mem_nil,false_or] at member
  · intro atom member
    rw [sourceSupport] at member
    have cases : atom = .inl () ∨ atom = .inr (.uninterned 0,.uninterned 9) := by
      simpa only [List.mem_cons,Sum.inr.injEq,List.not_mem_nil,or_false] using member
    rcases cases with rfl | rfl <;> rfl

private theorem sourceAligned : SourceCurrentStoredLiveSourceLineage.Aligned expression := by
  apply SourceCurrentStoredLiveSourceLineage.ordinary
  intro child strict
  obtain ⟨symbol,guard,originals,present,member,_⟩ := strict
  have row : EdgeSyntax.mk symbol guard originals = .mk 8 false [.var 0,.var 1] ∨
      EdgeSyntax.mk symbol guard originals = .mk 6 true [.empty,.var 2] := by
    simpa only [List.mem_cons,List.mem_singleton] using present
  rcases row with row | row
  · cases row
    have cases : child = .var 0 ∨ child = .var 1 := by simpa only [List.mem_cons,List.mem_singleton] using member
    rcases cases with rfl | rfl
    · exact SourceCurrentStoredLiveSourceLineage.reference 0
    · exact SourceCurrentStoredLiveSourceLineage.reference 1
  · cases row
    have cases : child = .empty ∨ child = .var 2 := by simpa only [List.mem_cons,List.mem_singleton] using member
    rcases cases with rfl | rfl
    · exact SourceCurrentStoredLiveSourceLineage.empty
    · exact SourceCurrentStoredLiveSourceLineage.reference 2

/-- A live row reconstructs nonempty while a dead row contains an incompatible ordinary-marker alias. -/
theorem initial_nonempty_with_dead_alias :
    ¬ Compatible (.var 2) localInputs firstNames secondNames firstMap secondMap ∧
    ∃ left middle right reader,
      execute (value firstRaw) firstMap entryHeap = .done left middle ∧
      execute (value secondRaw) secondMap middle = .done right reader ∧
      SourceEqualityRequiredCache.Keeps entryHeap middle ∧ SourceEqualityRequiredCache.Keeps middle reader ∧
      Available reader left ∧ Available reader right ∧
      Nonempty (SourceCurrentNativeMuPublication.History entryHeap middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle reader) ∧
      SourceCurrentOpenObservationSurvival.Related left right ∧ left.referenceOf ≠ .empty := by
  have rawGrowth : Grows rawHeap entryHeap := by
    simpa only [rawSecondDone,Outcome.state] using
      (InternedFreshOrdinaryGrowth.build_correct expression rightInputs rawHeap rawReady.semantic.1.normal.facts.coherent.valid).2
  have firstContext := SourceRecursiveIntersectionSemanticHeap.context common commonReady.semantic leftInputs (leftAvailable common)
  have secondContext := SourceRecursiveIntersectionSemanticHeap.context rawHeap rawReady.semantic rightInputs (rightAvailable rawHeap)
  obtain ⟨left,middle,right,reader,done,secondDone,_,_,firstKept,secondKept,leftKnown,rightKnown,firstHistory,secondHistory,related⟩ :=
    SourceCurrentStoredLiveSourceLineage.complete expression sourceAligned localInputs firstNames secondNames firstMap secondMap compatible
      common rawHeap rawHeap entryHeap entryHeap firstContext secondContext _ _ rawFirstDone rawSecondDone
      rawGrowth (grows_refl _) entryReady (leftAvailable entryHeap) (rightAvailable entryHeap)
      (replacements firstMarker) (replacements secondMarker)
  have expectedDone : expected = .done (value expected) expected.state := by cbv
  have same : left = value expected := (Outcome.done.inj (done.symm.trans expectedDone)).1
  refine ⟨?_,left,middle,right,reader,done,secondDone,firstKept,secondKept,leftKnown,rightKnown,firstHistory,secondHistory,related,?_⟩
  · intro supported
    have member : Sum.inr (Sum.inr (ignoredName,ignoredName)) ∈
        SourceCurrentNativeNormalizationInputs.support (.var 2) localInputs := by
      change Sum.inr (Sum.inr (ignoredName,ignoredName)) ∈ [.inr (.inr (ignoredName,ignoredName))]
      exact List.mem_cons_self
    have impossible := supported.2 (.inr (ignoredName,ignoredName)) member
    cbv at impossible
    cases impossible
  · rw [same]
    cbv
    intro impossible
    cases impossible

end MicroCFTA.LiveSourceKernels
