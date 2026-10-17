import MicroCFTA.SourceCurrentStoredMuBinderChildLineage

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.MuBinderChildKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedStoredSubstitution (Environment)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentStoredMuBinderChildLineage
open InternedBinderProtocol (Reference)

private def leafSource : Syntax Nat Bool := .node [.mk 3 true []]
private def leafBuilt := build leafSource [] empty
private def value (outcome : Outcome Nat Bool (Value Nat Bool)) := match outcome with | .done result _ => result | .pending .. => .empty
private def leaf := value leafBuilt
private def base := leafBuilt.state
private def body : Syntax Nat Bool := .node [.mk 8 false [.var 0,.var 1]]
private def inputs (name : Reference) : List (Value Nat Bool) := [.reference name]
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
private def firstEnvironment : Environment Nat Bool := fun name => if name = .uninterned 0 then some leaf else none
private def secondEnvironment : Environment Nat Bool := fun name => if name = .uninterned 9 then some leaf else none

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



private theorem firstInputs : InternedNestedProvenance.Values base (inputs (.uninterned 0)) := by
  intro value member
  have same := List.mem_singleton.mp member
  subst value
  exact InternedNestedProvenance.ordinary_available _ _
private theorem firstReady : Ready firstHeap := sourceReady (.binder true body) _ base baseReady firstInputs _ firstHeap firstActual
private theorem secondInputs : InternedNestedProvenance.Values firstHeap (inputs (.uninterned 9)) := by
  intro value member
  have same := List.mem_singleton.mp member
  subst value
  exact InternedNestedProvenance.ordinary_available _ _
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

/-- Actual used-binder publications require paired unequal tails and derive both reserved-body calls. -/
theorem paired_reserved_bodies :
    firstBuilt = .done firstEvent.result firstEvent.after ∧
    secondBuilt = .done secondEvent.result secondEvent.after ∧
    secondEvent.before = firstEvent.after ∧
    InternedFreshOrdinaryDepthHeap.usesLocal firstEvent.depth firstEvent.ordinary = true ∧
    InternedFreshOrdinaryDepthHeap.usesLocal secondEvent.depth secondEvent.ordinary = true ∧
    firstEvent.environment ≠ secondEvent.environment ∧
    (¬ ∃ captures : List (Value Nat Bool),
      (.reference (.interned firstEvent.entry.identity) :: firstEvent.environment).tail = captures ∧
      (.reference (.interned secondEvent.entry.identity) :: secondEvent.environment).tail = captures) ∧
    Paired (bind (.interned firstEvent.entry.identity) leaf firstEnvironment)
      (bind (.interned secondEvent.entry.identity) leaf secondEnvironment)
      (.reference (.interned firstEvent.entry.identity) :: firstEvent.environment)
      (.reference (.interned secondEvent.entry.identity) :: secondEvent.environment) ∧
    ∃ rawFirst afterFirst rawSecond afterSecond,
      build body (.reference (.interned firstEvent.entry.identity) :: firstEvent.environment)
        firstEvent.allocated = .done rawFirst afterFirst ∧
      run (withoutSelfReference (.interned firstEvent.entry.identity) rawFirst) afterFirst =
        (firstEvent.body,firstEvent.afterBody) ∧
      build body (.reference (.interned secondEvent.entry.identity) :: secondEvent.environment)
        secondEvent.allocated = .done rawSecond afterSecond ∧
      run (withoutSelfReference (.interned secondEvent.entry.identity) rawSecond) afterSecond =
        (secondEvent.body,secondEvent.afterBody) ∧
      Grows afterFirst firstEvent.afterBody ∧ Grows afterSecond secondEvent.afterBody := by
  have paired : Paired firstEnvironment secondEnvironment firstEvent.environment secondEvent.environment := by
    exact .cons rfl (.nil)
  obtain ⟨_,_,extended,raw⟩ := publication_extend firstEvent secondEvent firstEnvironment secondEnvironment paired leaf
  refine ⟨by cbv,by cbv,by cbv,by cbv,by cbv,?_,?_,extended,raw⟩
  · intro same
    have heads := congrArg List.head? same
    cases heads
  · rintro ⟨captures,first,second⟩
    have tails : firstEvent.environment = secondEvent.environment := first.trans second.symm
    have heads := congrArg List.head? tails
    cases heads

end MicroCFTA.MuBinderChildKernels
