import MicroCFTA.SourceCurrentScopedProfileInputs

set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.ScopedInputKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext InternedFreshOrdinaryFacts
open InternedStoredSubstitution (Environment)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentStoredMuBinderChildLineage (Paired Slot)
open SourceCurrentScopedProfileInputs
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
private def firstAssignment : Reference → InternedRootProfile.Profile := fun _ => some []
private def secondAssignment : Reference → InternedRootProfile.Profile :=
  fun name => if name = ignoredName then none else some []
private def localProfile : InternedRootProfile.Profile := some [.uninterned 99]
private def firstMarker : Reference := .uninterned (ordinaryLevel firstEvent.depth)
private def secondMarker : Reference := .uninterned (ordinaryLevel secondEvent.depth)
private def sourceRows : List (EdgeSyntax Nat Bool) := [.mk 8 false [.var 0],.mk 6 true [.empty,.var 1]]
private def sourceNode : Syntax Nat Bool := .node sourceRows
private def sourceCall := build sourceNode (inputs (.uninterned 0)) base

private theorem support_only : SourceCurrentNativeNormalizationInputs.support (.binder true body) descriptors =
    [.inr (.uninterned 0,.uninterned 9)] := by cbv
private theorem compatible : Compatible (.binder true body) descriptors Prod.fst Prod.snd
    firstAssignment secondAssignment := by
  constructor
  · intro name member
    rw [support_only] at member
    cases List.mem_singleton.mp member
  · intro atom member
    rw [support_only] at member
    obtain rfl := Sum.inr.inj (List.mem_singleton.mp member)
    cbv
private theorem aliases : SourceCurrentUsedBinderAliasTransport.Aliases (.binder true body) descriptors Prod.fst Prod.snd := by
  intro first firstLive second secondLive
  have firstCases : first = .inl .depth ∨ first = .inr (.uninterned 0,.uninterned 9) := by
    simpa only [SourceCurrentUsedBinderAliasTransport.Scope,support_only,List.mem_cons,List.not_mem_nil,or_false] using firstLive
  have secondCases : second = .inl .depth ∨ second = .inr (.uninterned 0,.uninterned 9) := by
    simpa only [SourceCurrentUsedBinderAliasTransport.Scope,support_only,List.mem_cons,List.not_mem_nil,or_false] using secondLive
  rcases firstCases with rfl | rfl <;> rcases secondCases with rfl | rfl <;> simp
private theorem ordinary_extended : Compatible body
    (.inr (.inl ()) :: descriptors.map InternedFreshOrdinaryLiveInputs.liftInput)
    (Sum.elim (fun _ => firstMarker) Prod.fst) (Sum.elim (fun _ => secondMarker) Prod.snd)
    (SourceCurrentStoredMuProfileContract.shadow firstMarker localProfile firstAssignment)
    (SourceCurrentStoredMuProfileContract.shadow secondMarker localProfile secondAssignment) := by
  exact SourceCurrentScopedProfileInputs.publication_ordinary firstEvent secondEvent rfl descriptors Prod.fst Prod.snd
    (by rfl) (by rfl) firstAssignment secondAssignment compatible localProfile
private theorem depth_extended : Compatible body
    (.inr (.inl ()) :: descriptors.map InternedFreshOrdinaryLiveInputs.liftInput)
    (Sum.elim (fun _ => .depth) Prod.fst) (Sum.elim (fun _ => .depth) Prod.snd)
    (SourceCurrentStoredMuProfileContract.shadow .depth localProfile firstAssignment)
    (SourceCurrentStoredMuProfileContract.shadow .depth localProfile secondAssignment) :=
  SourceCurrentScopedProfileInputs.extend_depth body descriptors Prod.fst Prod.snd firstAssignment secondAssignment
    compatible aliases localProfile
private theorem event_extended : Compatible firstEvent.expression
    (.inr (.inl ()) :: descriptors.map InternedFreshOrdinaryLiveInputs.liftInput)
    (Sum.elim (fun _ => .interned firstEvent.entry.identity) Prod.fst)
    (Sum.elim (fun _ => .uninterned (ordinaryLevel firstEvent.depth)) Prod.fst)
    (SourceCurrentStoredMuProfileContract.shadow (.interned firstEvent.entry.identity) localProfile firstAssignment)
    (SourceCurrentStoredMuProfileContract.shadow (.uninterned (ordinaryLevel firstEvent.depth)) localProfile firstAssignment) :=
  SourceCurrentScopedProfileInputs.publication firstEvent descriptors Prod.fst rfl firstAssignment localProfile
private theorem node_compatible : Compatible sourceNode descriptors Prod.fst Prod.snd firstAssignment secondAssignment := by
  have support : SourceCurrentNativeNormalizationInputs.support sourceNode descriptors =
      [.inr (.uninterned 0,.uninterned 9)] := by cbv
  constructor
  · intro name member
    rw [support] at member
    cases List.mem_singleton.mp member
  · intro atom member
    rw [support] at member
    obtain rfl := Sum.inr.inj (List.mem_singleton.mp member)
    cbv
private theorem child_compatible : Compatible (.var 0) descriptors Prod.fst Prod.snd firstAssignment secondAssignment :=
  SourceCurrentScopedProfileInputs.node_child sourceRows descriptors Prod.fst Prod.snd firstAssignment secondAssignment
    node_compatible 8 false [.var 0] List.mem_cons_self (by cbv) (.var 0) List.mem_cons_self
private theorem selected_profile : firstAssignment (.uninterned 0) = secondAssignment (.uninterned 9) :=
  SourceCurrentScopedProfileInputs.variable_input 0 descriptors Prod.fst Prod.snd firstAssignment secondAssignment
    child_compatible (.inr (.uninterned 0,.uninterned 9)) rfl
private theorem union_compatible : Compatible (.union [sourceNode,.empty]) descriptors Prod.fst Prod.snd
    firstAssignment secondAssignment := by
  have support : SourceCurrentNativeNormalizationInputs.support (.union [sourceNode,.empty]) descriptors =
      SourceCurrentNativeNormalizationInputs.support sourceNode descriptors := by cbv
  exact ⟨fun name member => node_compatible.1 name (support ▸ member),
    fun atom member => node_compatible.2 atom (support ▸ member)⟩
private theorem union_node : Compatible sourceNode descriptors Prod.fst Prod.snd firstAssignment secondAssignment :=
  SourceCurrentScopedProfileInputs.union_member [sourceNode,.empty] descriptors Prod.fst Prod.snd
    firstAssignment secondAssignment union_compatible sourceNode List.mem_cons_self

private theorem checked :
  Ready base ∧
  build (.binder true body) (inputs (.uninterned 0)) base = .done (value firstBuilt) firstHeap ∧
  build (.binder true body) (inputs (.uninterned 9)) firstHeap = .done (value secondBuilt) common ∧
  firstMarker = ignoredName ∧
  firstAssignment ignoredName ≠ secondAssignment ignoredName ∧
  Sum.inr (ignoredName,ignoredName) ∉ SourceCurrentNativeNormalizationInputs.support (.binder true body) descriptors ∧
  Compatible body (.inr (.inl ()) :: descriptors.map InternedFreshOrdinaryLiveInputs.liftInput)
    (Sum.elim (fun _ => firstMarker) Prod.fst) (Sum.elim (fun _ => secondMarker) Prod.snd)
    (SourceCurrentStoredMuProfileContract.shadow firstMarker localProfile firstAssignment)
    (SourceCurrentStoredMuProfileContract.shadow secondMarker localProfile secondAssignment) ∧
  Compatible body (.inr (.inl ()) :: descriptors.map InternedFreshOrdinaryLiveInputs.liftInput)
    (Sum.elim (fun _ => .depth) Prod.fst) (Sum.elim (fun _ => .depth) Prod.snd)
    (SourceCurrentStoredMuProfileContract.shadow .depth localProfile firstAssignment)
    (SourceCurrentStoredMuProfileContract.shadow .depth localProfile secondAssignment) ∧
  Compatible firstEvent.expression (.inr (.inl ()) :: descriptors.map InternedFreshOrdinaryLiveInputs.liftInput)
    (Sum.elim (fun _ => .interned firstEvent.entry.identity) Prod.fst)
    (Sum.elim (fun _ => .uninterned (ordinaryLevel firstEvent.depth)) Prod.fst)
    (SourceCurrentStoredMuProfileContract.shadow (.interned firstEvent.entry.identity) localProfile firstAssignment)
    (SourceCurrentStoredMuProfileContract.shadow (.uninterned (ordinaryLevel firstEvent.depth)) localProfile firstAssignment) ∧
  build sourceNode (inputs (.uninterned 0)) base = .done (value sourceCall) sourceCall.state ∧
  (InternedEdgeResidency.nodeEdges (value sourceCall)).length = 1 ∧
  Compatible sourceNode descriptors Prod.fst Prod.snd firstAssignment secondAssignment ∧
  firstAssignment (.uninterned 0) = secondAssignment (.uninterned 9) := by
  refine ⟨baseReady,firstActual,secondActual,?_,?_,?_,ordinary_extended,depth_extended,event_extended,?_,?_,union_node,selected_profile⟩
  · cbv
  · cbv
    intro impossible
    cases impossible
  · rw [support_only]
    intro impossible
    have same := List.mem_singleton.mp impossible
    cbv at same
    cases same
  · cbv
  · cbv

/-- Actual publications permit unused capture collision and original dead-row disagreement. -/
theorem actual_unused_collision :
  Ready base ∧
  build (.binder true body) (inputs (.uninterned 0)) base = .done (value firstBuilt) firstHeap ∧
  build (.binder true body) (inputs (.uninterned 9)) firstHeap = .done (value secondBuilt) common ∧
  firstMarker = ignoredName ∧
  firstAssignment ignoredName ≠ secondAssignment ignoredName ∧
  Sum.inr (ignoredName,ignoredName) ∉ SourceCurrentNativeNormalizationInputs.support (.binder true body) descriptors ∧
  Compatible body (.inr (.inl ()) :: descriptors.map InternedFreshOrdinaryLiveInputs.liftInput)
    (Sum.elim (fun _ => firstMarker) Prod.fst) (Sum.elim (fun _ => secondMarker) Prod.snd)
    (SourceCurrentStoredMuProfileContract.shadow firstMarker localProfile firstAssignment)
    (SourceCurrentStoredMuProfileContract.shadow secondMarker localProfile secondAssignment) ∧
  Compatible body (.inr (.inl ()) :: descriptors.map InternedFreshOrdinaryLiveInputs.liftInput)
    (Sum.elim (fun _ => .depth) Prod.fst) (Sum.elim (fun _ => .depth) Prod.snd)
    (SourceCurrentStoredMuProfileContract.shadow .depth localProfile firstAssignment)
    (SourceCurrentStoredMuProfileContract.shadow .depth localProfile secondAssignment) ∧
  Compatible firstEvent.expression (.inr (.inl ()) :: descriptors.map InternedFreshOrdinaryLiveInputs.liftInput)
    (Sum.elim (fun _ => .interned firstEvent.entry.identity) Prod.fst)
    (Sum.elim (fun _ => .uninterned (ordinaryLevel firstEvent.depth)) Prod.fst)
    (SourceCurrentStoredMuProfileContract.shadow (.interned firstEvent.entry.identity) localProfile firstAssignment)
    (SourceCurrentStoredMuProfileContract.shadow (.uninterned (ordinaryLevel firstEvent.depth)) localProfile firstAssignment) ∧
  build sourceNode (inputs (.uninterned 0)) base = .done (value sourceCall) sourceCall.state ∧
  (InternedEdgeResidency.nodeEdges (value sourceCall)).length = 1 ∧
  Compatible sourceNode descriptors Prod.fst Prod.snd firstAssignment secondAssignment ∧
  firstAssignment (.uninterned 0) = secondAssignment (.uninterned 9) := checked

end MicroCFTA.ScopedInputKernels
