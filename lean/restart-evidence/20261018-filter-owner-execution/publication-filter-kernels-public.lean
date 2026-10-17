import MicroCFTA.SourceCurrentPublicationFilterAlignment

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.PublicationFilterKernels.Nonbare
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open InternedBinderProtocol (Reference)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def replacementSource : Syntax Nat Bool := .binder false (.node [.mk 3 true []])
private def replacementBuilt := build replacementSource [] empty
private def replacement := value replacementBuilt
private def base := replacementBuilt.state
private def rows : List (InternedNestedConstruction.EdgeSyntax Nat Bool) :=
  [.mk 8 false [.union [.var 0,.empty]],.mk 6 true [.empty,.var 1],
   .mk 8 false [.union [.var 0,.empty]],.mk 2 true [.var 0,.var 0]]
private def expression : Syntax Nat Bool :=
  .union [.union [.node [.mk 8 false [.var 0]],.node rows,.var 0],.var 2,.empty]
private def captures : List (Value Nat Bool) := [.reference (.uninterned 1),replacement]
private def depthCall := callback expression captures .depth base
private def ordinaryCall := callback expression captures (.uninterned (ordinaryLevel (value depthCall))) depthCall.state
private def key := muKey (value depthCall) (value ordinaryCall)
private def entry := Cache.intern ordinaryCall.state.nodes key
private def allocated := {ordinaryCall.state with nodes := entry.2}
private def bodyCall := callback expression captures (.interned entry.1.identity) allocated

private theorem replacementDone : replacementBuilt = .done replacement base := by cbv
private theorem baseReady : Ready base :=
  SourceEqualityRequiredCache.constructed replacementSource replacement base replacementDone
private theorem inputsAvailable : InternedNestedProvenance.Values base captures := by
  intro selected member
  rcases List.mem_cons.mp member with rfl | member
  · exact InternedNestedProvenance.ordinary_available _ _
  · have same := List.mem_singleton.mp member
    subst selected
    exact (InternedFreshOrdinaryFacts.closed_verified replacementSource).result replacement base replacementDone

private def event : Publication (Symbol := Nat) (Guard := Bool) where
  smart := true
  expression := expression
  environment := captures
  before := base
  afterDepth := depthCall.state
  cut := ordinaryCall.state
  afterBody := bodyCall.state
  depth := value depthCall
  ordinary := value ordinaryCall
  body := value bodyCall
  context := ⟨SourceRecursiveIntersectionSemanticHeap.context base baseReady.semantic captures inputsAvailable,
    baseReady.semantic.2⟩
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv

private def common := event.after
private theorem currentReady : Ready common := by
  have actual : build (.binder true expression) captures base = .done event.result common := event.build_done
  have context := SourceRecursiveIntersectionSemanticHeap.context base baseReady.semantic captures inputsAvailable
  refine ⟨?_,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source
      (.binder true expression) captures base baseReady.semantic inputsAvailable
  · exact InternedFreshOrdinaryCoverage.build_covered (.binder true expression) captures base
      baseReady.semantic.1.normal.facts.coherent.valid baseReady.covered event.result common actual
  · simpa only [actual,Outcome.state] using (InternedOpenDepthExecution.build_depth
      (.binder true expression) captures base context baseReady.semantic.2 baseReady.depth).heap

private theorem current : Keeps event.afterBody common := by
  refine ⟨currentReady,?_,?_⟩
  · change Grows event.afterBody {event.afterBody with nodeRecords :=
      (keepFirst event.afterBody.nodeRecords event.key event.candidate)}
    exact ⟨extends_refl _,extends_refl _,extends_refl _,keepFirst_extends _ _ _⟩
  · exact extends_refl _
private theorem replacementAvailable : Available common replacement := by
  have initial := (InternedFreshOrdinaryFacts.closed_verified replacementSource).result replacement base replacementDone
  have retained := (InternedFreshOrdinaryFacts.build_verified (.binder true expression) captures base
    baseReady.semantic.1.normal.facts inputsAvailable).available replacement initial
  have actual : build (.binder true expression) captures base = .done event.result common := event.build_done
  simpa only [actual,Outcome.state] using retained

private def bodyMap : Environment Nat Bool :=
  fun name => if name = .interned event.entry.identity then some replacement else none
private def ordinaryMap : Environment Nat Bool :=
  fun name => if name = .uninterned (ordinaryLevel event.depth) then some replacement else none

private theorem witness_proof :
    build replacementSource [] empty = .done replacement base ∧
    build (.binder true expression) captures base = .done event.result common ∧
    build (.binder true expression) captures common = .done event.result common ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    (.reference (.uninterned (ordinaryLevel event.depth)) : Value Nat Bool) ∈ event.environment ∧
    (∃ own body depth ordinary, replacement = .mu own body depth ordinary) ∧
    ∃ left middle right reader,
      execute event.body bodyMap common = .done left middle ∧
      execute event.ordinary ordinaryMap middle = .done right reader ∧
      execute event.body bodyMap reader = .done left reader ∧
      execute event.ordinary ordinaryMap reader = .done right reader ∧
      Keeps common middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
      Nonempty (History common middle) ∧ Nonempty (History middle reader) ∧
      SourceCurrentOpenObservationSurvival.Related left right := by
  refine ⟨replacementDone,event.build_done,?_,?_,?_,?_,?_⟩
  · exact InternedFreshOrdinaryReplay.build_replay (.binder true expression) captures base common event.result common
      baseReady.semantic.1.normal.facts.coherent.valid event.build_done (grows_refl _)
  · cbv
  · have marker : ordinaryLevel event.depth = 1 := by cbv
    rw [marker]
    exact List.mem_cons_self
  · exact ⟨_,_,_,_,by cbv⟩
  · exact SourceCurrentPublicationFilterAlignment.publication_binder_free event
      (by cbv) common current replacement replacementAvailable

/-- A nested root union removes bare self and retains opaque captures through both actual filtered reconstructions. -/
theorem witness :
    build replacementSource [] empty = .done replacement base ∧
    build (.binder true expression) captures base = .done event.result common ∧
    build (.binder true expression) captures common = .done event.result common ∧
    InternedFreshOrdinaryDepthHeap.usesLocal event.depth event.ordinary = true ∧
    (.reference (.uninterned (ordinaryLevel event.depth)) : Value Nat Bool) ∈ event.environment ∧
    (∃ own body depth ordinary, replacement = .mu own body depth ordinary) ∧
    ∃ left middle right reader,
      execute event.body bodyMap common = .done left middle ∧
      execute event.ordinary ordinaryMap middle = .done right reader ∧
      execute event.body bodyMap reader = .done left reader ∧
      execute event.ordinary ordinaryMap reader = .done right reader ∧
      Keeps common middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
      Nonempty (History common middle) ∧ Nonempty (History middle reader) ∧
      SourceCurrentOpenObservationSurvival.Related left right := witness_proof

end MicroCFTA.PublicationFilterKernels.Nonbare

namespace MicroCFTA.PublicationFilterKernels.Bare
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open InternedBinderProtocol (Reference)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def replacementSource : Syntax Nat Bool := .binder false (.node [.mk 3 true []])
private def replacementBuilt := build replacementSource [] empty
private def replacement := value replacementBuilt
private def base := replacementBuilt.state
private def expression : Syntax Nat Bool := .union [.empty,.var 0,.var 0]
private def captures : List (Value Nat Bool) := []
private def depthCall := callback expression captures .depth base
private def ordinaryCall := callback expression captures (.uninterned (ordinaryLevel (value depthCall))) depthCall.state
private def key := muKey (value depthCall) (value ordinaryCall)
private def entry := Cache.intern ordinaryCall.state.nodes key
private def allocated := {ordinaryCall.state with nodes := entry.2}
private def bodyCall := callback expression captures (.interned entry.1.identity) allocated

private theorem replacementDone : replacementBuilt = .done replacement base := by cbv
private theorem baseReady : Ready base :=
  SourceEqualityRequiredCache.constructed replacementSource replacement base replacementDone
private theorem inputsAvailable : InternedNestedProvenance.Values base captures := by
  intro selected member
  cases member

private def event : Publication (Symbol := Nat) (Guard := Bool) where
  smart := true
  expression := expression
  environment := captures
  before := base
  afterDepth := depthCall.state
  cut := ordinaryCall.state
  afterBody := bodyCall.state
  depth := value depthCall
  ordinary := value ordinaryCall
  body := value bodyCall
  context := ⟨SourceRecursiveIntersectionSemanticHeap.context base baseReady.semantic captures inputsAvailable,
    baseReady.semantic.2⟩
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv

private def common := event.after
private theorem currentReady : Ready common := by
  have actual : build (.binder true expression) captures base = .done event.result common := event.build_done
  have context := SourceRecursiveIntersectionSemanticHeap.context base baseReady.semantic captures inputsAvailable
  refine ⟨?_,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source
      (.binder true expression) captures base baseReady.semantic inputsAvailable
  · exact InternedFreshOrdinaryCoverage.build_covered (.binder true expression) captures base
      baseReady.semantic.1.normal.facts.coherent.valid baseReady.covered event.result common actual
  · simpa only [actual,Outcome.state] using (InternedOpenDepthExecution.build_depth
      (.binder true expression) captures base context baseReady.semantic.2 baseReady.depth).heap

private theorem current : Keeps event.afterBody common := by
  refine ⟨currentReady,?_,?_⟩
  · change Grows event.afterBody {event.afterBody with nodeRecords :=
      (keepFirst event.afterBody.nodeRecords event.key event.candidate)}
    exact ⟨extends_refl _,extends_refl _,extends_refl _,keepFirst_extends _ _ _⟩
  · exact extends_refl _
private theorem replacementAvailable : Available common replacement := by
  have initial := (InternedFreshOrdinaryFacts.closed_verified replacementSource).result replacement base replacementDone
  have retained := (InternedFreshOrdinaryFacts.build_verified (.binder true expression) captures base
    baseReady.semantic.1.normal.facts inputsAvailable).available replacement initial
  have actual : build (.binder true expression) captures base = .done event.result common := event.build_done
  simpa only [actual,Outcome.state] using retained

private def bodyMap : Environment Nat Bool :=
  fun name => if name = .interned event.entry.identity then some replacement else none
private def ordinaryMap : Environment Nat Bool :=
  fun name => if name = .uninterned (ordinaryLevel event.depth) then some replacement else none

private theorem witness_proof :
    build replacementSource [] empty = .done replacement base ∧
    build (.binder true expression) captures base = .done event.result common ∧
    build (.binder true expression) captures common = .done event.result common ∧
    event.body = .reference (.interned event.entry.identity) ∧
    event.ordinary = .reference (.uninterned (ordinaryLevel event.depth)) ∧
    (∃ own body depth ordinary, replacement = .mu own body depth ordinary) ∧
    ∃ left middle right reader,
      execute event.body bodyMap common = .done left middle ∧
      execute event.ordinary ordinaryMap middle = .done right reader ∧
      execute event.body bodyMap reader = .done left reader ∧
      execute event.ordinary ordinaryMap reader = .done right reader ∧
      Keeps common middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
      Nonempty (History common middle) ∧ Nonempty (History middle reader) ∧
      SourceCurrentOpenObservationSurvival.Related left right := by
  refine ⟨replacementDone,event.build_done,?_,?_,?_,?_,?_⟩
  · exact InternedFreshOrdinaryReplay.build_replay (.binder true expression) captures base common event.result common
      baseReady.semantic.1.normal.facts.coherent.valid event.build_done (grows_refl _)
  · cbv
  · cbv
  · exact ⟨_,_,_,_,by cbv⟩
  · exact SourceCurrentPublicationFilterAlignment.publication_binder_free event
      (by cbv) common current replacement replacementAvailable

/-- Actual root-union bare-self callbacks reconstruct the same recursive replacement. -/
theorem witness :
    build replacementSource [] empty = .done replacement base ∧
    build (.binder true expression) captures base = .done event.result common ∧
    build (.binder true expression) captures common = .done event.result common ∧
    event.body = .reference (.interned event.entry.identity) ∧
    event.ordinary = .reference (.uninterned (ordinaryLevel event.depth)) ∧
    (∃ own body depth ordinary, replacement = .mu own body depth ordinary) ∧
    ∃ left middle right reader,
      execute event.body bodyMap common = .done left middle ∧
      execute event.ordinary ordinaryMap middle = .done right reader ∧
      execute event.body bodyMap reader = .done left reader ∧
      execute event.ordinary ordinaryMap reader = .done right reader ∧
      Keeps common middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
      Nonempty (History common middle) ∧ Nonempty (History middle reader) ∧
      SourceCurrentOpenObservationSurvival.Related left right := witness_proof

end MicroCFTA.PublicationFilterKernels.Bare

#check @MicroCFTA.PublicationFilterKernels.Nonbare.witness
#print MicroCFTA.PublicationFilterKernels.Nonbare.witness
#print axioms MicroCFTA.PublicationFilterKernels.Nonbare.witness

#check @MicroCFTA.PublicationFilterKernels.Bare.witness
#print MicroCFTA.PublicationFilterKernels.Bare.witness
#print axioms MicroCFTA.PublicationFilterKernels.Bare.witness
