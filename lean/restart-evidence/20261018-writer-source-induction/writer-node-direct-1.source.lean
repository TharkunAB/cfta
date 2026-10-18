import MicroCFTA.SourceCurrentPublicationSharedReplacements
import MicroCFTA.SourceCurrentReaderFiniteOrdinaryStep
import MicroCFTA.SourceCurrentRetainedMuWriterAlignment
import MicroCFTA.InternedFlatProbeCosts

/-!
# Finite reconstruction of an actual earlier node-body writer

Actual publication callbacks with a node source root retain their raw
results. The shared replacement map handles unused captured aliases.
Indexed strict-child hypotheses compare the reconstructed outputs at one
reader. Children can contain nested used Mu syntax. The initial producer
constructs both calls and their final reader with one common replacement.
No BinderFree, reader transport, or whole-parent comparison is assumed.
-/
namespace MicroCFTA.SourceCurrentWriterFiniteNodeAlignment
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext (Context)
open InternedStoredSubstitution (Environment Replacements leaves encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentRetainedMuWriterAlignment (Writer)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt AlignedAt)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceCurrentPublicationSharedReplacements (shared)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Both actual reconstructions retain their schedules and finite agreement at the final reader. -/
def ReconstructionAt (observationDepth : Nat) (entry : Interned NodeKey)
    (body sourceDepth ordinary replacement : Value Symbol Guard) (before : State Symbol Guard) : Prop :=
  ∃ left middle right reader,
    execute body (bind (.interned entry.identity) replacement (fun _ => none)) before = .done left middle ∧
    execute ordinary (bind (.uninterned (ordinaryLevel sourceDepth)) replacement (fun _ => none)) middle = .done right reader ∧
    execute body (bind (.interned entry.identity) replacement (fun _ => none)) reader = .done left reader ∧
    execute ordinary (bind (.uninterned (ordinaryLevel sourceDepth)) replacement (fun _ => none)) reader = .done right reader ∧
    Keeps before middle ∧ Keeps middle reader ∧ Available reader left ∧ Available reader right ∧
    Nonempty (History before middle) ∧ Nonempty (History middle reader) ∧
    RelatedAt observationDepth reader left right

private theorem node_callback (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (name : Reference) (before after : State Symbol Guard)
    (context : Context before (.reference name :: environment)) (value : Value Symbol Guard)
    (actual : callback (.node expressions) environment name before = .done value after) :
    build (.node expressions) (.reference name :: environment) before = .done value after := by
  obtain ⟨raw,middle,called,filtered⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.callback_raw (.node expressions) environment name before value after actual
  cases rowsDone : buildEdges expressions (.reference name :: environment) before with
  | pending key state => simp only [build,rowsDone,Outcome.bind] at called; cases called
  | done rows current =>
      have made : run (makeNode rows) current = (raw,middle) :=
        Prod.ext (Outcome.done.inj (by simpa only [build,rowsDone,Outcome.bind,work] using called)).1
          (Outcome.done.inj (by simpa only [build,rowsDone,Outcome.bind,work] using called)).2
      have checked := buildEdges_verified expressions _ before context.normal.facts context.inputs
      have facts : InternedNestedFacts.Facts current := by simpa only [rowsDone,Outcome.state] using checked.facts
      have fixed := InternedFlatProbeCosts.makeNode_filter name rows current facts.coherent facts.linked
        (checked.result rows current rowsDone)
      rw [made] at fixed
      rw [fixed,run] at filtered
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj filtered
      exact called

/-- Actual node-root publications retain both unfiltered calls and the original callback growth. -/
theorem raw_calls (event : Publication (Symbol := Symbol) (Guard := Guard))
    (expressions : List (EdgeSyntax Symbol Guard)) (node : event.expression = .node expressions) :
    build (.node expressions) (.reference (.interned event.entry.identity) :: event.environment)
      event.allocated = .done event.body event.afterBody ∧
    build (.node expressions) (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
      event.afterDepth = .done event.ordinary event.cut ∧ Grows event.cut event.afterBody := by
  obtain ⟨depthContext,cutContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have argument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have bodyInputs := bodyContext.base.local (.interned event.entry.identity) argument
  have ordinaryInputs := depthContext.base.local (.uninterned (ordinaryLevel event.depth))
    (InternedNestedProvenance.ordinary_available _ _)
  have bodyDone : callback (.node expressions) event.environment (.interned event.entry.identity)
      event.allocated = .done event.body event.afterBody := node ▸ event.bodyDone
  have ordinaryDone : callback (.node expressions) event.environment (.uninterned (ordinaryLevel event.depth))
      event.afterDepth = .done event.ordinary event.cut := node ▸ event.ordinaryDone
  have checked := callback_verified (.node expressions) event.environment (.interned event.entry.identity)
    event.allocated bodyInputs.normal.facts bodyInputs.inputs
  have growth : Grows event.allocated event.afterBody := by
    simpa only [bodyDone,Outcome.state] using checked.growth
  have reserved : Grows event.cut event.allocated :=
    ⟨extends_refl _,InternedBinderProtocol.intern_grows _ _,extends_refl _,extends_refl _⟩
  exact ⟨node_callback expressions _ _ _ _ bodyInputs _ bodyDone,
    node_callback expressions _ _ _ _ ordinaryInputs _ ordinaryDone,grows_trans reserved growth⟩

/-- Strict source-child hypotheses compare actual node-body reconstructions with distinct related replacements. -/
theorem warm (event : Publication (Symbol := Symbol) (Guard := Guard))
    (expressions : List (EdgeSyntax Symbol Guard)) (node : event.expression = .node expressions)
    (depth : Nat) (reader : State Symbol Guard) (current : Keeps event.afterBody reader)
    (children : ∀ (rowIndex : Nat) (symbol : Symbol) (guard : Guard) (originals : List (Syntax Symbol Guard)),
      expressions[rowIndex]? = some (.mk symbol guard originals) →
      ∀ (childIndex : Nat) (child : Syntax Symbol Guard), originals[childIndex]? = some child →
        sizeOf child < sizeOf (.node expressions : Syntax Symbol Guard) → AlignedAt depth reader child)
    (firstValue secondValue : Value Symbol Guard)
    (firstAvailable : Available reader firstValue) (secondAvailable : Available reader secondValue)
    (related : RelatedAt depth reader firstValue secondValue) (left right : Value Symbol Guard)
    (firstDone : execute event.body (bind (.interned event.entry.identity) firstValue (fun _ => none)) reader = .done left reader)
    (secondDone : execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) secondValue (fun _ => none)) reader = .done right reader) :
    RelatedAt (depth + 1) reader left right := by
  obtain ⟨depthContext,cutContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have argument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have bodyInputs := bodyContext.base.local (.interned event.entry.identity) argument
  have checked := callback_verified event.expression event.environment (.interned event.entry.identity)
    event.allocated bodyInputs.normal.facts bodyInputs.inputs
  have actual : callback event.expression event.environment (.interned event.entry.identity) event.allocated =
      .done event.body event.afterBody := event.bodyDone
  have argumentEnd : Available event.afterBody (.reference (.interned event.entry.identity)) := by
    simpa only [actual,Outcome.state] using checked.available _ argument
  have captures : Values event.afterBody event.environment := by
    intro value member
    simpa only [actual,Outcome.state] using checked.available value (bodyContext.base.inputs value member)
  have firstInputs : Values reader (.reference (.interned event.entry.identity) :: event.environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact current.available _ argumentEnd
    · exact current.available _ (captures _ member)
  have secondInputs : Values reader (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact InternedNestedProvenance.ordinary_available _ _
    · exact current.available _ (captures _ member)
  obtain ⟨firstRaw,secondRaw,cutGrowth⟩ := raw_calls event expressions node
  have firstWarm := InternedFreshOrdinaryReplay.build_replay (.node expressions) _ event.allocated reader
    event.body event.afterBody bodyInputs.normal.facts.coherent.valid firstRaw current.growth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay (.node expressions) _ event.afterDepth reader
    event.ordinary event.cut depthContext.base.normal.facts.coherent.valid secondRaw (grows_trans cutGrowth current.growth)
  have bodyAvailable := (build_verified (.node expressions) _ reader current.ready.semantic.1.normal.facts firstInputs).result
    event.body reader firstWarm
  have ordinaryAvailable := (build_verified (.node expressions) _ reader current.ready.semantic.1.normal.facts secondInputs).result
    event.ordinary reader secondWarm
  let environment := shared event firstValue secondValue (fun _ => none)
  have replacements : Replacements reader environment := by
    intro name value found
    dsimp only [environment,shared,SourceCurrentStoredMuBinderChildLineage.bind] at found
    split at found
    · cases found; exact firstAvailable
    · split at found
      · cases found; exact secondAvailable
      · cases found
  have substitutions := SourceCurrentPublicationSharedReplacements.substitutions event firstValue secondValue
    (fun _ => none) reader current.ready.semantic.1.normal.facts.coherent bodyAvailable ordinaryAvailable
  have firstShared : execute event.body environment reader = .done left reader := by
    rw [← substitutions.1]
    exact firstDone
  have secondShared : execute event.ordinary environment reader = .done right reader := by
    rw [← substitutions.2]
    exact secondDone
  have paired := SourceCurrentPublicationSharedReplacements.paired event (RelatedAt depth reader)
    (fun value => ⟨Iff.rfl,SourceCurrentOpenObservations.Same.refl depth reader [value]⟩)
    firstValue secondValue (fun _ => none) related
  exact SourceCurrentReaderFiniteOrdinaryStep.ordinary expressions depth reader children _ _ environment environment
    paired current.ready firstInputs secondInputs replacements replacements _ _ firstWarm secondWarm _ _ firstShared secondShared

/-- The actual selected earlier writer constructs both calls and applies strict child induction at their final reader. -/
theorem writer {before : State Symbol Guard} {key : NodeKey} {entry : Interned NodeKey}
    {body sourceDepth ordinary : Value Symbol Guard} {event : Publication (Symbol := Symbol) (Guard := Guard)}
    (selected : Writer before key (.mu entry body sourceDepth ordinary) event)
    (present : before.nodeRecords key = some (.mu entry body sourceDepth ordinary))
    (expressions : List (EdgeSyntax Symbol Guard)) (node : event.expression = .node expressions) (depth : Nat)
    (children : ∀ reader (rowIndex : Nat) (symbol : Symbol) (guard : Guard) (originals : List (Syntax Symbol Guard)),
      expressions[rowIndex]? = some (.mk symbol guard originals) →
      ∀ (childIndex : Nat) (child : Syntax Symbol Guard), originals[childIndex]? = some child →
        sizeOf child < sizeOf (.node expressions : Syntax Symbol Guard) → AlignedAt depth reader child)
    (ready : Ready before) (replacement : Value Symbol Guard) (available : Available before replacement) :
    ReconstructionAt (depth + 1) entry body sourceDepth ordinary replacement before := by
  obtain ⟨_,same,_,_,_,_,_,growth,issued⟩ := selected
  change Value.mu entry body sourceDepth ordinary = Value.mu event.entry event.body event.depth event.ordinary at same
  obtain ⟨rfl,rfl,rfl,rfl⟩ := Value.mu.inj same
  obtain ⟨left,middle,right,reader,firstDone,secondDone,firstKept,secondKept,leftAvailable,rightAvailable,
    firstHistory,secondHistory,_⟩ := SourceCurrentStoredReconstruction.mu key event.entry event.body event.depth event.ordinary
      replacement before ready present available
  have firstWarm := InternedFreshOrdinaryReplay.build_replay (encode (leaves event.body) [] event.body)
    ((leaves event.body).map (InternedStoredSubstitution.input (bind (.interned event.entry.identity) replacement (fun _ => none))))
    before reader left middle ready.semantic.1.normal.facts.coherent.valid firstDone secondKept.growth
  have secondWarm := InternedFreshOrdinaryReplay.build_replay (encode (leaves event.ordinary) [] event.ordinary)
    ((leaves event.ordinary).map (InternedStoredSubstitution.input
      (bind (.uninterned (ordinaryLevel event.depth)) replacement (fun _ => none))))
    middle reader right reader firstKept.ready.semantic.1.normal.facts.coherent.valid secondDone (grows_refl _)
  have initial : Keeps event.afterBody before := ⟨ready,growth,issued⟩
  have final := initial.trans (firstKept.trans secondKept)
  have replacementAvailable := secondKept.available replacement (firstKept.available replacement available)
  have related := warm event expressions node depth reader final (children reader) replacement replacement
    replacementAvailable replacementAvailable ⟨Iff.rfl,SourceCurrentOpenObservations.Same.refl depth reader [replacement]⟩
    left right firstWarm secondWarm
  exact ⟨left,middle,right,reader,firstDone,secondDone,firstWarm,secondWarm,firstKept,secondKept,
    leftAvailable,rightAvailable,firstHistory,secondHistory,related⟩

/-- Actual closed source history recovers the chosen writer before its node-body induction is applied. -/
theorem retained (source : Syntax Symbol Guard) (value : Value Symbol Guard) (before : State Symbol Guard)
    (built : build source [] empty = .done value before) (reader : State Symbol Guard) (current : Keeps before reader)
    (key : NodeKey) (entry : Interned NodeKey) (body sourceDepth ordinary : Value Symbol Guard)
    (present : before.nodeRecords key = some (.mu entry body sourceDepth ordinary)) :
    ∃ event, Writer reader key (.mu entry body sourceDepth ordinary) event ∧
      ∀ (expressions : List (EdgeSyntax Symbol Guard)), event.expression = .node expressions → ∀ depth,
        (∀ common (rowIndex : Nat) (symbol : Symbol) (guard : Guard) (originals : List (Syntax Symbol Guard)),
          expressions[rowIndex]? = some (.mk symbol guard originals) →
          ∀ (childIndex : Nat) (child : Syntax Symbol Guard), originals[childIndex]? = some child →
            sizeOf child < sizeOf (.node expressions : Syntax Symbol Guard) → AlignedAt depth common child) →
        ∀ replacement, Available reader replacement →
          ReconstructionAt (depth + 1) entry body sourceDepth ordinary replacement reader := by
  obtain ⟨event,selected,record,_,_,_⟩ := SourceCurrentRetainedMuWriterAlignment.retained source value before built reader current
    key entry body sourceDepth ordinary present
  exact ⟨event,selected,fun expressions node depth children replacement available =>
    writer selected record expressions node depth children current.ready replacement available⟩

end MicroCFTA.SourceCurrentWriterFiniteNodeAlignment
