import MicroCFTA.SourceCurrentPublicationFiniteRootReconstruction
import MicroCFTA.SourceCurrentFiniteRootSourceNode
import MicroCFTA.SourceCurrentSourceUnionFilterInduction

/-!
# Immediate source cases for actual publication bodies

The node case uses indexed strict source children at each later execution
heap. Actual publication contexts supply both local references and all
captured values. A shared sparse map permits unused lexical aliases.
The observation reader stays fixed. The active nested-binder source case
remains an explicit induction obligation.
-/
namespace MicroCFTA.SourceCurrentPublicationBodySourceCases
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryLiveInputs (input liftInput local_inputs)
open InternedBinderProtocol (Reference)
open SourceCurrentNativeMuPublication (Publication)
open SourceEqualityRequiredCache (Keeps)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt)
open SourceCurrentFiniteObservationExecution (AlignedAt)
open SourceCurrentPublicationFiniteRootReconstruction (BodyIH)
open SourceCurrentPublicationSharedReplacements (shared)
open SourceCurrentReaderReplacementSlots (Paired Slot)
open SourceCurrentUsedBinderAliasTransport (Aliases NamePair)
open SourceCurrentUsedBinderRootAlternatives (RootMatch)
open SourceCurrentFiniteRootReconstruction (Executions)

private theorem replacements_shared [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (state : State Symbol Guard) (replacement : Value Symbol Guard)
    (available : Available state replacement) (environment : Environment Symbol Guard)
    (replacements : Replacements state environment) :
    Replacements state (shared event replacement replacement environment) := by
  intro name value found
  dsimp only [shared,SourceCurrentStoredMuBinderChildLineage.bind] at found
  split at found
  · cases found; exact available
  · split at found
    · cases found; exact available
    · exact replacements name value found

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem callback_inputs
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    Values event.afterBody event.environment ∧
      Available event.afterBody (.reference (.interned event.entry.identity)) := by
  obtain ⟨_,cutContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have argument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have inputs := bodyContext.base.local (.interned event.entry.identity) argument
  have actual : callback event.expression event.environment (.interned event.entry.identity) event.allocated =
      .done event.body event.afterBody := event.bodyDone
  have checked := InternedFreshOrdinaryFacts.callback_verified event.expression event.environment
    (.interned event.entry.identity) event.allocated bodyContext.base.normal.facts inputs.inputs
  constructor
  · intro value member
    simpa only [actual,Outcome.state] using checked.available value (bodyContext.base.inputs value member)
  · simpa only [actual,Outcome.state] using checked.available _ argument

private theorem paired_shared (depth : Nat) (view : State Symbol Guard)
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (replacement : Value Symbol Guard) (environment : Environment Symbol Guard) :
    Paired (RelatedAt depth view) (shared event replacement replacement environment)
      (shared event replacement replacement environment)
      (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
      (.reference (.interned event.entry.identity) :: event.environment) := by
  have reflexive (value : Value Symbol Guard) : RelatedAt depth view value value :=
    ⟨Iff.rfl,SourceCurrentOpenObservations.Same.refl _ _ _⟩
  have existing := SourceCurrentPublicationSharedReplacements.paired event (RelatedAt depth view) reflexive
    replacement replacement environment (reflexive replacement)
  cases existing with
  | cons head tail =>
      refine .cons ?_ tail
      simpa only [Slot,shared,SourceCurrentStoredMuBinderChildLineage.bind,reduceCtorEq,ite_false,ite_true,
        Option.getD_some] using reflexive replacement

/-- Indexed strict source children derive the actual node publication's body hypothesis. -/
theorem node (event : Publication (Symbol := Symbol) (Guard := Guard))
    (expressions : List (EdgeSyntax Symbol Guard)) (shape : event.expression = .node expressions)
    (depth : Nat) (view common : State Symbol Guard) (current : Keeps event.afterBody common)
    (replacement : Value Symbol Guard) (available : Available common replacement)
    (environment : Environment Symbol Guard) (replacements : Replacements common environment)
    (children : ∀ (index : Nat) (symbol : Symbol) (guard : Guard) (originals : List (Syntax Symbol Guard)),
      expressions[index]? = some (.mk symbol guard originals) →
      ∀ (childIndex : Nat) (child : Syntax Symbol Guard), originals[childIndex]? = some child →
        sizeOf child < sizeOf event.expression →
        ∀ execution, Keeps common execution → AlignedAt (depth+1) view execution child) :
    BodyIH depth view event replacement environment common := by
  intro execution kept
  let inputs : List (Sum (Value Symbol Guard) Unit) := event.environment.map Sum.inl
  let names : Unit → Reference := fun _ => .depth
  let localInputs := .inr (.inl ()) :: inputs.map liftInput
  let firstNames := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) names
  let secondNames := Sum.elim (fun _ : Unit => .interned event.entry.identity) names
  have fixed : inputs.map (input names) = event.environment := by
    simp [inputs,input,List.map_map,Function.comp_def]
  have instantiated (own : Reference) :
      localInputs.map (input (Sum.elim (fun _ : Unit => own) names)) = .reference own :: event.environment := by
    rw [local_inputs,fixed]
  change sizeOf event.expression < sizeOf (.binder event.smart event.expression : Syntax Symbol Guard) →
    Aliases event.expression localInputs firstNames secondNames →
    ∀ before later, Context before (localInputs.map (input firstNames)) →
      Context later (localInputs.map (input secondNames)) →
    ∀ rawFirst rawHeap rawSecond rawLater,
      build event.expression (localInputs.map (input firstNames)) before = .done rawFirst rawHeap →
      build event.expression (localInputs.map (input secondNames)) later = .done rawSecond rawLater →
      Grows rawHeap execution → Grows rawLater execution →
      RootMatch (NamePair (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity))
        (Executions (depth+1) view execution (shared event replacement replacement environment)
          (shared event replacement replacement environment)) rawFirst rawSecond
  intro _ _ before later firstContext secondContext rawFirst rawHeap rawSecond rawLater firstRaw secondRaw firstGrowth secondGrowth
  have all := current.trans kept
  obtain ⟨captures,argument⟩ := callback_inputs event
  have firstInputs : Values execution (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | present
    · exact InternedNestedProvenance.ordinary_available _ _
    · exact all.available value (captures value present)
  have secondInputs : Values execution (.reference (.interned event.entry.identity) :: event.environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | present
    · exact all.available _ argument
    · exact all.available value (captures value present)
  have maps := replacements_shared event execution replacement (kept.available replacement available) environment
    (fun name value found => kept.available value (replacements name value found))
  apply SourceCurrentFiniteRootSourceNode.node expressions event.environment _ _ (depth+1) view execution
    (fun index symbol guard originals found childIndex child selected smaller =>
      children index symbol guard originals found childIndex child selected (by simpa only [shape] using smaller) execution kept)
    _ _ (paired_shared (depth+1) view event replacement environment) kept.ready firstInputs secondInputs maps maps
    before rawHeap later rawLater
    (by simpa only [firstNames,instantiated] using firstContext)
    (by simpa only [secondNames,instantiated] using secondContext) rawFirst rawSecond
    (by simpa only [shape,firstNames,instantiated] using firstRaw)
    (by simpa only [shape,secondNames,instantiated] using secondRaw) firstGrowth secondGrowth

end MicroCFTA.SourceCurrentPublicationBodySourceCases
