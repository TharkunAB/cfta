import MicroCFTA.SourceCurrentPublicationFiniteRootReconstruction
import MicroCFTA.SourceCurrentFiniteRootSourceNode

/-!
# Immediate source cases for actual publication bodies

The node case uses indexed strict source children at each later execution
heap. Actual publication contexts supply both local references and all
captured values. A shared sparse map permits unused lexical aliases.
The observation reader stays fixed. The union case derives member return
growth from actual source sequences. Its induction hypotheses apply only
to indexed strict members. The active nested-binder source case remains
an explicit induction obligation. The clauses do not establish that all
source expressions satisfy these hypotheses at arbitrary readers.
-/
namespace MicroCFTA.SourceCurrentPublicationBodySourceCases
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext InternedFreshOrdinaryFacts
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

private theorem member_aliases {Atom : Type} (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (aliases : Aliases (.union expressions) inputs firstNames secondNames)
    (child : Syntax Symbol Guard) (member : child ∈ expressions) :
    Aliases child inputs firstNames secondNames := by
  have included (label : Sum Reference Atom)
      (present : label ∈ SourceCurrentUsedBinderAliasTransport.Scope child inputs) :
      label ∈ SourceCurrentUsedBinderAliasTransport.Scope (.union expressions) inputs := by
    rcases List.mem_cons.mp present with rfl | present
    · exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      unfold SourceCurrentNativeNormalizationInputs.support at present ⊢
      rw [InternedFreeNameSemantics.evaluate]
      exact (InternedFreeNameSemantics.evaluateMany_member expressions
        (inputs.map InternedFreshOrdinaryLiveInputs.inputProfile)
        (inputs.map SourceCurrentNativeNormalizationInputs.inputNames) label).mpr ⟨child,member,present⟩
  exact fun left leftMember right rightMember =>
    aliases left (included left leftMember) right (included right rightMember)

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

private theorem many_calls (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before inputs)
    (outputs : List (Value Symbol Guard)) (after execution : State Symbol Guard)
    (actual : buildMany expressions inputs before = .done outputs after) (growth : Grows after execution) :
    All₂ (fun expression output => ∃ entry returned,
      Context entry inputs ∧ build expression inputs entry = .done output returned ∧ Grows returned execution)
      expressions outputs := by
  induction expressions generalizing before outputs after with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at actual
      obtain ⟨rfl,_⟩ := actual
      exact .nil
  | cons expression rest ih =>
      cases called : build expression inputs before with
      | pending key current => simp only [buildMany,called,Outcome.bind] at actual; cases actual
      | done value middle =>
          cases tail : buildMany rest inputs middle with
          | pending key current => simp only [buildMany,called,tail,Outcome.bind] at actual; cases actual
          | done values final =>
              simp only [buildMany,called,tail,Outcome.bind,Outcome.done.injEq] at actual
              obtain ⟨rfl,rfl⟩ := actual
              have next : Context middle inputs := by
                simpa only [called,Outcome.state] using context.build expression
              have tailGrowth : Grows middle final := by
                simpa only [tail,Outcome.state] using
                  (InternedFreshOrdinaryFacts.buildMany_verified rest inputs middle next.normal.facts next.inputs).growth
              exact .cons ⟨before,middle,context,called,grows_trans tailGrowth growth⟩
                (ih middle next values final tail growth)

private theorem paired_calls (expressions : List (Syntax Symbol Guard))
    (leftInputs rightInputs : List (Value Symbol Guard)) (execution : State Symbol Guard)
    (references : Reference → Reference → Prop) (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (cases : ∀ child ∈ expressions,
      ∀ leftEntry rightEntry, Context leftEntry leftInputs → Context rightEntry rightInputs →
      ∀ first leftAfter second rightAfter,
        build child leftInputs leftEntry = .done first leftAfter →
        build child rightInputs rightEntry = .done second rightAfter →
        Grows leftAfter execution → Grows rightAfter execution → RootMatch references values first second)
    (first second : List (Value Symbol Guard))
    (firstCalls : All₂ (fun expression output => ∃ entry returned,
      Context entry leftInputs ∧ build expression leftInputs entry = .done output returned ∧ Grows returned execution)
      expressions first)
    (secondCalls : All₂ (fun expression output => ∃ entry returned,
      Context entry rightInputs ∧ build expression rightInputs entry = .done output returned ∧ Grows returned execution)
      expressions second) : All₂ (RootMatch references values) first second := by
  induction firstCalls generalizing second with
  | nil => cases secondCalls; exact .nil
  | @cons expression first expressions firsts head tail ih =>
      cases secondCalls with
      | cons other remaining =>
          obtain ⟨leftEntry,leftAfter,leftContext,firstDone,firstGrowth⟩ := head
          obtain ⟨rightEntry,rightAfter,rightContext,secondDone,secondGrowth⟩ := other
          exact .cons (cases expression List.mem_cons_self leftEntry rightEntry leftContext rightContext
            first leftAfter _ rightAfter firstDone secondDone firstGrowth secondGrowth)
            (ih (fun child member => cases child (List.mem_cons_of_mem _ member)) _ remaining)

private theorem union_parts (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before inputs) (result : Value Symbol Guard)
    (after : State Symbol Guard) (actual : build (.union expressions) inputs before = .done result after) :
    ∃ outputs middle,
      buildMany expressions inputs before = .done outputs middle ∧ Context middle inputs ∧
      Values middle outputs ∧ run (makeUnion outputs) middle = (result,after) ∧ Grows middle after := by
  cases called : buildMany expressions inputs before with
  | pending key current => simp only [build,called,Outcome.bind] at actual; cases actual
  | done outputs middle =>
      have made : run (makeUnion outputs) middle = (result,after) :=
        Prod.ext (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).1
          (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).2
      have next : Context middle inputs := by
        simpa only [called,Outcome.state] using context.many expressions
      exact ⟨outputs,middle,rfl,next,
        (InternedFreshOrdinaryFacts.buildMany_verified expressions inputs before context.normal.facts context.inputs).result
          outputs middle called,made,
        by simpa only [made] using (run_correct (makeUnion outputs) middle next.normal.facts.coherent.valid).2⟩

/-- Indexed strict member root cases derive the actual union publication's body hypothesis. -/
theorem union (event : Publication (Symbol := Symbol) (Guard := Guard))
    (expressions : List (Syntax Symbol Guard)) (shape : event.expression = .union expressions)
    (depth : Nat) (view common : State Symbol Guard)
    (replacement : Value Symbol Guard) (environment : Environment Symbol Guard)
    (members :
      let localInputs := .inr (.inl ()) ::
        (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput
      let firstNames : Sum Unit Unit → Reference := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) (fun _ : Unit => .depth)
      let secondNames : Sum Unit Unit → Reference := Sum.elim (fun _ : Unit => .interned event.entry.identity) (fun _ : Unit => .depth)
      ∀ (index : Nat) (child : Syntax Symbol Guard), expressions[index]? = some child →
        sizeOf child < sizeOf event.expression →
      ∀ execution, Keeps common execution → Aliases child localInputs firstNames secondNames →
      ∀ before later, Context before (localInputs.map (input firstNames)) →
        Context later (localInputs.map (input secondNames)) →
      ∀ rawFirst rawHeap rawSecond rawLater,
        build child (localInputs.map (input firstNames)) before = .done rawFirst rawHeap →
        build child (localInputs.map (input secondNames)) later = .done rawSecond rawLater →
        Grows rawHeap execution → Grows rawLater execution →
        RootMatch (NamePair (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity))
          (Executions (depth+1) view execution (shared event replacement replacement environment)
            (shared event replacement replacement environment)) rawFirst rawSecond) :
    BodyIH depth view event replacement environment common := by
  intro execution kept
  let localInputs := .inr (.inl ()) ::
    (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput
  let firstNames : Sum Unit Unit → Reference := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) (fun _ : Unit => .depth)
  let secondNames : Sum Unit Unit → Reference := Sum.elim (fun _ : Unit => .interned event.entry.identity) (fun _ : Unit => .depth)
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
  intro _ aliases before later firstContext secondContext rawFirst rawHeap rawSecond rawLater firstRaw secondRaw firstGrowth secondGrowth
  obtain ⟨left,leftMiddle,leftMany,leftContext,leftAvailable,leftMade,leftGrowth⟩ :=
    union_parts expressions _ before firstContext rawFirst rawHeap (by simpa only [shape] using firstRaw)
  obtain ⟨right,rightMiddle,rightMany,rightContext,rightAvailable,rightMade,rightGrowth⟩ :=
    union_parts expressions _ later secondContext rawSecond rawLater (by simpa only [shape] using secondRaw)
  have childCases : ∀ child ∈ expressions,
      ∀ leftEntry rightEntry, Context leftEntry (localInputs.map (input firstNames)) →
        Context rightEntry (localInputs.map (input secondNames)) →
      ∀ first leftAfter second rightAfter,
        build child (localInputs.map (input firstNames)) leftEntry = .done first leftAfter →
        build child (localInputs.map (input secondNames)) rightEntry = .done second rightAfter →
        Grows leftAfter execution → Grows rightAfter execution →
        RootMatch (NamePair (.uninterned (ordinaryLevel event.depth)) (.interned event.entry.identity))
          (Executions (depth+1) view execution (shared event replacement replacement environment)
            (shared event replacement replacement environment)) first second := by
    intro child member
    obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
    have smaller : sizeOf child < sizeOf event.expression := by
      have strict := List.sizeOf_lt_of_mem member
      simp only [shape,Syntax.union.sizeOf_spec]
      omega
    exact members index child found smaller execution kept
      (member_aliases expressions localInputs firstNames secondNames (by simpa only [shape] using aliases) child member)
  have matched := paired_calls expressions _ _ execution _ _ childCases left right
    (many_calls expressions _ before firstContext left leftMiddle execution leftMany (grows_trans leftGrowth firstGrowth))
    (many_calls expressions _ later secondContext right rightMiddle execution rightMany (grows_trans rightGrowth secondGrowth))
  have raw := SourceCurrentUsedBinderRootAlternatives.union_ordered _ _ left right leftMiddle rightMiddle
    leftContext.normal rightContext.normal leftAvailable rightAvailable matched
  rw [leftMade,rightMade] at raw
  exact raw

end MicroCFTA.SourceCurrentPublicationBodySourceCases
