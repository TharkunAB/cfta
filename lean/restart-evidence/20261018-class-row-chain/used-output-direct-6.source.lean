import MicroCFTA.SourceCurrentUsedBinderAliasTransport
import MicroCFTA.InternedActualProbeTags
import MicroCFTA.InternedRecordDepthCompletion
import MicroCFTA.SourceCurrentUsedBinderRootAlternatives
import MicroCFTA.SourceCurrentStoredReconstruction

/-!
# Actual source output tags through live lexical aliases

Full source execution reflects empty and bare-reference output tags.
Nested source binders and captured Depth aliases remain in scope.
The callback induction step constructs its actual calls. Its comparison
uses an explicit strict source-body induction hypothesis.
-/
namespace MicroCFTA.SourceCurrentUsedBinderOutputTags
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedFacts (filter_verified)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreshOrdinaryLiveInputs (input inputProfile input_profiles liftInput liftName local_inputs)
open SourceCurrentNativeNormalizationInputs (support)
open SourceCurrentUsedBinderAliasTransport (Scope Aliases)
open InternedRootProfile (profile Single)
open InternedBinderProtocol (Reference)
variable {Atom : Type}

private def rootProfile (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom)) :=
  InternedProfileSemantics.evaluate expression (inputs.map inputProfile)

private theorem shape_profiles (inputs : List (Sum (Value Symbol Guard) Atom)) :
    (inputs.map SourceCurrentNativeNormalizedComparison.inputShape).map InternedDepthSemanticProjections.profile =
      inputs.map inputProfile := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro selected member
  cases selected with
  | inl value =>
      exact (InternedDepthSemanticProjections.profile_map Sum.inl (InternedRecordDepthShape.shape value)).trans
        (congrArg (InternedProfileSemantics.mapNames Sum.inl) (InternedRecordDepthShape.shape_profile value))
  | inr atom => rfl

private theorem coherent_shapes (inputs : List (Sum (Value Symbol Guard) Atom)) :
    InternedDepthSemanticProjections.CoherentMany (inputs.map SourceCurrentNativeNormalizedComparison.inputShape) := by
  intro value member
  obtain ⟨selected, present, rfl⟩ := List.mem_map.mp member
  cases selected with
  | inl value => exact InternedDepthSemanticProjections.coherent_map Sum.inl _ (InternedRecordDepthShape.shape_coherent value)
  | inr atom => intro _; rfl

private theorem root_scoped (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before : State Symbol Guard) (context : Context before (inputs.map (input names)))
    (label : Sum Reference Atom) (member : label ∈ (rootProfile expression inputs).getD []) :
    label ∈ Scope expression inputs := by
  have projected : InternedDepthSemanticProjections.profile
      (SourceCurrentNativeNormalizedComparison.symbolic expression inputs) = rootProfile expression inputs := by
    rw [SourceCurrentNativeNormalizedComparison.symbolic,
      InternedDepthSemanticProjections.evaluate_profile expression _ (coherent_shapes inputs), shape_profiles]
    rfl
  rw [← projected, InternedDepthSemanticProjections.profile] at member
  have root : label ∈ (SourceCurrentNativeNormalizedComparison.symbolic expression inputs).roots := by
    split at member
    · simp only [Option.getD_none, List.not_mem_nil] at member
    · exact member
  apply List.mem_cons_of_mem
  apply (SourceCurrentNativeNormalizedComparison.symbolic_free_support expression inputs names before context label).mp
  exact List.mem_append_left _ root

private theorem output_profile [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names))) (value : Value Symbol Guard)
    (actual : build expression (inputs.map (input names)) before = .done value after) :
    InternedRootProfile.Equivalent (profile value)
      (InternedProfileSemantics.mapNames (Sum.elim id names) (rootProfile expression inputs)) := by
  have observed := (InternedFreshOrdinaryProfiles.build_profile expression _ before context.normal context.inputs context.profiles).result
    value after actual
  rw [input_profiles, InternedProfileSemantics.evaluate_map] at observed
  exact observed

private theorem output_context [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before after : State Symbol Guard) (context : Context before environment) (value : Value Symbol Guard)
    (actual : build expression environment before = .done value after) :
    Context after environment ∧ Available after value := by
  exact ⟨by simpa only [actual, Outcome.state] using context.build expression,
    (build_verified expression environment before context.normal.facts context.inputs).result value after actual⟩

private theorem single_map (labels : List (Sum Reference Atom))
    (firstNames secondNames : Atom → Reference) (firstOwn secondOwn : Reference)
    (aliases : ∀ label ∈ labels,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) :
    Single firstOwn (labels.map (Sum.elim id firstNames)) ↔
      Single secondOwn (labels.map (Sum.elim id secondNames)) := by
  constructor
  · rintro ⟨member, unique⟩
    obtain ⟨label, present, same⟩ := List.mem_map.mp member
    refine ⟨List.mem_map.mpr ⟨label, present, (aliases label present).mp same⟩, ?_⟩
    intro name member
    obtain ⟨other, included, rfl⟩ := List.mem_map.mp member
    exact (aliases other included).mp (unique _ (List.mem_map.mpr ⟨other, included, rfl⟩))
  · rintro ⟨member, unique⟩
    obtain ⟨label, present, same⟩ := List.mem_map.mp member
    refine ⟨List.mem_map.mpr ⟨label, present, (aliases label present).mpr same⟩, ?_⟩
    intro name member
    obtain ⟨other, included, rfl⟩ := List.mem_map.mp member
    exact (aliases other included).mpr (unique _ (List.mem_map.mpr ⟨other, included, rfl⟩))

/-- Equal live alias tests reflect the exact bare-reference tag of both actual outputs. -/
theorem bare [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstOwn secondOwn : Reference)
    (before after later final : State Symbol Guard)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (first second : Value Symbol Guard)
    (firstDone : build expression (inputs.map (input firstNames)) before = .done first after)
    (secondDone : build expression (inputs.map (input secondNames)) later = .done second final)
    (aliases : ∀ label ∈ Scope expression inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) :
    first = .reference firstOwn ↔ second = .reference secondOwn := by
  have firstProfile := output_profile expression inputs firstNames before after firstContext first firstDone
  have secondProfile := output_profile expression inputs secondNames later final secondContext second secondDone
  have firstOutput := output_context expression _ before after firstContext first firstDone
  have secondOutput := output_context expression _ later final secondContext second secondDone
  rw [← InternedRootProfileReflection.profile_single_iff first after firstOutput.1.normal firstOutput.2 firstOwn,
    ← InternedRootProfileReflection.profile_single_iff second final secondOutput.1.normal secondOutput.2 secondOwn,
    InternedActualProbeTags.single_equivalent firstOwn firstProfile,
    InternedActualProbeTags.single_equivalent secondOwn secondProfile]
  cases computed : rootProfile expression inputs with
  | none => simp only [InternedProfileSemantics.mapNames, Option.map_none, Option.getD_none, Single, List.not_mem_nil, false_and]
  | some labels =>
      simp only [InternedProfileSemantics.mapNames, Option.map_some, Option.getD_some]
      apply single_map labels firstNames secondNames firstOwn secondOwn
      intro label member
      exact aliases label (root_scoped expression inputs firstNames before firstContext label (by simpa only [computed, Option.getD_some] using member))

/-- A scoped lexical label needs only the existing live alias relation. -/
theorem scoped_bare [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (label : Sum Reference Atom)
    (member : label ∈ Scope expression inputs) (aliases : Aliases expression inputs firstNames secondNames)
    (before after later final : State Symbol Guard)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (first second : Value Symbol Guard)
    (firstDone : build expression (inputs.map (input firstNames)) before = .done first after)
    (secondDone : build expression (inputs.map (input secondNames)) later = .done second final) :
    first = .reference (Sum.elim id firstNames label) ↔ second = .reference (Sum.elim id secondNames label) :=
  bare expression inputs firstNames secondNames _ _ before after later final firstContext secondContext
    first second firstDone secondDone (fun other present => aliases other present label member)

/-- Captured aliases with Depth preserve exact bare Depth outputs. -/
theorem depth_bare [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (aliases : Aliases expression inputs firstNames secondNames)
    (before after later final : State Symbol Guard)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (first second : Value Symbol Guard)
    (firstDone : build expression (inputs.map (input firstNames)) before = .done first after)
    (secondDone : build expression (inputs.map (input secondNames)) later = .done second final) :
    first = .reference .depth ↔ second = .reference .depth :=
  scoped_bare expression inputs firstNames secondNames (.inl .depth) List.mem_cons_self aliases
    before after later final firstContext secondContext first second firstDone secondDone

/-- Source empty outputs agree under arbitrary assignments, with no freshness premise. -/
theorem empty [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (before after later final : State Symbol Guard)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (first second : Value Symbol Guard)
    (firstDone : build expression (inputs.map (input firstNames)) before = .done first after)
    (secondDone : build expression (inputs.map (input secondNames)) later = .done second final) :
    first = .empty ↔ second = .empty := by
  have firstProfile := output_profile expression inputs firstNames before after firstContext first firstDone
  have secondProfile := output_profile expression inputs secondNames later final secondContext second secondDone
  have firstOutput := output_context expression _ before after firstContext first firstDone
  have secondOutput := output_context expression _ later final secondContext second secondDone
  rw [← InternedRootProfileNode.profile_empty_iff first after firstOutput.1.normal.proper firstOutput.2,
    ← InternedRootProfileNode.profile_empty_iff second final secondOutput.1.normal.proper secondOutput.2,
    InternedProfileComposition.empty_same firstProfile, InternedProfileComposition.empty_same secondProfile]
  cases computed : rootProfile expression inputs with
  | none => simp only [InternedProfileSemantics.mapNames, Option.map_none, reduceCtorEq]
  | some labels => simp only [InternedProfileSemantics.mapNames, Option.map_some, Option.some.injEq, List.map_eq_nil_iff]

private theorem scope_body (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (label : Sum Reference (Sum Unit Atom))
    (member : label ∈ Scope body (.inr (.inl ()) :: inputs.map liftInput)) :
    label = .inr (.inl ()) ∨ ∃ old ∈ Scope (.binder true body) inputs, label = liftName (.inr old) := by
  rcases List.mem_cons.mp member with rfl | member
  · exact Or.inr ⟨.inl .depth, List.mem_cons_self, rfl⟩
  · cases label with
    | inl name =>
        exact Or.inr ⟨.inl name, List.mem_cons_of_mem _
          ((SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inl name)).mp member), rfl⟩
    | inr selected =>
        cases selected with
        | inl token => cases token; exact Or.inl rfl
        | inr atom =>
            exact Or.inr ⟨.inr atom, List.mem_cons_of_mem _
              ((SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inr atom)).mp member), rfl⟩

private theorem local_tests (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstOwn secondOwn : Reference)
    (aliases : ∀ label ∈ Scope (.binder true body) inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) :
    ∀ label ∈ Scope body (.inr (.inl ()) :: inputs.map liftInput),
      Sum.elim id (Sum.elim (fun _ : Unit => firstOwn) firstNames) label = firstOwn ↔
        Sum.elim id (Sum.elim (fun _ : Unit => secondOwn) secondNames) label = secondOwn := by
  intro label member
  rcases scope_body body inputs label member with rfl | ⟨old, present, rfl⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · cases old with
    | inl name => exact aliases (.inl name) present
    | inr atom => exact aliases (.inr atom) present

/-- The induction premise covers only syntax strictly smaller than the enclosing binder. -/
def StrictBodyIH [DecidableEq (EdgeKey Symbol Guard)]
    (whole : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (references : Reference → Reference → Prop)
    (values : Value Symbol Guard → Value Symbol Guard → Prop) : Prop :=
  ∀ child : Syntax Symbol Guard, sizeOf child < sizeOf whole →
    Aliases child inputs firstNames secondNames →
    ∀ before later : State Symbol Guard,
      Context before (inputs.map (input firstNames)) → Context later (inputs.map (input secondNames)) →
    ∀ first after second final,
      build child (inputs.map (input firstNames)) before = .done first after →
      build child (inputs.map (input secondNames)) later = .done second final →
      SourceCurrentUsedBinderRootAlternatives.RootMatch references values first second

private theorem source_keeps [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (before after : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready before)
    (available : InternedNestedProvenance.Values before inputs) (value : Value Symbol Guard)
    (actual : build expression inputs before = .done value after) : SourceEqualityRequiredCache.Keeps before after := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic inputs available
  have checked := build_verified expression inputs before ready.semantic.1.normal.facts available
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source expression inputs before ready.semantic available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs before
      ready.semantic.1.normal.facts.coherent.valid ready.covered value after actual
  · simpa only [actual,Outcome.state] using
      (InternedOpenDepthExecution.build_depth expression inputs before context ready.semantic.2 ready.depth).heap
  · simpa only [actual,Outcome.state] using checked.growth
  · simpa only [actual,Outcome.state] using checked.history

private theorem filter_keeps [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready state) (available : Available state value) :
    SourceEqualityRequiredCache.Keeps state (run (withoutSelfReference name value) state).2 := by
  have facts := ready.semantic.1.normal.facts
  have checked := filter_verified name value state facts available
  have old := InternedStoredMuOrigins.filter_noNewMu name value state
  have normal := InternedFreshOrdinaryNormal.filter_normal name value state ready.semantic.1.normal available
  exact ⟨⟨SourceRecursiveIntersectionSemanticHeap.preserve state _ ready.semantic normal old,
    InternedNestedCoverage.run_covered _ state facts.coherent.valid ready.covered,
    InternedOpenDepthReadback.preserve state _ ready.depth old⟩, checked.growth, checked.history⟩

private theorem callback_complete [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (argument : Reference)
    (before : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready before)
    (available : InternedNestedProvenance.Values before environment)
    (argumentAvailable : Available before (.reference argument)) :
    ∃ raw rawHeap value after,
      build body (.reference argument :: environment) before = .done raw rawHeap ∧
      run (withoutSelfReference argument raw) rawHeap = (value, after) ∧
      callback body environment argument before = .done value after ∧
      SourceEqualityRequiredCache.Keeps before after ∧ Available after value ∧
      Nonempty (SourceCurrentNativeMuPublication.History before after) ∧
      Context rawHeap (.reference argument :: environment) ∧ Available rawHeap raw := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic environment available
  have localContext := context.local argument argumentAvailable
  obtain ⟨raw, rawHeap, done⟩ := InternedRecordDepthCompletion.source_complete body _ before localContext ready.semantic.2 ready.covered
  have rawKept := source_keeps body _ before rawHeap ready localContext.inputs raw done
  have rawAvailable := (build_verified body _ before localContext.normal.facts localContext.inputs).result raw rawHeap done
  let filtered := run (withoutSelfReference argument raw) rawHeap
  have filteredKept := filter_keeps argument raw rawHeap rawKept.ready rawAvailable
  have filteredAvailable := (filter_verified argument raw rawHeap rawKept.ready.semantic.1.normal.facts rawAvailable).result filtered.1 filtered.2 rfl
  obtain ⟨history⟩ := SourceCurrentNativeMuPublication.build_history body _ before ⟨localContext,ready.semantic.2⟩
  have rawHistory : SourceCurrentNativeMuPublication.History before rawHeap := by
    simpa only [done,Outcome.state] using history
  have finalHistory : SourceCurrentNativeMuPublication.History before filtered.2 :=
    .trans rawHistory (.retain _ _ (InternedStoredMuOrigins.filter_noNewMu argument raw rawHeap))
  refine ⟨raw,rawHeap,filtered.1,filtered.2,done,rfl,?_,rawKept.trans filteredKept,?_,⟨finalHistory⟩,?_,rawAvailable⟩
  · simp only [callback,done,Outcome.bind,InternedNestedConstruction.work,filtered]
  · exact filteredAvailable
  · simpa only [done,Outcome.state] using localContext.build body

/-- Strict body induction constructs both normalized callbacks and their matching actual root parts. -/
theorem callback_induction_step [DecidableEq (EdgeKey Symbol Guard)]
    (smart : Bool) (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstOwn secondOwn : Reference)
    (references : Reference → Reference → Prop) (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (aliases : Aliases (.binder true body) inputs firstNames secondNames)
    (localAliases : ∀ label ∈ Scope (.binder true body) inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn)
    (referenceLocal : ∀ first second, references first second → (first = firstOwn ↔ second = secondOwn))
    (strict : StrictBodyIH (.binder smart body) (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ : Unit => firstOwn) firstNames)
      (Sum.elim (fun _ : Unit => secondOwn) secondNames) references values)
    (before : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready before)
    (firstAvailable : InternedNestedProvenance.Values before (inputs.map (input firstNames)))
    (secondAvailable : InternedNestedProvenance.Values before (inputs.map (input secondNames)))
    (firstArgument : Available before (.reference firstOwn))
    (secondArgument : Available before (.reference secondOwn)) :
    ∃ first middle second after,
      callback body (inputs.map (input firstNames)) firstOwn before = .done first middle ∧
      callback body (inputs.map (input secondNames)) secondOwn middle = .done second after ∧
      SourceEqualityRequiredCache.Keeps before middle ∧ SourceEqualityRequiredCache.Keeps middle after ∧
      Available after first ∧ Available after second ∧
      Nonempty (SourceCurrentNativeMuPublication.History before middle) ∧
      Nonempty (SourceCurrentNativeMuPublication.History middle after) ∧
      (first = .reference firstOwn ↔ second = .reference secondOwn) ∧
      SourceCurrentUsedBinderRootAlternatives.RootMatch references values first second := by
  let localInputs := .inr (.inl ()) :: inputs.map liftInput
  let firstLabels := Sum.elim (fun _ : Unit => firstOwn) firstNames
  let secondLabels := Sum.elim (fun _ : Unit => secondOwn) secondNames
  obtain ⟨rawFirst,rawHeap,first,middle,firstRaw,firstFilter,firstDone,firstKept,firstKnown,firstHistory,firstRawContext,firstRawKnown⟩ :=
    callback_complete body _ firstOwn before ready firstAvailable firstArgument
  have secondInputs : InternedNestedProvenance.Values middle (inputs.map (input secondNames)) :=
    fun value member => firstKept.available value (secondAvailable value member)
  obtain ⟨rawSecond,rawLater,second,after,secondRaw,secondFilter,secondDone,secondKept,secondKnown,secondHistory,secondRawContext,secondRawKnown⟩ :=
    callback_complete body _ secondOwn middle firstKept.ready secondInputs (firstKept.available _ secondArgument)
  have firstContext : Context before (localInputs.map (input firstLabels)) := by
    rw [local_inputs]
    exact (SourceRecursiveIntersectionSemanticHeap.context before ready.semantic _ firstAvailable).local firstOwn firstArgument
  have secondContext : Context middle (localInputs.map (input secondLabels)) := by
    rw [local_inputs]
    exact (SourceRecursiveIntersectionSemanticHeap.context middle firstKept.ready.semantic _ secondInputs).local
      secondOwn (firstKept.available _ secondArgument)
  have firstActual : build body (localInputs.map (input firstLabels)) before = .done rawFirst rawHeap := by
    simpa only [localInputs,firstLabels,local_inputs] using firstRaw
  have secondActual : build body (localInputs.map (input secondLabels)) middle = .done rawSecond rawLater := by
    simpa only [localInputs,secondLabels,local_inputs] using secondRaw
  have rawBare := bare body localInputs firstLabels secondLabels firstOwn secondOwn before rawHeap middle rawLater
    firstContext secondContext rawFirst rawSecond firstActual secondActual
    (local_tests body inputs firstNames secondNames firstOwn secondOwn localAliases)
  have filteredBare : first = .reference firstOwn ↔ second = .reference secondOwn := by
    have firstSelf := InternedFilterSelfReference.filter_self_iff firstOwn rawFirst rawHeap
      firstRawContext.normal.facts.coherent firstRawContext.normal.flat firstRawKnown
    have secondSelf := InternedFilterSelfReference.filter_self_iff secondOwn rawSecond rawLater
      secondRawContext.normal.facts.coherent secondRawContext.normal.flat secondRawKnown
    rw [firstFilter] at firstSelf
    rw [secondFilter] at secondSelf
    exact firstSelf.trans (rawBare.trans secondSelf.symm)
  have rawMatch := strict body (by simp)
    (SourceCurrentUsedBinderAliasTransport.extend body inputs firstNames secondNames firstOwn secondOwn aliases localAliases)
    before middle firstContext secondContext rawFirst rawHeap rawSecond rawLater firstActual secondActual
  have filteredMatch := SourceCurrentUsedBinderRootAlternatives.filter references values firstOwn secondOwn
    rawFirst rawSecond rawHeap rawLater firstRawContext.normal secondRawContext.normal firstRawKnown secondRawKnown
    rawMatch referenceLocal rawBare
  rw [firstFilter,secondFilter] at filteredMatch
  exact ⟨first,middle,second,after,firstDone,secondDone,firstKept,secondKept,
    secondKept.available first firstKnown,secondKnown,firstHistory,secondHistory,filteredBare,filteredMatch⟩

/-- Strict source-body induction derives the actual publication's filtered output relation. -/
theorem publication_induction_step [DecidableEq (EdgeKey Symbol Guard)]
    (event : SourceCurrentNativeMuPublication.Publication (Symbol := Symbol) (Guard := Guard))
    (references : Reference → Reference → Prop) (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (referenceLocal : ∀ first second, references first second →
      (first = .uninterned (ordinaryLevel event.depth) ↔ second = .interned event.entry.identity))
    (strict : StrictBodyIH (.binder event.smart event.expression)
      (.inr (.inl ()) :: (event.environment.map (fun value => (Sum.inl value : Sum (Value Symbol Guard) Unit))).map liftInput)
      (Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) (fun _ : Unit => .depth))
      (Sum.elim (fun _ : Unit => .interned event.entry.identity) (fun _ : Unit => .depth)) references values) :
    SourceCurrentUsedBinderRootAlternatives.RootMatch references values event.ordinary event.body := by
  let inputs : List (Sum (Value Symbol Guard) Unit) := event.environment.map Sum.inl
  let names : Unit → Reference := fun _ => .depth
  let localInputs := .inr (.inl ()) :: inputs.map liftInput
  let firstNames := Sum.elim (fun _ : Unit => .uninterned (ordinaryLevel event.depth)) names
  let secondNames := Sum.elim (fun _ : Unit => .interned event.entry.identity) names
  change StrictBodyIH (.binder event.smart event.expression) localInputs firstNames secondNames references values at strict
  have fixed : inputs.map (input names) = event.environment := by
    simp [inputs,input,List.map_map,Function.comp_def]
  have instantiated (own : Reference) :
      localInputs.map (input (Sum.elim (fun _ : Unit => own) names)) = .reference own :: event.environment := by
    rw [local_inputs,fixed]
  obtain ⟨rawFirst,rawHeap,rawSecond,rawLater,firstRaw,firstFilter,secondRaw,secondFilter,_,_,firstEntry,secondEntry⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have bodyArgument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have firstContext := firstEntry.base.local (.uninterned (ordinaryLevel event.depth))
    (InternedNestedProvenance.ordinary_available _ _)
  have secondContext := secondEntry.base.local (.interned event.entry.identity) bodyArgument
  have rawMatch := strict event.expression (by simp) (SourceCurrentUsedBinderAliasTransport.publication event)
    event.afterDepth event.allocated
    (by simpa only [firstNames,instantiated] using firstContext)
    (by simpa only [secondNames,instantiated] using secondContext)
    rawFirst rawHeap rawSecond rawLater
    (by simpa only [firstNames,instantiated] using firstRaw)
    (by simpa only [secondNames,instantiated] using secondRaw)
  have firstReturned := output_context event.expression _ event.afterDepth rawHeap firstContext rawFirst firstRaw
  have secondReturned := output_context event.expression _ event.allocated rawLater secondContext rawSecond secondRaw
  have rawBare : rawFirst = .reference (.uninterned (ordinaryLevel event.depth)) ↔
      rawSecond = .reference (.interned event.entry.identity) := by
    have firstSelf := InternedFilterSelfReference.filter_self_iff _ rawFirst rawHeap
      firstReturned.1.normal.facts.coherent firstReturned.1.normal.flat firstReturned.2
    have secondSelf := InternedFilterSelfReference.filter_self_iff _ rawSecond rawLater
      secondReturned.1.normal.facts.coherent secondReturned.1.normal.flat secondReturned.2
    rw [firstFilter] at firstSelf
    rw [secondFilter] at secondSelf
    exact firstSelf.symm.trans ((SourceCurrentPublicationBareParity.bare event).symm.trans secondSelf)
  have filtered := SourceCurrentUsedBinderRootAlternatives.filter references values _ _ rawFirst rawSecond rawHeap rawLater
    firstReturned.1.normal secondReturned.1.normal firstReturned.2 secondReturned.2 rawMatch referenceLocal rawBare
  rw [firstFilter,secondFilter] at filtered
  exact filtered

end MicroCFTA.SourceCurrentUsedBinderOutputTags
