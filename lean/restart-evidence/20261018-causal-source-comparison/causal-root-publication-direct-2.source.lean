import MicroCFTA.SourceCurrentCausalPublicationProfile
import MicroCFTA.SourceCurrentStoredMuRootContract
import MicroCFTA.SourceCurrentStoredRootDeletionErasure

/-!
# Original root contracts for actual publication candidates

The source law compares the two actual raw callbacks at the body reader.
The reader contains only earlier payload contracts. Actual self filtering
adds the local cut. Normalized callback profiles and paired free names
also preserve the exact standalone-reference tag.
-/
namespace MicroCFTA.SourceCurrentCausalPublicationRootContract
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryLiveInputs (input liftInput)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent profile Single)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentStoredMuProfileContract (shadow)
open SourceCurrentStoredMuRootContract (tag bare Correct)
open SourceCurrentPublicationHeapInduction (Heap)
open SourceCurrentStoredRootDeletion (deleted)

private theorem tagged_pair (firstOwn secondOwn first second : Reference)
    (paired : SourceCurrentUsedBinderAliasTransport.NamePair firstOwn secondOwn first second) :
    tag firstOwn first = tag secondOwn second := by
  rcases paired with ⟨rfl,rfl⟩ | ⟨rfl,firstDifferent,secondDifferent⟩
  · simp only [tag,ite_true]
  · simp only [tag,firstDifferent,secondDifferent,ite_false]

private theorem reference_match (firstOwn secondOwn : Reference)
    (first second : Value Symbol Guard) (secondState : State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal secondState) (available : Available secondState second)
    (opacity : profile first = none ↔ profile second = none)
    (forward : ∀ name ∈ first.free, ∃ other ∈ second.free, tag firstOwn name = tag secondOwn other)
    (backward : ∀ other ∈ second.free, ∃ name ∈ first.free, tag firstOwn name = tag secondOwn other)
    (name : Reference) (selected : first = .reference name) :
    ∃ other, second = .reference other ∧ tag firstOwn name = tag secondOwn other := by
  subst first
  obtain ⟨other,member,matched⟩ := forward name (by simp only [Value.free,List.mem_singleton])
  cases found : profile second with
  | none =>
      have impossible := opacity.mpr found
      simp only [profile,reduceCtorEq] at impossible
  | some names =>
      have reflected := InternedRootProfileReflection.pure_free second secondState
        normal.facts.coherent available names found
      have single : Single other ((profile second).getD []) := by
        rw [found,Option.getD_some]
        constructor
        · exact (reflected other).mp member
        · intro another included
          obtain ⟨original,present,same⟩ := backward another ((reflected another).mpr included)
          have originalEq : original = name := by simpa only [Value.free,List.mem_singleton] using present
          subst original
          exact SourceCurrentStoredMuRootContract.tag_injective secondOwn (same.symm.trans matched)
      exact ⟨other,(InternedRootProfileReflection.profile_single_iff second secondState normal available other).mp single,
        matched⟩

private theorem bare_match (firstOwn secondOwn : Reference) (first second : Value Symbol Guard)
    (firstState secondState : State Symbol Guard)
    (firstNormal : InternedStoredMuOrigins.Normal firstState)
    (secondNormal : InternedStoredMuOrigins.Normal secondState)
    (firstAvailable : Available firstState first) (secondAvailable : Available secondState second)
    (opacity : profile first = none ↔ profile second = none)
    (forward : ∀ name ∈ first.free, ∃ other ∈ second.free, tag firstOwn name = tag secondOwn other)
    (backward : ∀ other ∈ second.free, ∃ name ∈ first.free, tag firstOwn name = tag secondOwn other) :
    bare firstOwn first = bare secondOwn second := by
  have one := reference_match firstOwn secondOwn first second secondState secondNormal secondAvailable
    opacity forward backward
  have two := reference_match secondOwn firstOwn second first firstState firstNormal firstAvailable
    opacity.symm
    (fun name member => by
      obtain ⟨other,present,same⟩ := backward name member
      exact ⟨other,present,same.symm⟩)
    (fun other member => by
      obtain ⟨name,present,same⟩ := forward other member
      exact ⟨name,present,same.symm⟩)
  cases first with
  | reference name =>
      obtain ⟨other,rfl,matched⟩ := one name rfl
      exact congrArg some matched
  | empty | node | union | mu =>
      cases second with
      | reference name => obtain ⟨other,impossible,_⟩ := two name rfl; cases impossible
      | empty | node | union | mu => rfl

private theorem callback_profile [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (name : Reference) (before after : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context before environment)
    (argument : Available before (.reference name)) (value : Value Symbol Guard)
    (actual : InternedFreshOrdinaryFacts.callback expression environment name before = .done value after) :
    Equivalent (profile value) (InternedRootProfile.normalize name
      (InternedProfileSemantics.evaluate expression (some [name] :: environment.map profile))) := by
  have localContext := context.local name argument
  have checked := InternedFreshOrdinaryProfileExecutionFacts.callback_checked expression environment name before
    context.normal localContext.inputs (by
      simpa only [List.map_cons,profile] using
        InternedFreshOrdinaryProfiles.build_profile expression (.reference name :: environment) before
          context.normal localContext.inputs context.profiles)
  exact checked.result value after actual

private theorem callback_opacity [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    profile event.body = none ↔ profile event.ordinary = none := by
  obtain ⟨depthContext,cutContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have bodyArgument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have ordinaryArgument := InternedNestedProvenance.ordinary_available (Symbol := Symbol) (Guard := Guard)
    event.afterDepth (ordinaryLevel event.depth)
  have first := callback_profile event.expression event.environment (.interned event.entry.identity)
    event.allocated event.afterBody bodyContext.base bodyArgument event.body event.bodyDone
  have second := callback_profile event.expression event.environment (.uninterned (ordinaryLevel event.depth))
    event.afterDepth event.cut depthContext.base ordinaryArgument event.ordinary event.ordinaryDone
  rcases InternedProfileCallbackForm.callback_form event.expression (event.environment.map profile) with hidden |
    ⟨captured,uses,pure⟩
  · rw [hidden,InternedRootProfile.normalize] at first second
    exact first.1.trans second.1.symm
  · have bodyPure := InternedTwoProbeProfiles.normalize_same (.interned event.entry.identity)
      (pure (.interned event.entry.identity))
    have ordinaryPure := InternedTwoProbeProfiles.normalize_same (.uninterned (ordinaryLevel event.depth))
      (pure (.uninterned (ordinaryLevel event.depth)))
    have firstCompared := InternedProfileEquivalence.trans first bodyPure
    have secondCompared := InternedProfileEquivalence.trans second ordinaryPure
    exact firstCompared.1.trans (by simpa only [InternedRootProfile.probe,InternedRootProfile.normalize,
      reduceCtorEq] using secondCompared.1.symm)

private theorem combined_tag (own : Reference) (cuts : Option Reference → Bool) :
    (fun name => cuts (tag own name) || (name == own)) =
      (fun name => cuts (some name) || (name == own)) := by
  funext name
  by_cases same : name = own
  · subst name; simp only [beq_self_eq_true,Bool.or_true]
  · simp only [tag,same,ite_false]

/-- The strict source law and actual earlier history prove the full candidate root contract. -/
theorem publication [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (source : SourceCurrentCausalSourceRootLaw.Law event.expression)
    (earlier : Heap SourceCurrentStoredMuProfileContract.Correct event.afterBody)
    (history : History empty event.afterBody) :
    Correct event.entry event.body event.depth event.ordinary := by
  obtain ⟨rawOrdinary,afterRawOrdinary,rawBody,afterRawBody,ordinaryDone,ordinaryFilter,
    bodyDone,bodyFilter,ordinaryGrowth,bodyGrowth,depthContext,allocatedContext⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  let own : Reference := .interned event.entry.identity
  let ordinary : Reference := .uninterned (ordinaryLevel event.depth)
  let inputs : List (Sum (Value Symbol Guard) Unit) := event.environment.map Sum.inl
  let names : Unit → Reference := fun _ => .depth
  let locals : List (Sum (Value Symbol Guard) (Sum Unit Unit)) := .inr (.inl ()) :: inputs.map liftInput
  let bodyNames : Sum Unit Unit → Reference := Sum.elim (fun _ => own) names
  let ordinaryNames : Sum Unit Unit → Reference := Sum.elim (fun _ => ordinary) names
  have captured : inputs.map (input names) = event.environment := by
    simp only [inputs,List.map_map]
    change event.environment.map id = event.environment
    simp only [List.map_id_fun,id_eq]
  have bodyInputs : locals.map (input bodyNames) = .reference own :: event.environment := by
    simp only [locals,inputs,List.map_cons,List.map_map]
    change .reference own :: event.environment.map id = _
    simp only [List.map_id_fun,id_eq]
  have ordinaryInputs : locals.map (input ordinaryNames) = .reference ordinary :: event.environment := by
    simp only [locals,inputs,List.map_cons,List.map_map]
    change .reference ordinary :: event.environment.map id = _
    simp only [List.map_id_fun,id_eq]
  have bodyArgument : Available event.allocated (.reference own) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have ordinaryArgument := InternedNestedProvenance.ordinary_available (Symbol := Symbol) (Guard := Guard)
    event.afterDepth (ordinaryLevel event.depth)
  have bodyLocal := allocatedContext.local own bodyArgument
  have ordinaryLocal := depthContext.local ordinary ordinaryArgument
  have rawBodyContext : Context afterRawBody (.reference own :: event.environment) := by
    simpa only [own,bodyDone,Outcome.state] using bodyLocal.build event.expression
  have rawOrdinaryContext : Context afterRawOrdinary (.reference ordinary :: event.environment) := by
    simpa only [ordinary,ordinaryDone,Outcome.state] using ordinaryLocal.build event.expression
  have rawBodyAvailable := (InternedFreshOrdinaryFacts.build_verified event.expression _ event.allocated
    bodyLocal.base.normal.facts bodyLocal.base.inputs).result rawBody afterRawBody bodyDone
  have rawOrdinaryAvailable := (InternedFreshOrdinaryFacts.build_verified event.expression _ event.afterDepth
    ordinaryLocal.base.normal.facts ordinaryLocal.base.inputs).result rawOrdinary afterRawOrdinary ordinaryDone
  have ordinaryFresh := SourceCurrentNativeNormalizationFreshness.ordinary event.expression inputs names
    event.before event.afterDepth (captured ▸ event.context.base) event.depth (captured ▸ event.depthDone)
  have ownFresh := SourceCurrentNativeNormalizationFreshness.reserved (.binder true event.expression)
    inputs names event.cut (captured ▸ cutContext.base) event.key event.missing
  have localAliases : ∀ label ∈ SourceCurrentNativeNormalizationInputs.support (.binder true event.expression) inputs,
      Sum.elim id names label = own ↔ Sum.elim id names label = ordinary := by
    intro label member
    constructor
    · intro same
      exact False.elim (ownFresh (List.mem_map.mpr ⟨label,member,same⟩))
    · intro same
      exact False.elim (ordinaryFresh (List.mem_map.mpr ⟨label,member,same⟩))
  have aliases : SourceCurrentUsedBinderAliasTransport.Aliases event.expression locals bodyNames ordinaryNames := by
    intro first firstMember second secondMember
    exact (SourceCurrentUsedBinderAliasTransport.publication event first firstMember second secondMember).symm
  have bareParity := SourceCurrentPublicationBareParity.bare event
  constructor
  · intro assignment replacement cuts
    by_cases bodyBare : event.body = .reference own
    · have ordinaryBare := bareParity.mp bodyBare
      rw [bodyBare,ordinaryBare]
      simp only [deleted,own,ordinary,tag,ite_true,shadow]
      exact InternedProfileEquivalence.refl _
    · have ordinaryNotBare : event.ordinary ≠ .reference ordinary := fun same => bodyBare (bareParity.mpr same)
      have cutCompatible := SourceCurrentScopedDeletionInputs.extend true event.expression inputs names names
        (fun name => cuts (some name)) (fun name => cuts (some name))
        ⟨fun _ _ => rfl,fun _ _ => rfl⟩ own ordinary localAliases
      have profiles := SourceCurrentScopedProfileInputs.publication event inputs names captured assignment replacement
      have compared := source event.afterBody locals bodyNames ordinaryNames
        (shadow own replacement assignment) (shadow ordinary replacement assignment)
        (fun name => cuts (some name) || (name == own))
        (fun name => cuts (some name) || (name == ordinary))
        event.allocated afterRawBody event.afterDepth afterRawOrdinary rawBody rawOrdinary
        (bodyInputs ▸ bodyLocal) (ordinaryInputs ▸ ordinaryLocal) aliases profiles cutCompatible
        (by simpa only [bodyInputs] using bodyDone) (by simpa only [ordinaryInputs] using ordinaryDone)
        bodyGrowth ordinaryGrowth earlier history
      have first := SourceCurrentStoredRootDeletionErasure.erased_filter
        (fun name => cuts (tag own name)) own rawBody (shadow own replacement assignment) afterRawBody
        rawBodyContext.base.normal rawBodyAvailable
      have second := SourceCurrentStoredRootDeletionErasure.erased_filter
        (fun name => cuts (tag ordinary name)) ordinary rawOrdinary (shadow ordinary replacement assignment)
        afterRawOrdinary rawOrdinaryContext.base.normal rawOrdinaryAvailable
      rw [bodyFilter] at first
      rw [ordinaryFilter] at second
      have firstNotSelf : event.body.referenceOf ≠ .ref own := fun same =>
        bodyBare ((referenceOf_self_iff own event.body).mp same)
      have secondNotSelf : event.ordinary.referenceOf ≠ .ref ordinary := fun same =>
        ordinaryNotBare ((referenceOf_self_iff ordinary event.ordinary).mp same)
      simp only [SourceCurrentNativeCallbackErasure.eraseSelf,firstNotSelf,ite_false,combined_tag] at first
      simp only [SourceCurrentNativeCallbackErasure.eraseSelf,secondNotSelf,ite_false,combined_tag] at second
      exact InternedProfileEquivalence.trans first
        (InternedProfileEquivalence.trans compared (InternedProfileEquivalence.symm second))
  · have ordinaryAvailable := (InternedFreshOrdinaryFacts.callback_verified event.expression event.environment ordinary
      event.afterDepth depthContext.base.normal.facts ordinaryLocal.base.inputs).result
        event.ordinary event.cut event.ordinaryDone
    have bodyAvailable := (InternedFreshOrdinaryFacts.callback_verified event.expression event.environment own
      event.allocated allocatedContext.base.normal.facts bodyLocal.base.inputs).result
        event.body event.afterBody event.bodyDone
    have bodyContext : Context event.afterBody event.environment := by
      simpa only [own,event.bodyDone,Outcome.state] using allocatedContext.callback event.expression own bodyArgument
    have paired := SourceCurrentUsedBinderAliasTransport.publication_filtered event
    apply bare_match own ordinary event.body event.ordinary event.afterBody event.cut bodyContext.base.normal
      cutContext.base.normal bodyAvailable ordinaryAvailable (callback_opacity event)
    · intro name member
      obtain ⟨other,present,same⟩ := paired.2 name member
      exact ⟨other,present,(tagged_pair ordinary own other name same).symm⟩
    · intro other member
      obtain ⟨name,present,same⟩ := paired.1 other member
      exact ⟨name,present,(tagged_pair ordinary own other name same).symm⟩

end MicroCFTA.SourceCurrentCausalPublicationRootContract
