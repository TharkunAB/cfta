import MicroCFTA.SourceCurrentCausalSourceRootLaw
import MicroCFTA.SourceCurrentCausalPublicationHeapInduction
import MicroCFTA.InternedFilterSelfReference

/-!
# Parametric profiles for an actual publication candidate

The source comparison runs at the actual pre-publication body heap.
Its payload facts concern earlier records only. Exact root filtering and
bare-self parity then establish the new candidate's profile contract.
The source law remains explicit until its syntax induction is proved.
-/
namespace MicroCFTA.SourceCurrentCausalPublicationProfile
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryLiveInputs (input liftInput)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Equivalent)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentStoredMuProfileContract (Correct shadow)
open SourceCurrentPublicationHeapInduction (Heap)

/-- The strict source law and earlier heap facts prove the actual candidate before installation. -/
theorem publication [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard))
    (source : SourceCurrentCausalSourceRootLaw.Law event.expression)
    (earlier : Heap Correct event.afterBody) (history : History empty event.afterBody) :
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
  have cutCompatible := SourceCurrentScopedDeletionInputs.local_cuts true event.expression inputs names names
    own ordinary localAliases
  have bodySelf := InternedFilterSelfReference.filter_self_iff own rawBody afterRawBody
    rawBodyContext.base.normal.facts.coherent rawBodyContext.base.normal.flat rawBodyAvailable
  have ordinarySelf := InternedFilterSelfReference.filter_self_iff ordinary rawOrdinary afterRawOrdinary
    rawOrdinaryContext.base.normal.facts.coherent rawOrdinaryContext.base.normal.flat rawOrdinaryAvailable
  rw [bodyFilter] at bodySelf
  rw [ordinaryFilter] at ordinarySelf
  have bare : rawBody = .reference own ↔ rawOrdinary = .reference ordinary :=
    bodySelf.symm.trans ((SourceCurrentPublicationBareParity.bare event).trans ordinarySelf)
  have bareTests : (rawBody.referenceOf == .ref own) = (rawOrdinary.referenceOf == .ref ordinary) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact (referenceOf_self_iff own rawBody).trans (bare.trans (referenceOf_self_iff ordinary rawOrdinary).symm)
  intro assignment replacement
  have profiles := SourceCurrentScopedProfileInputs.publication event inputs names captured assignment replacement
  have aliases : SourceCurrentUsedBinderAliasTransport.Aliases event.expression locals bodyNames ordinaryNames := by
    intro first firstMember second secondMember
    exact (SourceCurrentUsedBinderAliasTransport.publication event first firstMember second secondMember).symm
  have compared := source event.afterBody locals bodyNames ordinaryNames
    (shadow own replacement assignment) (shadow ordinary replacement assignment)
    (fun name => name == own) (fun name => name == ordinary)
    event.allocated afterRawBody event.afterDepth afterRawOrdinary rawBody rawOrdinary
    (bodyInputs ▸ bodyLocal) (ordinaryInputs ▸ ordinaryLocal) aliases profiles cutCompatible
    (by simpa only [bodyInputs] using bodyDone) (by simpa only [ordinaryInputs] using ordinaryDone)
    bodyGrowth ordinaryGrowth earlier history
  have bodyProfile := SourceCurrentStoredRootDeletionConstruction.filter_profile own rawBody
    (shadow own replacement assignment) afterRawBody rawBodyContext.base.normal rawBodyAvailable
  have ordinaryProfile := SourceCurrentStoredRootDeletionConstruction.filter_profile ordinary rawOrdinary
    (shadow ordinary replacement assignment) afterRawOrdinary rawOrdinaryContext.base.normal rawOrdinaryAvailable
  rw [bodyFilter] at bodyProfile
  rw [ordinaryFilter] at ordinaryProfile
  rw [bareTests] at bodyProfile
  cases selected : rawOrdinary.referenceOf == .ref ordinary with
  | false =>
      simp only [selected,Bool.false_eq_true,ite_false] at bodyProfile ordinaryProfile
      exact InternedProfileEquivalence.trans bodyProfile
        (InternedProfileEquivalence.trans compared (InternedProfileEquivalence.symm ordinaryProfile))
  | true =>
      simp only [selected,ite_true,shadow] at bodyProfile ordinaryProfile
      exact InternedProfileEquivalence.trans bodyProfile (InternedProfileEquivalence.symm ordinaryProfile)

/-- Source comparison proves the payload contract through every actual construction prefix. -/
theorem build [DecidableEq (EdgeKey Symbol Guard)]
    (sources : ∀ expression : InternedNestedConstruction.Syntax Symbol Guard,
      SourceCurrentCausalSourceRootLaw.Law expression)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (history : History empty state) (initial : Heap Correct state) :
    Heap Correct (InternedFreshOrdinaryConstruction.build expression environment state).state := by
  apply SourceCurrentCausalPublicationHeapInduction.build Correct expression environment state context history initial
  intro event prefix _before _afterDepth _cut _allocated afterBody
  exact publication event (sources event.expression) afterBody prefix

/-- Empty tables derive the complete payload heap from the full source law. -/
theorem closed [DecidableEq (EdgeKey Symbol Guard)]
    (sources : ∀ expression : InternedNestedConstruction.Syntax Symbol Guard,
      SourceCurrentCausalSourceRootLaw.Law expression)
    (expression : InternedNestedConstruction.Syntax Symbol Guard) :
    Heap Correct (InternedFreshOrdinaryConstruction.build expression [] empty).state :=
  build sources expression [] empty SourceCurrentConstrainedCapSourceHistory.empty_context
    (.refl empty) (SourceCurrentPublicationHeapInduction.empty Correct)

end MicroCFTA.SourceCurrentCausalPublicationProfile
