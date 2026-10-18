import MicroCFTA.SourceCurrentCausalSourceRootLaw
import MicroCFTA.SourceCurrentNativeRetainedRootDeletion
import MicroCFTA.SourceCurrentNativeUnusedRootShadow
import MicroCFTA.SourceCurrentUsedBinderOutputTags

/-!
# Causal root comparison for the source binder step

The strict original body supplies the induction hypothesis. Actual probes
choose the same retained or unused branch. Retained payloads use the old
contract at the common reader. Unused returns use its actual publication
history. No reader validity or future output comparison is assumed.
-/
namespace MicroCFTA.SourceCurrentCausalSourceBinderComparison
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedFreshOrdinaryLiveInputs (input liftInput liftName local_inputs)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceCurrentNativeNormalizationInputs (support)
open SourceCurrentStoredMuProfileContract (shadow)
open SourceCurrentStoredRootDeletion (deleted)
open SourceCurrentStoredMuTrackedProfile (erase)
open SourceCurrentCausalSourceRootLaw (Law)

private theorem scope_body (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (label : Sum Reference (Sum Unit Atom))
    (member : label ∈ Scope body (.inr (.inl ()) :: inputs.map liftInput)) :
    label = .inr (.inl ()) ∨ ∃ old ∈ Scope (.binder true body) inputs,
      label = liftName (.inr old) := by
  rcases List.mem_cons.mp member with rfl | member
  · exact Or.inr ⟨.inl .depth,List.mem_cons_self,rfl⟩
  · cases label with
    | inl name =>
        exact Or.inr ⟨.inl name,List.mem_cons_of_mem _
          ((SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inl name)).mp member),rfl⟩
    | inr selected =>
        cases selected with
        | inl token => cases token; exact Or.inl rfl
        | inr atom =>
            exact Or.inr ⟨.inr atom,List.mem_cons_of_mem _
              ((SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inr atom)).mp member),rfl⟩

private theorem local_tests (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstOwn secondOwn : Reference)
    (tests : ∀ label ∈ Scope (.binder true body) inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) :
    ∀ label ∈ Scope body (.inr (.inl ()) :: inputs.map liftInput),
      Sum.elim id (Sum.elim (fun _ : Unit => firstOwn) firstNames) label = firstOwn ↔
        Sum.elim id (Sum.elim (fun _ : Unit => secondOwn) secondNames) label = secondOwn := by
  intro label member
  rcases scope_body body inputs label member with rfl | ⟨old,present,rfl⟩
  · exact Iff.rfl
  · cases old with
    | inl name => exact tests (.inl name) present
    | inr atom => exact tests (.inr atom) present

private theorem erase_same (marker : Reference) {first second : Profile}
    (same : Equivalent first second) : Equivalent (erase marker first) (erase marker second) := by
  cases first with
  | none =>
      have other := same.1.mp rfl
      subst second
      exact InternedProfileEquivalence.refl _
  | some first =>
      cases second with
      | none => simp [Equivalent] at same
      | some second =>
          constructor
          · simp [erase]
          · intro name
            simp only [erase,Option.map_some,Option.getD_some,List.mem_filter,Bool.not_eq_true,beq_iff_eq]
            exact and_congr (same.2 name) Iff.rfl

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem unused_reduction (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryConstruction.build (.binder true body) environment before = .done value after)
    (reader : State Symbol Guard) (later : Grows after reader)
    (history : SourceCurrentNativeMuPublication.History empty reader)
    (depth : Value Symbol Guard) (afterDepth : State Symbol Guard)
    (ordinary : Value Symbol Guard) (cut : State Symbol Guard)
    (raw : Value Symbol Guard) (afterRaw : State Symbol Guard)
    (depthDone : callback body environment .depth before = .done depth afterDepth)
    (ordinaryDone : callback body environment (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut)
    (rawDone : InternedFreshOrdinaryConstruction.build body
      (.reference (.uninterned (ordinaryLevel depth)) :: environment) afterDepth = .done raw afterRaw)
    (unused : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false)
    (cuts : Reference → Bool) (assignment : Reference → Profile) :
    Equivalent (deleted cuts value assignment)
      (deleted (fun name => cuts name || (name == .uninterned (ordinaryLevel depth))) raw
        (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment)) := by
  obtain ⟨otherDepth,otherAfterDepth,otherOrdinary,otherCut,otherRaw,otherAfterRaw,
    otherDepthDone,otherOrdinaryDone,otherRawDone,_filter,_growth,_issued,reduced⟩ :=
    SourceCurrentNativeUnusedRootShadow.build body environment before context value after actual reader later history
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (depthDone.symm.trans otherDepthDone)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (ordinaryDone.symm.trans otherOrdinaryDone)
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj (rawDone.symm.trans otherRawDone)
  exact (reduced unused).2.2 cuts assignment

/-- The strict original-body law derives the complete binder law at the same causal reader. -/
theorem binder (smart : Bool) (body : Syntax Symbol Guard) (ih : Law body) : Law (.binder smart body) := by
  intro Atom reader inputs firstNames secondNames firstAssignment secondAssignment firstCuts secondCuts
    firstBefore firstAfter secondBefore secondAfter first second
    firstContext secondContext aliases profiles cuts firstDone secondDone firstGrowth secondGrowth heap history
  obtain ⟨firstDepth,firstAfterDepth,firstOrdinary,firstCut,firstRaw,firstAfterRaw,firstEntry,firstBody,
    firstDepthDone,firstOrdinaryDone,firstRawDone,firstFilter,firstRawGrowth,_firstIssued,
    _firstPresent,_firstReader,_firstCorrect,firstFinished,firstRetained⟩ :=
    SourceCurrentNativeRetainedRootDeletion.build smart body _ firstBefore firstContext first firstAfter firstDone
      reader firstGrowth heap
  obtain ⟨secondDepth,secondAfterDepth,secondOrdinary,secondCut,secondRaw,secondAfterRaw,secondEntry,secondBody,
    secondDepthDone,secondOrdinaryDone,secondRawDone,secondFilter,secondRawGrowth,_secondIssued,
    _secondPresent,_secondReader,_secondCorrect,secondFinished,secondRetained⟩ :=
    SourceCurrentNativeRetainedRootDeletion.build smart body _ secondBefore secondContext second secondAfter secondDone
      reader secondGrowth heap
  have sameUse := SourceCurrentNativeNormalizedComparison.probes_same body inputs firstNames secondNames
    firstBefore firstAfterDepth firstCut secondBefore secondAfterDepth secondCut
    firstContext.base secondContext.base firstContext.depth secondContext.depth
    firstDepth firstOrdinary secondDepth secondOrdinary
    firstDepthDone firstOrdinaryDone secondDepthDone secondOrdinaryDone
  let firstOwn : Reference := .uninterned (ordinaryLevel firstDepth)
  let secondOwn : Reference := .uninterned (ordinaryLevel secondDepth)
  have firstFresh : firstOwn ∉ (Scope (.binder true body) inputs).map (Sum.elim id firstNames) := by
    have fresh := SourceCurrentNativeNormalizationFreshness.ordinary body inputs firstNames
      firstBefore firstAfterDepth firstContext.base firstDepth firstDepthDone
    simpa only [Scope,List.map_cons,Sum.elim_inl,id_eq,List.mem_cons,reduceCtorEq,false_or] using fresh
  have secondFresh : secondOwn ∉ (Scope (.binder true body) inputs).map (Sum.elim id secondNames) := by
    have fresh := SourceCurrentNativeNormalizationFreshness.ordinary body inputs secondNames
      secondBefore secondAfterDepth secondContext.base secondDepth secondDepthDone
    simpa only [Scope,List.map_cons,Sum.elim_inl,id_eq,List.mem_cons,reduceCtorEq,false_or] using fresh
  have oldAliases : Aliases (.binder true body) inputs firstNames secondNames := by
    simpa only [Aliases,Scope,support,InternedFreeNameSemantics.evaluate] using aliases
  have oldProfiles : SourceCurrentScopedProfileInputs.Compatible (.binder true body) inputs
      firstNames secondNames firstAssignment secondAssignment := by
    simpa only [SourceCurrentScopedProfileInputs.Compatible,support,InternedFreeNameSemantics.evaluate] using profiles
  have tests : ∀ label ∈ Scope (.binder true body) inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn := by
    intro label member
    exact iff_of_false (fun same => firstFresh (List.mem_map.mpr ⟨label,member,same⟩))
      (fun same => secondFresh (List.mem_map.mpr ⟨label,member,same⟩))
  let localInputs := .inr (.inl ()) :: inputs.map liftInput
  let firstLocal := Sum.elim (fun _ : Unit => firstOwn) firstNames
  let secondLocal := Sum.elim (fun _ : Unit => secondOwn) secondNames
  have firstLocalInputs : localInputs.map (input firstLocal) = .reference firstOwn :: inputs.map (input firstNames) :=
    local_inputs firstOwn firstNames inputs
  have secondLocalInputs : localInputs.map (input secondLocal) = .reference secondOwn :: inputs.map (input secondNames) :=
    local_inputs secondOwn secondNames inputs
  have firstDepthContext : Context firstAfterDepth (inputs.map (input firstNames)) := by
    simpa only [firstDepthDone,Outcome.state] using firstContext.callback body .depth
      (InternedNestedProvenance.depth_available firstBefore)
  have secondDepthContext : Context secondAfterDepth (inputs.map (input secondNames)) := by
    simpa only [secondDepthDone,Outcome.state] using secondContext.callback body .depth
      (InternedNestedProvenance.depth_available secondBefore)
  have firstLocalContext : Context firstAfterDepth (localInputs.map (input firstLocal)) := by
    rw [firstLocalInputs]
    exact firstDepthContext.local firstOwn (InternedNestedProvenance.ordinary_available firstAfterDepth (ordinaryLevel firstDepth))
  have secondLocalContext : Context secondAfterDepth (localInputs.map (input secondLocal)) := by
    rw [secondLocalInputs]
    exact secondDepthContext.local secondOwn (InternedNestedProvenance.ordinary_available secondAfterDepth (ordinaryLevel secondDepth))
  have firstRawActual : InternedFreshOrdinaryConstruction.build body (localInputs.map (input firstLocal))
      firstAfterDepth = .done firstRaw firstAfterRaw := by simpa only [firstLocalInputs] using firstRawDone
  have secondRawActual : InternedFreshOrdinaryConstruction.build body (localInputs.map (input secondLocal))
      secondAfterDepth = .done secondRaw secondAfterRaw := by simpa only [secondLocalInputs] using secondRawDone
  have localAliases := SourceCurrentUsedBinderAliasTransport.extend_fresh body inputs firstNames secondNames
    firstOwn secondOwn oldAliases firstFresh secondFresh
  have localProfiles (replacement : Profile) := SourceCurrentScopedProfileInputs.extend body inputs firstNames secondNames
    firstAssignment secondAssignment oldProfiles firstOwn secondOwn replacement
    (fun label member => tests label (List.mem_cons_of_mem _ member))
  have localGrowthFirst := grows_trans firstRawGrowth firstGrowth
  have localGrowthSecond := grows_trans secondRawGrowth secondGrowth
  cases keep : (!smart || InternedFreshOrdinaryDepthHeap.usesLocal firstDepth firstOrdinary) with
  | false =>
      have smartTrue : smart = true := by cases smart <;> simp_all only [Bool.not_false,Bool.true_or,Bool.true_eq_false]
      subst smart
      have firstUnused : InternedFreshOrdinaryDepthHeap.usesLocal firstDepth firstOrdinary = false := by simpa using keep
      have secondUnused := sameUse ▸ firstUnused
      have firstReduced := unused_reduction body _ firstBefore firstContext first firstAfter firstDone reader firstGrowth history
        firstDepth firstAfterDepth firstOrdinary firstCut firstRaw firstAfterRaw
        firstDepthDone firstOrdinaryDone firstRawDone firstUnused firstCuts firstAssignment
      have secondReduced := unused_reduction body _ secondBefore secondContext second secondAfter secondDone reader secondGrowth history
        secondDepth secondAfterDepth secondOrdinary secondCut secondRaw secondAfterRaw
        secondDepthDone secondOrdinaryDone secondRawDone secondUnused secondCuts secondAssignment
      have compared := ih reader localInputs firstLocal secondLocal
        (shadow firstOwn (some []) firstAssignment) (shadow secondOwn (some []) secondAssignment)
        (fun name => firstCuts name || (name == firstOwn)) (fun name => secondCuts name || (name == secondOwn))
        firstAfterDepth firstAfterRaw secondAfterDepth secondAfterRaw firstRaw secondRaw
        firstLocalContext secondLocalContext localAliases (localProfiles (some []))
        (SourceCurrentScopedDeletionInputs.extend true body inputs firstNames secondNames firstCuts secondCuts cuts
          firstOwn secondOwn (fun label member => tests label (List.mem_cons_of_mem _ member)))
        firstRawActual secondRawActual localGrowthFirst localGrowthSecond heap history
      exact InternedProfileEquivalence.trans firstReduced
        (InternedProfileEquivalence.trans compared (InternedProfileEquivalence.symm secondReduced))
  | true =>
      have secondKeep : (!smart || InternedFreshOrdinaryDepthHeap.usesLocal secondDepth secondOrdinary) = true := by
        rw [← sameUse]; exact keep
      obtain ⟨firstShape,firstReduced⟩ := firstRetained keep
      obtain ⟨secondShape,secondReduced⟩ := secondRetained secondKeep
      obtain ⟨marker,firstFreshMarker,secondFreshMarker⟩ :=
        SourceCurrentNativeRetainedRootDeletion.fresh_pair firstBody secondBody firstAssignment secondAssignment
      have compared := ih reader localInputs firstLocal secondLocal
        (shadow firstOwn (some [marker]) firstAssignment) (shadow secondOwn (some [marker]) secondAssignment)
        (fun name => name == firstOwn) (fun name => name == secondOwn)
        firstAfterDepth firstAfterRaw secondAfterDepth secondAfterRaw firstRaw secondRaw
        firstLocalContext secondLocalContext localAliases (localProfiles (some [marker]))
        (SourceCurrentScopedDeletionInputs.local_cuts smart body inputs firstNames secondNames firstOwn secondOwn
          (fun label member => tests label (List.mem_cons_of_mem _ member)))
        firstRawActual secondRawActual localGrowthFirst localGrowthSecond heap history
      have bare := SourceCurrentUsedBinderOutputTags.bare body localInputs firstLocal secondLocal firstOwn secondOwn
        firstAfterDepth firstAfterRaw secondAfterDepth secondAfterRaw firstLocalContext.base secondLocalContext.base
        firstRaw secondRaw firstRawActual secondRawActual (local_tests body inputs firstNames secondNames firstOwn secondOwn tests)
      have firstRawContext : Context firstAfterRaw (localInputs.map (input firstLocal)) := by
        simpa only [firstRawActual,Outcome.state] using firstLocalContext.build body
      have secondRawContext : Context secondAfterRaw (localInputs.map (input secondLocal)) := by
        simpa only [secondRawActual,Outcome.state] using secondLocalContext.build body
      have firstAvailable := (InternedFreshOrdinaryFacts.build_verified body _ firstAfterDepth
        firstLocalContext.base.normal.facts firstLocalContext.base.inputs).result firstRaw firstAfterRaw firstRawActual
      have secondAvailable := (InternedFreshOrdinaryFacts.build_verified body _ secondAfterDepth
        secondLocalContext.base.normal.facts secondLocalContext.base.inputs).result secondRaw secondAfterRaw secondRawActual
      have firstFiltered := SourceCurrentStoredRootDeletionConstruction.filter_profile firstOwn firstRaw
        (shadow firstOwn (some [marker]) firstAssignment) firstAfterRaw firstRawContext.base.normal firstAvailable
      have secondFiltered := SourceCurrentStoredRootDeletionConstruction.filter_profile secondOwn secondRaw
        (shadow secondOwn (some [marker]) secondAssignment) secondAfterRaw secondRawContext.base.normal secondAvailable
      rw [firstFilter] at firstFiltered
      rw [secondFilter] at secondFiltered
      have ordinarySame : Equivalent
          (SourceCurrentStoredProfileFunction.denote firstOrdinary (shadow firstOwn (some [marker]) firstAssignment))
          (SourceCurrentStoredProfileFunction.denote secondOrdinary (shadow secondOwn (some [marker]) secondAssignment)) := by
        by_cases firstBare : firstRaw = .reference firstOwn
        · have secondBare := bare.mp firstBare
          simp only [firstBare,secondBare,Value.referenceOf,beq_self_eq_true,ite_true,shadow,ite_true] at firstFiltered secondFiltered
          exact InternedProfileEquivalence.trans firstFiltered (InternedProfileEquivalence.symm secondFiltered)
        · have secondBare : secondRaw ≠ .reference secondOwn := fun same => firstBare (bare.mpr same)
          have firstTag : (firstRaw.referenceOf == .ref firstOwn) = false := by
            simp only [beq_eq_false_iff_ne]; exact fun same => firstBare ((referenceOf_self_iff firstOwn firstRaw).mp same)
          have secondTag : (secondRaw.referenceOf == .ref secondOwn) = false := by
            simp only [beq_eq_false_iff_ne]; exact fun same => secondBare ((referenceOf_self_iff secondOwn secondRaw).mp same)
          simp only [firstTag,secondTag,Bool.false_eq_true,ite_false] at firstFiltered secondFiltered
          exact InternedProfileEquivalence.trans firstFiltered
            (InternedProfileEquivalence.trans compared (InternedProfileEquivalence.symm secondFiltered))
      have closed : first.free.isEmpty = second.free.isEmpty := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.isEmpty_iff,List.eq_nil_iff_forall_not_mem]
        have firstFree := SourceCurrentNativeNormalizationInputs.actual_free (.binder smart body) inputs firstNames
          firstBefore firstAfter firstContext.base first firstDone
        have secondFree := SourceCurrentNativeNormalizationInputs.actual_free (.binder smart body) inputs secondNames
          secondBefore secondAfter secondContext.base second secondDone
        constructor
        · intro empty name member
          obtain ⟨label,present,rfl⟩ := List.mem_map.mp ((secondFree name).mp member)
          exact empty _ ((firstFree _).mpr (List.mem_map.mpr ⟨label,present,rfl⟩))
        · intro empty name member
          obtain ⟨label,present,rfl⟩ := List.mem_map.mp ((firstFree name).mp member)
          exact empty _ ((secondFree _).mpr (List.mem_map.mpr ⟨label,present,rfl⟩))
      have left := firstReduced firstCuts firstAssignment marker firstFreshMarker
      have right := secondReduced secondCuts secondAssignment marker secondFreshMarker
      rw [← firstShape] at left
      rw [← secondShape] at right
      rw [closed] at left
      apply InternedProfileEquivalence.trans left
      apply InternedProfileEquivalence.trans _ (InternedProfileEquivalence.symm right)
      split
      · exact InternedProfileEquivalence.refl _
      · exact erase_same marker ordinarySame

end MicroCFTA.SourceCurrentCausalSourceBinderComparison
