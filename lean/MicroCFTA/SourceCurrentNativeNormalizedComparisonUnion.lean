import MicroCFTA.SourceCurrentNativeNormalizedComparisonInactive
import MicroCFTA.InternedFreshOrdinaryLiveInputReplay

/-!
# Actual normalized comparison through source unions

Ordered source child runs supply their own comparison receipts. The actual
union constructor then retains the same stripped canonical alternatives.
-/
set_option maxHeartbeats 1600000
namespace MicroCFTA.SourceCurrentNativeNormalizedComparisonUnion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedNestedProvenance InternedNestedSpecialization
open InternedDeepFreeDepth InternedDeepFreeNormalization InternedStoredMuOrigins
open SourceCurrentNativeNormalizedComparison SourceCurrentNativeNormalizedComparisonFinite
open SourceCurrentNativeStrippedAlternatives
open InternedBinderProtocol (Reference)
variable {Atom : Type}

private theorem strip_append (names : List Reference) (first second : List (Value Symbol Guard)) :
    stripMany names (first ++ second) = stripMany names first ++ stripMany names second := by
  induction names generalizing first second with
  | nil => rfl
  | cons name names ih => simp only [stripMany, InternedRootAlternativeLists.remove, List.filter_append, ih]

private theorem strip_nil (names : List Reference) :
    stripMany names ([] : List (Value Symbol Guard)) = [] := by
  induction names with
  | nil => rfl
  | cons name names ih => simpa only [stripMany, InternedRootAlternativeLists.remove, List.filter_nil] using ih

private theorem support_cons (expression : Syntax Symbol Guard) (members : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) :
    SourceCurrentNativeNormalizationInputs.support (.union (expression :: members)) inputs =
      SourceCurrentNativeNormalizationInputs.support expression inputs ++
      SourceCurrentNativeNormalizationInputs.support (.union members) inputs := by
  simp only [SourceCurrentNativeNormalizationInputs.support, InternedFreeNameSemantics.evaluate,
    InternedFreeNameSemantics.evaluateMany, List.flatten_cons]

private theorem many_compared [DecidableEq (EdgeKey Symbol Guard)]
    (members : List (Syntax Symbol Guard)) (inputs : List (Sum (Value Symbol Guard) Atom))
    (atoms : List Atom) (firstNames secondNames : Atom → Reference) (common : State Symbol Guard)
    (children : ∀ expression ∈ members, Compared expression inputs atoms firstNames secondNames common)
    (before later after final : State Symbol Guard)
    (lc : Context before (inputs.map (input firstNames)))
    (rc : Context later (inputs.map (input secondNames)))
    (lh : InternedFreshOrdinaryDepthHeap.Heap before)
    (rh : InternedFreshOrdinaryDepthHeap.Heap later)
    (first second : List (Value Symbol Guard))
    (leftDone : buildMany members (inputs.map (input firstNames)) before = .done first after)
    (rightDone : buildMany members (inputs.map (input secondNames)) later = .done second final)
    (lg : Grows after common) (rg : Grows final common)
    (li : Extends after.nodes.issued common.nodes.issued)
    (ri : Extends final.nodes.issued common.nodes.issued)
    (lf : ∀ atom ∈ atoms, .inl (firstNames atom) ∉ SourceCurrentNativeNormalizationInputs.support (.union members) inputs)
    (rf : ∀ atom ∈ atoms, .inl (secondNames atom) ∉ SourceCurrentNativeNormalizationInputs.support (.union members) inputs)
    (shallow : ∀ atom ∈ atoms, ∀ value ∈ first, firstNames atom ∉ deepNames value) :
    stripMany (atoms.map firstNames) (first.flatMap unionMembers) =
      stripMany (atoms.map secondNames) (second.flatMap unionMembers) := by
  induction members generalizing before later after final first second with
  | nil =>
      simp only [buildMany, Outcome.done.injEq] at leftDone rightDone
      obtain ⟨rfl, rfl⟩ := leftDone
      obtain ⟨rfl, rfl⟩ := rightDone
      simp only [List.flatMap_nil, strip_nil]
  | cons expression members ih =>
      simp only [buildMany] at leftDone rightDone
      obtain ⟨headLeft, middleLeft, leftHead, leftTail⟩ := bind_done _ _ _ _ leftDone
      obtain ⟨headRight, middleRight, rightHead, rightTail⟩ := bind_done _ _ _ _ rightDone
      obtain ⟨tailLeft, endLeft, leftRest, leftPure⟩ := bind_done _ _ _ _ leftTail
      obtain ⟨tailRight, endRight, rightRest, rightPure⟩ := bind_done _ _ _ _ rightTail
      simp only [Outcome.done.injEq] at leftPure rightPure
      obtain ⟨rfl, rfl⟩ := leftPure
      obtain ⟨rfl, rfl⟩ := rightPure
      have lcHead : Context middleLeft (inputs.map (input firstNames)) := by
        simpa only [leftHead, Outcome.state] using lc.build expression
      have rcHead : Context middleRight (inputs.map (input secondNames)) := by
        simpa only [rightHead, Outcome.state] using rc.build expression
      have lhHead : InternedFreshOrdinaryDepthHeap.Heap middleLeft := by
        simpa only [leftHead, Outcome.state] using (InternedRecordDepthExecution.build_depth expression _ before lc lh).heap
      have rhHead : InternedFreshOrdinaryDepthHeap.Heap middleRight := by
        simpa only [rightHead, Outcome.state] using (InternedRecordDepthExecution.build_depth expression _ later rc rh).heap
      have leftVerified := InternedFreshOrdinaryFacts.buildMany_verified members _ middleLeft lcHead.normal.facts lcHead.inputs
      have rightVerified := InternedFreshOrdinaryFacts.buildMany_verified members _ middleRight rcHead.normal.facts rcHead.inputs
      have leftGrowth : Grows middleLeft endLeft := by simpa only [leftRest, Outcome.state] using leftVerified.growth
      have rightGrowth : Grows middleRight endRight := by simpa only [rightRest, Outcome.state] using rightVerified.growth
      have leftHistory : Extends middleLeft.nodes.issued endLeft.nodes.issued := by
        simpa only [leftRest, Outcome.state] using leftVerified.history
      have rightHistory : Extends middleRight.nodes.issued endRight.nodes.issued := by
        simpa only [rightRest, Outcome.state] using rightVerified.history
      have leftHeadFresh : ∀ atom ∈ atoms, .inl (firstNames atom) ∉ SourceCurrentNativeNormalizationInputs.support expression inputs := by
        intro atom selected present
        apply lf atom selected
        rw [support_cons]
        exact List.mem_append_left _ present
      have rightHeadFresh : ∀ atom ∈ atoms, .inl (secondNames atom) ∉ SourceCurrentNativeNormalizationInputs.support expression inputs := by
        intro atom selected present
        apply rf atom selected
        rw [support_cons]
        exact List.mem_append_left _ present
      have leftRestFresh : ∀ atom ∈ atoms, .inl (firstNames atom) ∉ SourceCurrentNativeNormalizationInputs.support (.union members) inputs := by
        intro atom selected present
        apply lf atom selected
        rw [support_cons]
        exact List.mem_append_right _ present
      have rightRestFresh : ∀ atom ∈ atoms, .inl (secondNames atom) ∉ SourceCurrentNativeNormalizationInputs.support (.union members) inputs := by
        intro atom selected present
        apply rf atom selected
        rw [support_cons]
        exact List.mem_append_right _ present
      have headSame := children expression List.mem_cons_self before later middleLeft middleRight lc rc lh rh headLeft headRight
        leftHead rightHead (grows_trans leftGrowth lg) (grows_trans rightGrowth rg)
        (extends_trans leftHistory li) (extends_trans rightHistory ri) leftHeadFresh rightHeadFresh
        (fun atom selected => shallow atom selected headLeft List.mem_cons_self)
      have tailSame := ih (fun child member => children child (List.mem_cons_of_mem expression member))
        middleLeft middleRight endLeft endRight lcHead rcHead lhHead rhHead tailLeft tailRight leftRest rightRest
        lg rg li ri leftRestFresh rightRestFresh
        (fun atom selected value member => shallow atom selected value (List.mem_cons_of_mem headLeft member))
      simp only [List.flatMap_cons, strip_append, headSame, tailSame]

private theorem union_root_origin [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (normal : Normal state)
    (available : Values state values) (name : Reference)
    (named : name ∈ (run (makeUnion values) state).1.free)
    (shallow : name ∉ deepNames (run (makeUnion values) state).1) :
    Value.reference name ∈ values.flatMap unionMembers := by
  obtain ⟨value, member, free⟩ := (InternedNormalizationFree.makeUnion_free values state
    normal.facts.coherent normal.facts.cached normal.facts.linked normal.live available name).mp named
  have childShallow : name ∉ deepNames value := by
    intro deep
    exact shallow ((makeUnion_deep values state normal.facts.coherent normal.facts.cached
      normal.facts.linked normal.live available name).mpr ⟨value, member, deep⟩)
  exact List.mem_flatMap.mpr ⟨value, member,
    free_root value state normal (available value member) name free childShallow⟩

/-- Actual ordered source union calls compare from their child receipts and initial label coverage. -/
theorem union_compared [DecidableEq (EdgeKey Symbol Guard)]
    (members : List (Syntax Symbol Guard)) (inputs : List (Sum (Value Symbol Guard) Atom))
    (atoms : List Atom) (firstNames secondNames : Atom → Reference) (common : State Symbol Guard)
    (commonNormal : Normal common) (covered : ∀ atom, .inr atom ∈ inputs → atom ∈ atoms)
    (children : ∀ expression ∈ members, Compared expression inputs atoms firstNames secondNames common) :
    Compared (.union members) inputs atoms firstNames secondNames common := by
  by_cases live : ∃ atom, .inr atom ∈ SourceCurrentNativeNormalizationInputs.support (.union members) inputs
  · intro before later after final lc rc lh rh first second leftDone rightDone lg rg li ri lf rf shallow
    have rightShallow := deep_transport_on (.union members) inputs atoms firstNames secondNames
      before after later final lc rc lh rh first second leftDone rightDone covered shallow rf
    have leftWhole := leftDone
    have rightWhole := rightDone
    simp only [build] at leftDone rightDone
    obtain ⟨leftValues, middleLeft, leftBuilt, leftMade⟩ := bind_done _ _ _ _ leftDone
    obtain ⟨rightValues, middleRight, rightBuilt, rightMade⟩ := bind_done _ _ _ _ rightDone
    have leftContext : Context middleLeft (inputs.map (input firstNames)) := by
      simpa only [leftBuilt, Outcome.state] using lc.many members
    have rightContext : Context middleRight (inputs.map (input secondNames)) := by
      simpa only [rightBuilt, Outcome.state] using rc.many members
    have leftAvailable := (InternedFreshOrdinaryFacts.buildMany_verified members _ before
      lc.normal.facts lc.inputs).result _ _ leftBuilt
    have rightAvailable := (InternedFreshOrdinaryFacts.buildMany_verified members _ later
      rc.normal.facts rc.inputs).result _ _ rightBuilt
    simp only [work, Outcome.done.injEq] at leftMade rightMade
    obtain ⟨rfl, rfl⟩ := leftMade
    obtain ⟨rfl, rfl⟩ := rightMade
    have leftUnion := InternedNestedFacts.union_verified leftValues middleLeft leftContext.normal.facts leftAvailable
    have rightUnion := InternedNestedFacts.union_verified rightValues middleRight rightContext.normal.facts rightAvailable
    have same := many_compared members inputs atoms firstNames secondNames common children
      before later middleLeft middleRight lc rc lh rh leftValues rightValues leftBuilt rightBuilt
      (grows_trans leftUnion.growth lg) (grows_trans rightUnion.growth rg)
      (extends_trans leftUnion.history li) (extends_trans rightUnion.history ri) lf rf
      (by
        intro atom selected value member deep
        exact shallow atom selected ((makeUnion_deep leftValues middleLeft leftContext.normal.facts.coherent
          leftContext.normal.facts.cached leftContext.normal.facts.linked leftContext.normal.live leftAvailable
          (firstNames atom)).mpr ⟨value, member, deep⟩))
    obtain ⟨atom, present⟩ := live
    have selected := covered atom (support_varying_member (.union members) inputs atom present)
    have leftFree := (SourceCurrentNativeNormalizationInputs.actual_free (.union members) inputs firstNames
      before _ lc _ leftWhole (firstNames atom)).mpr (List.mem_map.mpr ⟨.inr atom, present, rfl⟩)
    have rightFree := (SourceCurrentNativeNormalizationInputs.actual_free (.union members) inputs secondNames
      later _ rc _ rightWhole (secondNames atom)).mpr (List.mem_map.mpr ⟨.inr atom, present, rfl⟩)
    rw [union_stripped (atoms.map firstNames) leftValues middleLeft leftContext.normal.facts leftAvailable
        ⟨firstNames atom, union_root_origin leftValues middleLeft leftContext.normal leftAvailable
          (firstNames atom) leftFree (shallow atom selected)⟩,
      union_stripped (atoms.map secondNames) rightValues middleRight rightContext.normal.facts rightAvailable
        ⟨secondNames atom, union_root_origin rightValues middleRight rightContext.normal rightAvailable
          (secondNames atom) rightFree (rightShallow atom selected)⟩,
      same]
  · exact SourceCurrentNativeNormalizedComparisonInactive.inactive_compared (.union members)
      inputs atoms firstNames secondNames common commonNormal (fun atom present => live ⟨atom, present⟩)

end MicroCFTA.SourceCurrentNativeNormalizedComparisonUnion
