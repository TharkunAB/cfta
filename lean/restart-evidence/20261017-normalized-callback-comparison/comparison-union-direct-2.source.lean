import MicroCFTA.SourceCurrentNativeNormalizedComparisonFinite
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
open InternedDeepFreeDepth InternedDeepFreeNormalization
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

end MicroCFTA.SourceCurrentNativeNormalizedComparisonUnion
