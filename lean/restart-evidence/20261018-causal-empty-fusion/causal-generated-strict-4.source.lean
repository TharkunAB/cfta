import MicroCFTA.SourceCurrentCausalFilteredSourceFusion
import MicroCFTA.SourceCurrentRetainedMuDirectedCase

/-!
# Physical Empty agreement for actual recursive generators

Generated pairs recurse through their resolved lexical reference slots.
An actual reader history supplies causal filtered source fusion at each
generator. Mutual induction proves the Empty test for every generated
pair. It does not prove the recursive guarded simulation clauses.
-/
namespace MicroCFTA.SourceCurrentCausalGeneratedEmpty
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedStoredSubstitution (Environment)
open InternedFreshOrdinaryLiveInputs (input)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentReaderReplacementSlots (Paired Slot)
open SourceEqualityRequiredCache (Ready)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem raw_available (reader before : State Symbol Guard) (ready : Ready reader)
    (raw filtered : Value Symbol Guard) (own : InternedBinderProtocol.Reference)
    (earlier : Available before raw) (growth : Grows before reader)
    (available : Available reader filtered)
    (warm : run (withoutSelfReference own raw) reader = (filtered, reader)) : Available reader raw := by
  have resident := InternedFreshProbeKeys.resident_grows before reader growth raw earlier.resident
  cases raw with
  | empty => exact empty_available reader
  | reference name =>
      have same : filtered = .reference name := (congrArg Prod.fst warm).symm
      exact same ▸ available
  | node entry rows depth free => exact ready.semantic.1.normal.facts.cached.nodes _ _ (resident entry rfl)
  | union entry members depth free => exact ready.semantic.1.normal.facts.cached.nodes _ _ (resident entry rfl)
  | mu entry body depth ordinary => exact ready.semantic.1.normal.facts.cached.nodes _ _ (resident entry rfl)

/-- Every actual recursive generator at a causal reader preserves the physical Empty test. -/
theorem generated (reader : State Symbol Guard) (history : History empty reader)
    {first second : Value Symbol Guard} (pair : Generated reader first second) :
    (first.referenceOf == .empty) = (second.referenceOf == .empty) := by
  induction pair using Generated.rec
      (motive_2 := fun first second left right _ =>
        Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second left right) with
  | refl value => rfl
  | filtered expression captures firstNames secondNames firstOwn secondOwn firstMap secondMap
      firstBefore secondBefore firstRawHeap secondRawHeap _firstFilterHeap _secondFilterHeap
      firstRaw secondRaw firstFiltered secondFiltered left right ready firstContext secondContext aliases tests paired
      firstReplacements secondReplacements firstAvailable secondAvailable firstBuild secondBuild
      _firstFilter _secondFilter firstGrowth secondGrowth _firstFilteredGrowth _secondFilteredGrowth
      _firstWarmBuild _secondWarmBuild firstWarmFilter secondWarmFilter firstDone secondDone pairedIH =>
      have firstRawAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ firstBefore
        firstContext.base.normal.facts firstContext.base.inputs).result firstRaw firstRawHeap firstBuild
      have secondRawAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ secondBefore
        secondContext.base.normal.facts secondContext.base.inputs).result secondRaw secondRawHeap secondBuild
      exact SourceCurrentCausalFilteredSourceFusion.source expression reader ready history captures firstNames secondNames
        firstOwn secondOwn firstMap secondMap firstBefore secondBefore firstRawHeap secondRawHeap
        firstRaw secondRaw firstFiltered secondFiltered _ _ firstContext secondContext aliases tests
        pairedIH firstReplacements secondReplacements
        (raw_available reader firstRawHeap ready firstRaw firstFiltered firstOwn firstRawAvailable firstGrowth
          firstAvailable firstWarmFilter)
        (raw_available reader secondRawHeap ready secondRaw secondFiltered secondOwn secondRawAvailable secondGrowth
          secondAvailable secondWarmFilter)
        firstBuild secondBuild firstGrowth secondGrowth firstWarmFilter secondWarmFilter firstDone secondDone
  | nil first second => exact .nil
  | reference _head _back _tail headIH _backIH tailIH => exact .cons headIH tailIH
  | @fixed firstMap secondMap lefts rights value agree _tail tailIH =>
      refine .cons ?_ tailIH
      cases value with
      | reference name =>
          change (((firstMap name).getD (.reference name)).referenceOf == .empty) =
            (((secondMap name).getD (.reference name)).referenceOf == .empty)
          rw [agree name (by simp only [Value.free, List.mem_singleton])]
      | empty | node | union | mu => exact ⟨rfl, agree⟩

/-- Recursive lexical inputs supply the paired Empty relation required by causal source fusion. -/
theorem inputs (reader : State Symbol Guard) (history : History empty reader)
    {first second : Environment Symbol Guard} {left right : List (Value Symbol Guard)}
    (paired : Inputs reader first second left right) :
    Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second left right := by
  induction paired using Inputs.rec (motive_1 := fun _ _ _ => True) with
  | refl => trivial
  | filtered => trivial
  | nil => exact .nil
  | reference head _back _tail _headIH _backIH tailIH => exact .cons (generated reader history head) tailIH
  | @fixed firstMap secondMap lefts rights value agree _tail tailIH =>
      refine .cons ?_ tailIH
      cases value with
      | reference name =>
          change (((firstMap name).getD (.reference name)).referenceOf == .empty) =
            (((secondMap name).getD (.reference name)).referenceOf == .empty)
          rw [agree name (by simp only [Value.free, List.mem_singleton])]
      | empty | node | union | mu => exact ⟨rfl, agree⟩

end MicroCFTA.SourceCurrentCausalGeneratedEmpty
