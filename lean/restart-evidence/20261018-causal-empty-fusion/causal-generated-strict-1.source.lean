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

mutual
/-- Every actual recursive generator at a causal reader preserves the physical Empty test. -/
theorem generated (reader : State Symbol Guard) (history : History empty reader)
    {first second : Value Symbol Guard} (pair : Generated reader first second) :
    (first.referenceOf == .empty) = (second.referenceOf == .empty) := by
  cases pair with
  | refl value => rfl
  | filtered expression captures firstNames secondNames firstOwn secondOwn firstMap secondMap
      firstBefore secondBefore firstRawHeap secondRawHeap _firstFilterHeap _secondFilterHeap
      firstRaw secondRaw firstFiltered secondFiltered left right ready firstContext secondContext aliases tests paired
      firstReplacements secondReplacements firstAvailable secondAvailable firstBuild secondBuild
      _firstFilter _secondFilter firstGrowth secondGrowth _firstFilteredGrowth _secondFilteredGrowth
      _firstWarmBuild _secondWarmBuild firstWarmFilter secondWarmFilter firstDone secondDone =>
      have firstRawAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ firstBefore
        firstContext.base.normal.facts firstContext.base.inputs).result firstRaw firstRawHeap firstBuild
      have secondRawAvailable := (InternedFreshOrdinaryFacts.build_verified expression _ secondBefore
        secondContext.base.normal.facts secondContext.base.inputs).result secondRaw secondRawHeap secondBuild
      exact SourceCurrentCausalFilteredSourceFusion.source expression reader ready history captures firstNames secondNames
        firstOwn secondOwn firstMap secondMap firstBefore secondBefore firstRawHeap secondRawHeap
        firstRaw secondRaw firstFiltered secondFiltered left right firstContext secondContext aliases tests
        (inputs reader history paired) firstReplacements secondReplacements
        (raw_available reader firstRawHeap ready firstRaw firstFiltered firstOwn firstRawAvailable firstGrowth
          firstAvailable firstWarmFilter)
        (raw_available reader secondRawHeap ready secondRaw secondFiltered secondOwn secondRawAvailable secondGrowth
          secondAvailable secondWarmFilter)
        firstBuild secondBuild firstGrowth secondGrowth firstWarmFilter secondWarmFilter firstDone secondDone
termination_by structural pair

/-- Recursive lexical inputs supply the paired Empty relation required by causal source fusion. -/
theorem inputs (reader : State Symbol Guard) (history : History empty reader)
    {first second : Environment Symbol Guard} {left right : List (Value Symbol Guard)}
    (paired : Inputs reader first second left right) :
    Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second left right := by
  cases paired with
  | nil first second => exact .nil
  | reference head _back tail => exact .cons (generated reader history head) (inputs reader history tail)
  | fixed value agree tail =>
      refine .cons ?_ (inputs reader history tail)
      cases value with
      | reference name =>
          change (((first name).getD (.reference name)).referenceOf == .empty) =
            (((second name).getD (.reference name)).referenceOf == .empty)
          rw [agree name (by simp only [Value.free, List.mem_singleton])]
      | empty | node | union | mu => exact ⟨rfl, agree⟩
termination_by structural paired
end

end MicroCFTA.SourceCurrentCausalGeneratedEmpty
