import MicroCFTA.SourceCurrentUsedBinderOutputTags
import MicroCFTA.SourceCurrentCausalUnionPairPreparation
import MicroCFTA.SourceCurrentFilteredUnionFragments
import MicroCFTA.SourceCurrentGeneratedGrowth
import MicroCFTA.SourceCurrentGeneratedUnionCases
import MicroCFTA.SourceCurrentLiteralLocalSimulation

/-!
# Conditional literal source clauses through actual unions

Member laws apply at one produced common reader. Actual ordered member
schedules retain the original parent outputs. Exact bare-self tests select
retained members. This module does not assert the law for every source or
transport observations to the earlier reader.
-/
namespace MicroCFTA.SourceCurrentLiteralSourceClauses
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input inputProfile)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentRetainedMuDirectedCase (Inputs)
open SourceCurrentUsedBinderAliasTransport (Scope Aliases)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentLiteralLocalSimulation (Clauses Relation)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceEqualityRequiredCache (Ready Keeps)

private theorem member_scope {Atom : Type} (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom))
    (child : Syntax Symbol Guard) (member : child ∈ expressions)
    (label : Sum Reference Atom) (present : label ∈ Scope child inputs) :
    label ∈ Scope (.union expressions) inputs := by
  rcases List.mem_cons.mp present with rfl | present
  · exact List.mem_cons_self
  · apply List.mem_cons_of_mem
    unfold support at present ⊢
    rw [InternedFreeNameSemantics.evaluate]
    exact (InternedFreeNameSemantics.evaluateMany_member expressions (inputs.map inputProfile)
      (inputs.map inputNames) label).mpr ⟨child,member,present⟩

private theorem at_left {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (paired : All₂ relation first second) (index : Nat) (value : α) (found : first[index]? = some value) :
    ∃ other, second[index]? = some other ∧ relation value other := by
  induction paired generalizing index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | @cons head other first second pair rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at found
          subst value
          exact ⟨other,rfl,pair⟩
      | succ index => exact ih index found

private theorem at_right {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (paired : All₂ relation first second) (index : Nat) (value : β) (found : second[index]? = some value) :
    ∃ other, first[index]? = some other ∧ relation other value := by
  induction paired generalizing index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | @cons head other first second pair rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at found
          subst value
          exact ⟨head,rfl,pair⟩
      | succ index => exact ih index found

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A source law transfers literal clauses under the exact causal reconstruction premises. -/
def Law (expression : Syntax Symbol Guard) : Prop :=
  ∀ {Atom : Type} (reader : State Symbol Guard) (_ready : Ready reader) (_history : History empty reader)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
    (firstBefore secondBefore firstRawHeap secondRawHeap : State Symbol Guard)
    (firstRaw secondRaw firstFiltered secondFiltered left right : Value Symbol Guard),
    Context firstBefore (inputs.map (input firstNames)) →
    Context secondBefore (inputs.map (input secondNames)) →
    Aliases expression inputs firstNames secondNames →
    (∀ label ∈ Scope expression inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) →
    Inputs reader firstMap secondMap
      (inputs.map (input firstNames)) (inputs.map (input secondNames)) →
    Replacements reader firstMap → Replacements reader secondMap →
    Available reader firstRaw → Available reader secondRaw →
    build expression (inputs.map (input firstNames)) firstBefore = .done firstRaw firstRawHeap →
    build expression (inputs.map (input secondNames)) secondBefore = .done secondRaw secondRawHeap →
    Grows firstRawHeap reader → Grows secondRawHeap reader →
    run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered, reader) →
    run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered, reader) →
    execute firstFiltered firstMap reader = .done left reader →
    execute secondFiltered secondMap reader = .done right reader →
    Clauses reader (Relation reader) left right

/-- Strict original member laws transfer both parent outputs at a produced common reader. -/
theorem union (expressions : List (Syntax Symbol Guard))
    (ih : ∀ child ∈ expressions, Law child) :
    ∀ {Atom : Type} (reader : State Symbol Guard) (_ready : Ready reader) (_history : History empty reader)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
    (firstBefore secondBefore firstRawHeap secondRawHeap : State Symbol Guard)
    (firstRaw secondRaw firstFiltered secondFiltered left right : Value Symbol Guard),
    Context firstBefore (inputs.map (input firstNames)) →
    Context secondBefore (inputs.map (input secondNames)) →
    Aliases (.union expressions) inputs firstNames secondNames →
    (∀ label ∈ Scope (.union expressions) inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) →
    Inputs reader firstMap secondMap
      (inputs.map (input firstNames)) (inputs.map (input secondNames)) →
    Replacements reader firstMap → Replacements reader secondMap →
    Available reader firstRaw → Available reader secondRaw →
    build (.union expressions) (inputs.map (input firstNames)) firstBefore = .done firstRaw firstRawHeap →
    build (.union expressions) (inputs.map (input secondNames)) secondBefore = .done secondRaw secondRawHeap →
    Grows firstRawHeap reader → Grows secondRawHeap reader →
    run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered, reader) →
    run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered, reader) →
    execute firstFiltered firstMap reader = .done left reader →
    execute secondFiltered secondMap reader = .done right reader →
    ∃ final, Keeps reader final ∧ Nonempty (History empty final) ∧ Clauses final (Relation final) left right := by
  intro Atom reader ready history inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right
    firstContext secondContext aliases tests paired firstReplacements secondReplacements firstAvailable secondAvailable
    firstBuild secondBuild firstGrowth secondGrowth firstFilter secondFilter firstDone secondDone
  obtain ⟨final,kept,⟨finalHistory⟩,firstSchedule,secondSchedule⟩ :=
    SourceCurrentCausalUnionPairPreparation.prepare expressions
      (inputs.map (input firstNames)) (inputs.map (input secondNames))
      firstBefore firstRawHeap secondBefore secondRawHeap reader firstContext secondContext firstRaw secondRaw
      firstBuild secondBuild ready history firstGrowth secondGrowth firstAvailable secondAvailable
      firstOwn secondOwn firstMap secondMap firstReplacements secondReplacements
      firstFiltered secondFiltered left right firstFilter secondFilter firstDone secondDone
  obtain ⟨firstValues,firstFilters,firstOutputs,firstValuesAvailable,_firstFiltersAvailable,_firstOutputsAvailable,
    firstMade,_firstSource,_firstMany,firstFiltersCalled,firstStored,firstSources,firstParentFilter,firstParentDone⟩ := firstSchedule
  obtain ⟨secondValues,secondFilters,secondOutputs,secondValuesAvailable,_secondFiltersAvailable,_secondOutputsAvailable,
    secondMade,_secondSource,_secondMany,secondFiltersCalled,secondStored,secondSources,secondParentFilter,secondParentDone⟩ := secondSchedule
  have finalPaired := SourceCurrentGeneratedGrowth.inputs paired kept
  have firstFinalReplacements : Replacements final firstMap :=
    fun name value found => kept.available value (firstReplacements name value found)
  have secondFinalReplacements : Replacements final secondMap :=
    fun name value found => kept.available value (secondReplacements name value found)
  have parentBare : firstRaw = .reference firstOwn ↔ secondRaw = .reference secondOwn :=
    SourceCurrentUsedBinderOutputTags.bare (.union expressions) inputs firstNames secondNames firstOwn secondOwn
      firstBefore firstRawHeap secondBefore secondRawHeap firstContext.base secondContext.base
      firstRaw secondRaw firstBuild secondBuild tests
  have fragments := SourceCurrentFilteredUnionFragments.parts final kept.ready
    firstValues firstFilters firstOutputs firstValuesAvailable firstRaw firstFiltered left firstOwn firstMap
    firstMade firstParentFilter firstFinalReplacements firstParentDone firstFiltersCalled firstStored
  have memberClauses (index : Nat) (raw cut output : Value Symbol Guard)
      (rawFound : firstValues[index]? = some raw) (cutFound : firstFilters[index]? = some cut)
      (outputFound : firstOutputs[index]? = some output)
      (retained : raw ≠ .reference firstOwn ∨ firstRaw = .reference firstOwn) :
      Clauses final (Relation final) output right := by
    obtain ⟨child,childFound,firstStart,firstReturn,firstChildContext,firstChildBuild,firstChildGrowth,_firstWarm⟩ :=
      at_right firstSources index raw rawFound
    have childMember : child ∈ expressions := List.mem_of_getElem? childFound
    obtain ⟨otherRaw,otherRawFound,secondStart,secondReturn,secondChildContext,secondChildBuild,secondChildGrowth,_secondWarm⟩ :=
      at_left secondSources index child childFound
    obtain ⟨actualCut,actualCutFound,firstCutCall⟩ := at_left firstFiltersCalled index raw rawFound
    have cutSame := Option.some.inj (actualCutFound.symm.trans cutFound)
    subst actualCut
    obtain ⟨actualOutput,actualOutputFound,firstOutputCall⟩ := at_left firstStored index cut cutFound
    have outputSame := Option.some.inj (actualOutputFound.symm.trans outputFound)
    subst actualOutput
    obtain ⟨otherCut,otherCutFound,secondCutCall⟩ := at_left secondFiltersCalled index otherRaw otherRawFound
    obtain ⟨otherOutput,_otherOutputFound,secondOutputCall⟩ := at_left secondStored index otherCut otherCutFound
    have childAliases : Aliases child inputs firstNames secondNames :=
      fun a aMember b bMember => aliases a (member_scope expressions inputs child childMember a aMember)
        b (member_scope expressions inputs child childMember b bMember)
    have childTests : ∀ label ∈ Scope child inputs,
        Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn :=
      fun label present => tests label (member_scope expressions inputs child childMember label present)
    have childBare : raw = .reference firstOwn ↔ otherRaw = .reference secondOwn :=
      SourceCurrentUsedBinderOutputTags.bare child inputs firstNames secondNames firstOwn secondOwn
        firstStart firstReturn secondStart secondReturn firstChildContext.base secondChildContext.base
        raw otherRaw firstChildBuild secondChildBuild childTests
    have otherRetained : otherRaw ≠ .reference secondOwn ∨ secondRaw = .reference secondOwn := by
      rcases retained with different | bare
      · exact Or.inl (fun same => different (childBare.mpr same))
      · exact Or.inr (parentBare.mp bare)
    have childClauses := ih child childMember final kept.ready finalHistory inputs firstNames secondNames
      firstOwn secondOwn firstMap secondMap firstStart secondStart firstReturn secondReturn
      raw otherRaw cut otherCut output otherOutput firstChildContext secondChildContext childAliases childTests finalPaired
      firstFinalReplacements secondFinalReplacements
      (firstValuesAvailable raw (List.mem_of_getElem? rawFound))
      (secondValuesAvailable otherRaw (List.mem_of_getElem? otherRawFound))
      firstChildBuild secondChildBuild firstChildGrowth secondChildGrowth
      firstCutCall secondCutCall firstOutputCall secondOutputCall
    have included := SourceCurrentGeneratedUnionCases.retained_member final kept.ready secondValues secondValuesAvailable
      otherRaw secondRaw otherCut secondFiltered otherOutput right secondOwn secondMap
      (List.mem_of_getElem? otherRawFound) secondMade otherRetained secondCutCall secondParentFilter
      secondFinalReplacements secondOutputCall secondParentDone
    exact SourceCurrentLiteralLocalSimulation.post_below final childClauses included
  refine ⟨final,kept,⟨finalHistory⟩,?_,?_,?_⟩
  · intro name found
    obtain ⟨index,raw,cut,output,rawFound,cutFound,outputFound,retained,inside⟩ := (fragments.1 (.reference name)).mp found
    exact (memberClauses index raw cut output rawFound cutFound outputFound retained).1 name inside
  · intro row found
    obtain ⟨index,raw,cut,output,rawFound,cutFound,outputFound,retained,inside⟩ := (fragments.2 row).mp found
    exact (memberClauses index raw cut output rawFound cutFound outputFound retained).2.1 row inside
  · intro entry body depth ordinary found next member
    obtain ⟨index,raw,cut,output,rawFound,cutFound,outputFound,retained,inside⟩ :=
      (fragments.1 (.mu entry body depth ordinary)).mp found
    exact (memberClauses index raw cut output rawFound cutFound outputFound retained).2.2
      entry body depth ordinary inside next member

end MicroCFTA.SourceCurrentLiteralSourceClauses
