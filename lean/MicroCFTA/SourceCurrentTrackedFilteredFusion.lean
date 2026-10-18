import MicroCFTA.SourceCurrentFilteredNonemptyFusion
import MicroCFTA.SourceCurrentTrackedRootProfile
import MicroCFTA.SourceCurrentBoundedFilteredFusion
import MicroCFTA.InternedNormalizationFree

/-!
# Reader-filtered fusion of finitely tracked root profiles

Both original raw source results lie within one depth bound. Resolved
reference slots agree on tracked root alternatives and opacity. Fixed
captures retain equal maps on their free names. The actual historical
source and warm reader calls remain explicit. This module proves the
empty and variable cases, including arbitrary fixed open Mu captures.
-/
namespace MicroCFTA.SourceCurrentTrackedFilteredFusion
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome work)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input)
open InternedStoredSubstitution (Environment Replacements)
open InternedNestedProvenance (Values)
open InternedStoredMuOrigins (Normal)
open InternedBinderProtocol (Reference)
open SourceCurrentReaderReplacementSlots (Paired Slot)
open SourceCurrentUsedBinderAliasTransport (Scope Aliases)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentTrackedRootProfile (Related)

private theorem slot_at {relation : Value Symbol Guard → Value Symbol Guard → Prop}
    {first second : Environment Symbol Guard} {left right : List (Value Symbol Guard)}
    (paired : Paired relation first second left right) (index : Nat) :
    Slot relation first second (left[index]?.getD .empty) (right[index]?.getD .empty) := by
  induction paired generalizing index with
  | nil => exact ⟨rfl,by intro name impossible; cases impossible⟩
  | cons head tail ih =>
      cases index with
      | zero => exact head
      | succ index => exact ih index

private theorem fixed_slot {relation : Value Symbol Guard → Value Symbol Guard → Prop}
    {first second : Environment Symbol Guard} {left right : Value Symbol Guard}
    (paired : Slot relation first second left right) (nonreference : ∀ name, left ≠ .reference name) :
    left = right ∧ ∀ name ∈ left.free, first name = second name := by
  cases left <;> cases right
  all_goals try {exact False.elim (nonreference _ rfl)}
  all_goals try {cases paired}
  all_goals exact paired

private theorem union_named (reader : State Symbol Guard) (normal : Normal reader)
    (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
    (level : Nat) (free : List Reference) (available : Available reader (.union entry members level free))
    (name : Reference) (member : .reference name ∈ members) : name ∈ (Value.union entry members level free).free := by
  rw [Value.free,InternedNormalizationFree.union_free reader normal.facts.coherent entry members level free available.resident]
  exact childFree_member members name |>.mpr ⟨.reference name,member,List.mem_singleton_self _⟩

private theorem filter_absent [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard) (normal : Normal reader)
    (value : Value Symbol Guard) (available : Available reader value) (own : Reference)
    (absent : own ∉ value.free) : run (withoutSelfReference own value) reader = (value,reader) := by
  cases value with
  | empty | reference | node | mu => rfl
  | union entry members level free =>
      have missing : members.any (fun value => value.referenceOf == .ref own) = false := by
        apply Bool.eq_false_iff.mpr
        intro selected
        obtain ⟨value,member,same⟩ := List.any_eq_true.mp selected
        have equal := (referenceOf_self_iff own value).mp (eq_of_beq same)
        exact absent (union_named reader normal entry members level free available own (equal ▸ member))
      simp only [withoutSelfReference,missing,Bool.false_eq_true,↓reduceIte,run]

private theorem filters_same [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard) (normal : Normal reader)
    (value : Value Symbol Guard) (available : Available reader value) (firstOwn secondOwn : Reference)
    (tests : ∀ name ∈ value.free, name = firstOwn ↔ name = secondOwn) :
    run (withoutSelfReference firstOwn value) reader = run (withoutSelfReference secondOwn value) reader := by
  by_cases same : firstOwn = secondOwn
  · rw [same]
  · rw [filter_absent reader normal value available firstOwn
      (fun present => same ((tests firstOwn present).mp rfl)),
      filter_absent reader normal value available secondOwn
      (fun present => same ((tests secondOwn present).mpr rfl).symm)]

private theorem filtered_free [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard) (normal : Normal reader)
    (value : Value Symbol Guard) (available : Available reader value) (own name : Reference)
    (member : name ∈ (run (withoutSelfReference own value) reader).1.free) : name ∈ value.free := by
  cases value with
  | empty | reference | node | mu => exact member
  | union entry members level free =>
      simp only [withoutSelfReference] at member
      split at member
      · rw [InternedNormalizationFree.makeUnion_free
          (members.filter (fun value => value.referenceOf != .ref own)) reader normal.facts.coherent normal.facts.cached
          normal.facts.linked normal.live (fun child present => available.children child (List.mem_filter.mp present).1) name] at member
        obtain ⟨child,present,named⟩ := member
        rw [Value.free,InternedNormalizationFree.union_free reader normal.facts.coherent entry members level free available.resident]
        exact (childFree_member members name).mpr ⟨child,(List.mem_filter.mp present).1,named⟩
      · exact member

private theorem fixed_tests {Atom : Type} (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstOwn secondOwn : Reference)
    (index : Nat) (raw : Value Symbol Guard) (selected : (inputs.map (input firstNames))[index]?.getD .empty = raw)
    (nonreference : ∀ name, raw ≠ .reference name)
    (tests : ∀ label ∈ Scope (.var index) inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) :
    ∀ name ∈ raw.free, name = firstOwn ↔ name = secondOwn := by
  cases found : inputs[index]? with
  | none =>
      simp only [List.getElem?_map,found,Option.map_none,Option.getD_none] at selected
      cases selected
      intro name impossible
      cases impossible
  | some supplied =>
      cases supplied with
      | inl value =>
          simp only [List.getElem?_map,found,Option.map_some,Option.getD_some,input] at selected
          cases selected
          intro name present
          apply tests (.inl name)
          apply List.mem_cons_of_mem
          simp only [SourceCurrentNativeNormalizationInputs.support,InternedFreeNameSemantics.evaluate,
            List.getElem?_map,found,Option.map_some,Option.getD_some,SourceCurrentNativeNormalizationInputs.inputNames]
          exact List.mem_map.mpr ⟨name,present,rfl⟩
      | inr atom =>
          simp only [List.getElem?_map,found,Option.map_some,Option.getD_some,input] at selected
          exact False.elim (nonreference _ selected.symm)

private theorem reference_execute [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (environment : Environment Symbol Guard)
    (reader : State Symbol Guard) :
    execute (.reference name) environment reader = .done ((environment name).getD (.reference name)) reader := by
  simp [execute,InternedStoredSubstitution.leaves,Value.free,InternedStoredSubstitution.encode,
    InternedStoredSubstitution.slot,build,InternedStoredSubstitution.input]

private theorem resolved_empty (reader : State Symbol Guard) (ready : Ready reader)
    (environment : Environment Symbol Guard) (replacements : Replacements reader environment) (name : Reference) :
    InternedProfileSemantics.isEmpty (InternedRootProfile.profile ((environment name).getD (.reference name))) =
      (((environment name).getD (.reference name)).referenceOf == .empty) := by
  cases found : environment name with
  | none => simp [InternedRootProfile.profile,InternedProfileSemantics.isEmpty,Value.referenceOf]
  | some value =>
      exact InternedRootProfileNode.isEmpty_profile value reader ready.semantic.1.normal.proper
        (replacements name value found)

private theorem paired_from_empty (reader : State Symbol Guard) (ready : Ready reader)
    (first second : Environment Symbol Guard) (firstReplacements : Replacements reader first)
    (secondReplacements : Replacements reader second) (left right : List (Value Symbol Guard))
    (paired : Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second left right) :
    Paired (Related []) first second left right := by
  classical
  induction paired with
  | nil => exact .nil
  | @cons left right lefts rights head tail ih =>
      refine .cons ?_ ih
      cases left <;> cases right
      all_goals try {cases head}
      case reference.reference a b =>
        change InternedRootProfile.Equivalent
          (SourceCurrentTrackedRootProfile.mask [] (InternedRootProfile.profile ((first a).getD (.reference a))))
          (SourceCurrentTrackedRootProfile.mask [] (InternedRootProfile.profile ((second b).getD (.reference b))))
        apply (SourceCurrentTrackedRootProfile.nil_equiv _ _).mpr
        rw [resolved_empty reader ready first firstReplacements a,resolved_empty reader ready second secondReplacements b]
        exact head
      all_goals exact head

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual historical source and warm reader calls compare tracked root profiles within an original depth bound. -/
def Fusion (bound : Nat) (expression : Syntax Symbol Guard) : Prop :=
  ∀ (markers : List Reference) {Atom : Type} (reader : State Symbol Guard) (_ready : Ready reader)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
    (firstBefore secondBefore firstRawHeap secondRawHeap : State Symbol Guard)
    (firstRaw secondRaw firstFiltered secondFiltered left right : Value Symbol Guard),
    firstRaw.depth ≤ bound → secondRaw.depth ≤ bound →
    Context firstBefore (inputs.map (input firstNames)) →
    Context secondBefore (inputs.map (input secondNames)) →
    Aliases expression inputs firstNames secondNames →
    (∀ label ∈ Scope expression inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn) →
    Paired (Related markers) firstMap secondMap
      (inputs.map (input firstNames)) (inputs.map (input secondNames)) →
    Replacements reader firstMap → Replacements reader secondMap →
    Available reader firstRaw → Available reader secondRaw →
    build expression (inputs.map (input firstNames)) firstBefore = .done firstRaw firstRawHeap →
    build expression (inputs.map (input secondNames)) secondBefore = .done secondRaw secondRawHeap →
    Grows firstRawHeap reader → Grows secondRawHeap reader →
    run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered,reader) →
    run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered,reader) →
    execute firstFiltered firstMap reader = .done left reader →
    execute secondFiltered secondMap reader = .done right reader →
    Related markers left right

/-- Empty source calls retain Empty through both actual reader operations. -/
theorem empty (bound : Nat) : Fusion bound (.empty : Syntax Symbol Guard) := by
  intro markers Atom reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right
    _firstDepth _secondDepth _firstContext _secondContext _aliases _tests _paired _firstReplacements _secondReplacements _firstAvailable _secondAvailable
    firstBuild secondBuild _firstGrowth _secondGrowth firstFilter secondFilter firstDone secondDone
  have firstRawSame : firstRaw = .empty := (Outcome.done.inj (by simpa only [build] using firstBuild)).1.symm
  have secondRawSame : secondRaw = .empty := (Outcome.done.inj (by simpa only [build] using secondBuild)).1.symm
  subst firstRaw secondRaw
  have firstSame : firstFiltered = .empty := (congrArg Prod.fst firstFilter).symm
  have secondSame : secondFiltered = .empty := (congrArg Prod.fst secondFilter).symm
  subst firstFiltered secondFiltered
  have leftSame : left = .empty := by
    symm
    simpa [execute,InternedStoredSubstitution.leaves,Value.free,InternedStoredSubstitution.encode,
      InternedStoredSubstitution.slot,build,InternedStoredSubstitution.input] using firstDone
  have rightSame : right = .empty := by
    symm
    simpa [execute,InternedStoredSubstitution.leaves,Value.free,InternedStoredSubstitution.encode,
      InternedStoredSubstitution.slot,build,InternedStoredSubstitution.input] using secondDone
  rw [leftSame,rightSame]
  exact Related.refl markers .empty

/-- An actual filtered variable retains its selected tracked profile or its exact fixed capture. -/
theorem reference (bound index : Nat) : Fusion bound (.var index : Syntax Symbol Guard) := by
  intro markers Atom reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right
    _firstDepth _secondDepth _firstContext _secondContext _aliases tests paired _firstReplacements _secondReplacements available _secondAvailable
    firstBuild secondBuild _firstGrowth _secondGrowth firstFilter secondFilter firstDone secondDone
  have firstSelected : (inputs.map (input firstNames))[index]?.getD .empty = firstRaw :=
    (Outcome.done.inj (by simpa only [build] using firstBuild)).1
  have secondSelected : (inputs.map (input secondNames))[index]?.getD .empty = secondRaw :=
    (Outcome.done.inj (by simpa only [build] using secondBuild)).1
  have slot := slot_at paired index
  rw [firstSelected,secondSelected] at slot
  by_cases bare : ∃ name, firstRaw = .reference name
  · obtain ⟨name,rfl⟩ := bare
    cases secondRaw with
    | empty | node | union | mu => cases slot
    | reference other =>
        have firstSame : firstFiltered = .reference name := (congrArg Prod.fst firstFilter).symm
        have secondSame : secondFiltered = .reference other := (congrArg Prod.fst secondFilter).symm
        subst firstFiltered secondFiltered
        rw [reference_execute] at firstDone secondDone
        obtain ⟨rfl,_⟩ := Outcome.done.inj firstDone
        obtain ⟨rfl,_⟩ := Outcome.done.inj secondDone
        exact slot
  · have nonreference : ∀ name, firstRaw ≠ .reference name := fun name same => bare ⟨name,same⟩
    obtain ⟨same,agree⟩ := fixed_slot slot nonreference
    rw [←same] at secondFilter
    have ownTests := fixed_tests inputs firstNames secondNames firstOwn secondOwn index firstRaw firstSelected nonreference tests
    have filtered := filters_same reader ready.semantic.1.normal firstRaw available firstOwn secondOwn ownTests
    rw [firstFilter,secondFilter] at filtered
    obtain rfl := (Prod.mk.inj filtered).1
    have filteredAvailable : Available reader firstFiltered := by
      apply (InternedNestedFacts.filter_verified firstOwn firstRaw reader ready.semantic.1.normal.facts available).result firstFiltered reader
      simp only [work,firstFilter]
    have equal := InternedFreshOrdinaryStoredSubstitution.execute_congr firstFiltered firstMap secondMap reader
      ready.semantic.1.normal.facts.coherent filteredAvailable (by
        intro name present
        apply agree name
        apply filtered_free reader ready.semantic.1.normal firstRaw available firstOwn name
        simpa only [firstFilter] using present)
    rw [firstDone,secondDone] at equal
    obtain ⟨rfl,_⟩ := Outcome.done.inj equal
    exact Related.refl markers _

private theorem output_available (reader : State Symbol Guard) (ready : Ready reader)
    (raw filtered result : Value Symbol Guard) (own : Reference) (environment : Environment Symbol Guard)
    (available : Available reader raw) (replacements : Replacements reader environment)
    (filter : run (withoutSelfReference own raw) reader = (filtered,reader))
    (actual : execute filtered environment reader = .done result reader) : Available reader result := by
  have filteredAvailable : Available reader filtered := by
    apply (InternedNestedFacts.filter_verified own raw reader ready.semantic.1.normal.facts available).result filtered reader
    simp only [work,filter]
  exact (InternedFreshOrdinaryFacts.build_verified (InternedStoredSubstitution.encode (InternedStoredSubstitution.leaves filtered) [] filtered)
    ((InternedStoredSubstitution.leaves filtered).map (InternedStoredSubstitution.input environment)) reader ready.semantic.1.normal.facts
    (InternedStoredSubstitution.inputs_available filtered environment reader filteredAvailable replacements)).result result reader actual

/-- Empty tracking recovers the full earlier bounded Empty contract with its original slot premises. -/
theorem to_empty (bound : Nat) (expression : Syntax Symbol Guard) (tracked : Fusion bound expression) :
    SourceCurrentBoundedFilteredFusion.Fusion bound expression := by
  intro Atom reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right
    firstDepth secondDepth firstContext secondContext aliases tests paired firstReplacements secondReplacements firstAvailable secondAvailable
    firstBuild secondBuild firstGrowth secondGrowth firstFilter secondFilter firstDone secondDone
  have compared := tracked [] reader ready inputs firstNames secondNames firstOwn secondOwn firstMap secondMap
    firstBefore secondBefore firstRawHeap secondRawHeap firstRaw secondRaw firstFiltered secondFiltered left right
    firstDepth secondDepth firstContext secondContext aliases tests
    (paired_from_empty reader ready firstMap secondMap firstReplacements secondReplacements _ _ paired)
    firstReplacements secondReplacements firstAvailable secondAvailable firstBuild secondBuild firstGrowth secondGrowth
    firstFilter secondFilter firstDone secondDone
  exact compared.empty reader ready
    (output_available reader ready firstRaw firstFiltered left firstOwn firstMap firstAvailable firstReplacements firstFilter firstDone)
    (output_available reader ready secondRaw secondFiltered right secondOwn secondMap secondAvailable secondReplacements secondFilter secondDone)

end MicroCFTA.SourceCurrentTrackedFilteredFusion
