import MicroCFTA.SourceCurrentGeneratedLexicalCases
import MicroCFTA.InternedNormalizationFree

/-!
# Actual filtered variable reconstruction

Reference slots use their resolved generated pairs. Fixed captures use
equal maps on their free names. Scoped self tests make both filters of
one fixed capture equal. Filtering adds no free name, so map agreement
also holds on the filtered capture. The physical Empty hypothesis applies
only to the selected resolved reference pair. No output law is assumed
for an opaque fixed capture.
-/
namespace MicroCFTA.SourceCurrentGeneratedVariableFilter
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome work)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input)
open InternedStoredSubstitution (Environment)
open InternedNestedProvenance (Values)
open InternedStoredMuOrigins (Normal)
open InternedBinderProtocol (Reference)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceCurrentReaderReplacementSlots (Paired Slot)
open SourceCurrentUsedBinderAliasTransport (Scope)
open SourceEqualityRequiredCache (Ready)

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

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual filtered variable calls retain both generated directions and resolved-reference Empty agreement. -/
theorem variable_call {Atom : Type} (reader : State Symbol Guard) (ready : Ready reader)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
    (paired : Inputs reader firstMap secondMap (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (index : Nat) (firstRaw secondRaw firstFiltered secondFiltered left right : Value Symbol Guard)
    (available : Available reader firstRaw)
    (tests : ∀ label ∈ Scope (.var index) inputs,
      Sum.elim id firstNames label = firstOwn ↔ Sum.elim id secondNames label = secondOwn)
    (firstBuild : build (.var index) (inputs.map (input firstNames)) reader = .done firstRaw reader)
    (secondBuild : build (.var index) (inputs.map (input secondNames)) reader = .done secondRaw reader)
    (firstFilter : run (withoutSelfReference firstOwn firstRaw) reader = (firstFiltered,reader))
    (secondFilter : run (withoutSelfReference secondOwn secondRaw) reader = (secondFiltered,reader))
    (firstDone : execute firstFiltered firstMap reader = .done left reader)
    (secondDone : execute secondFiltered secondMap reader = .done right reader)
    (referenceEmpty : ∀ a b, firstRaw = .reference a → secondRaw = .reference b →
      (((firstMap a).getD (.reference a)).referenceOf = .empty ↔
        ((secondMap b).getD (.reference b)).referenceOf = .empty)) :
    (Generated reader left right ∧ Generated reader right left) ∧
      (left.referenceOf = .empty ↔ right.referenceOf = .empty) := by
  have slots := SourceCurrentGeneratedLexicalCases.paired reader firstMap secondMap _ _ paired
  have firstSelected : (inputs.map (input firstNames))[index]?.getD .empty = firstRaw :=
    (Outcome.done.inj (by simpa only [build] using firstBuild)).1
  have secondSelected : (inputs.map (input secondNames))[index]?.getD .empty = secondRaw :=
    (Outcome.done.inj (by simpa only [build] using secondBuild)).1
  have slot := slot_at slots index
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
        exact ⟨slot,referenceEmpty name other rfl rfl⟩
  · have nonreference : ∀ name, firstRaw ≠ .reference name := fun name same => bare ⟨name,same⟩
    obtain ⟨same,agree⟩ := fixed_slot slot nonreference
    rw [← same] at secondFilter
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
    exact ⟨⟨.refl _,.refl _⟩,Iff.rfl⟩

end MicroCFTA.SourceCurrentGeneratedVariableFilter
