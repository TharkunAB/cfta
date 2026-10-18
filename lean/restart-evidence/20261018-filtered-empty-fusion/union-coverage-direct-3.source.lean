import MicroCFTA.SourceCurrentGeneratedUnionPreparation
import MicroCFTA.SourceCurrentLiteralPartsObservations

/-!
# Exact parts of filtered source-union reconstruction

Each returned literal atom or ordinary row comes from a retained original
source member. A bare self member is retained only when the entire parent
is that bare self. Member filters can be cold before finite preparation.
The result uses actual warm calls after that preparation.
-/
namespace MicroCFTA.SourceCurrentFilteredUnionCoverage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome work)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentLiteralRootParts (Literal Row SameParts)
open SourceEqualityRequiredCache (Ready)
open InternedBinderProtocol (Reference)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem filtered_available (reader : State Symbol Guard) (ready : Ready reader)
    (own : Reference) (raw filtered : Value Symbol Guard) (available : Available reader raw)
    (actual : run (withoutSelfReference own raw) reader = (filtered,reader)) :
    Available reader filtered := by
  apply (InternedNestedFacts.filter_verified own raw reader ready.semantic.1.normal.facts available).result filtered reader
  simp only [work,actual]

private theorem output_available (reader : State Symbol Guard) (ready : Ready reader)
    (raw result : Value Symbol Guard) (environment : Environment Symbol Guard)
    (available : Available reader raw) (replacements : Replacements reader environment)
    (actual : execute raw environment reader = .done result reader) : Available reader result :=
  (InternedFreshOrdinaryFacts.build_verified _ _ reader ready.semantic.1.normal.facts
    (InternedStoredSubstitution.inputs_available raw environment reader available replacements)).result result reader actual

private theorem empty_parts (value : Value Symbol Guard) (empty : value.referenceOf = .empty) :
    (∀ atom, ¬ Literal value atom) ∧ ∀ row, ¬ Row value row := by
  have same := (InternedEmptyNormalization.reference_empty value).mp empty
  subst value
  constructor <;> intro _ impossible <;> cases impossible

private theorem no_parts_empty (reader : State Symbol Guard) (ready : Ready reader)
    (value : Value Symbol Guard) (available : Available reader value)
    (noAtoms : ∀ atom, ¬ Literal value atom) (noRows : ∀ row, ¬ Row value row) :
    value.referenceOf = .empty := by
  apply (SourceCurrentLiteralPartsObservations.related reader reader ready.semantic.1.normal ready.semantic.1.normal
    value .empty available (empty_available reader) ?_).1.mpr rfl
  exact ⟨fun atom => iff_of_false (noAtoms atom) (by intro impossible; cases impossible),
    fun row => iff_of_false (noRows row) (by intro impossible; cases impossible)⟩

/-- Actual parent parts are exactly the parts of the retained member reconstructions. -/
theorem parts (reader : State Symbol Guard) (ready : Ready reader)
    (values : List (Value Symbol Guard)) (available : Values reader values)
    (parent filtered result : Value Symbol Guard) (own : Reference) (environment : Environment Symbol Guard)
    (made : run (makeUnion values) reader = (parent,reader))
    (parentFilter : run (withoutSelfReference own parent) reader = (filtered,reader))
    (replacements : Replacements reader environment)
    (called : execute filtered environment reader = .done result reader)
    (members : ∀ raw ∈ values, ∃ cut output,
      run (withoutSelfReference own raw) reader = (cut,reader) ∧
      execute cut environment reader = .done output reader) :
    (∀ atom, Literal result atom ↔ ∃ raw ∈ values, (raw ≠ .reference own ∨ parent = .reference own) ∧
      ∃ cut output, run (withoutSelfReference own raw) reader = (cut,reader) ∧
        execute cut environment reader = .done output reader ∧ Literal output atom) ∧
    ∀ row, Row result row ↔ ∃ raw ∈ values, (raw ≠ .reference own ∨ parent = .reference own) ∧
      ∃ cut output, run (withoutSelfReference own raw) reader = (cut,reader) ∧
        execute cut environment reader = .done output reader ∧ Row output row := by
  have parentAvailable : Available reader parent := by
    apply (InternedNestedFacts.union_verified values reader ready.semantic.1.normal.facts available).result parent reader
    simp only [work,made]
  have cutAvailable := filtered_available reader ready own parent filtered parentAvailable parentFilter
  have outputParts := SourceCurrentStoredLiteralExecutionParts.parts filtered result environment reader ready
    cutAvailable replacements called
  have rawLiteral := SourceCurrentLiteralUnionParts.literal reader ready.semantic.1.normal.facts values available
  have rawRows := SourceCurrentLiteralUnionParts.row reader ready.semantic.1.normal.facts
    ready.semantic.1.normal.live values available
  rw [made] at rawLiteral rawRows
  have selectAtom (atom : Value Symbol Guard) (found : Literal filtered atom) :
      ∃ raw ∈ values, (raw ≠ .reference own ∨ parent = .reference own) ∧
        Literal (run (withoutSelfReference own raw) reader).1 atom := by
    have original := (SourceCurrentLiteralFilterParts.literal reader ready.semantic.1.normal own parent parentAvailable atom)
    rw [parentFilter] at original
    obtain ⟨part,retained⟩ := original.mp found
    obtain ⟨raw,member,inside⟩ := (rawLiteral atom).mp part
    have keep : raw ≠ .reference own ∨ parent = .reference own := by
      by_cases bare : raw = .reference own
      · have atomSame : atom = .reference own := by rw [bare] at inside; cases inside; rfl
        exact Or.inr (retained.resolve_right (fun different => different atomSame))
      · exact Or.inl bare
    refine ⟨raw,member,keep,?_⟩
    apply (SourceCurrentLiteralFilterParts.literal reader ready.semantic.1.normal own raw (available raw member) atom).mpr
    refine ⟨inside,?_⟩
    rcases retained with bare | different
    · apply Or.inl
      apply (SourceCurrentLiteralFilterParts.bare_iff reader ready.semantic.1.normal own raw (available raw member)).mpr
      have atomSame : atom = .reference own := by rw [bare] at part; cases part; rfl
      refine ⟨atomSame ▸ inside,?_,?_⟩
      · intro other otherPart
        have parentPart := (rawLiteral other).mpr ⟨raw,member,otherPart⟩
        rw [bare] at parentPart
        cases parentPart
        rfl
      · intro row rowPart
        have parentPart := (rawRows row).mpr ⟨raw,member,rowPart⟩
        rw [bare] at parentPart
        cases parentPart
    · exact Or.inr different
  have below (raw cut output : Value Symbol Guard) (member : raw ∈ values)
      (retained : raw ≠ .reference own ∨ parent = .reference own)
      (cutCall : run (withoutSelfReference own raw) reader = (cut,reader))
      (outputCall : execute cut environment reader = .done output reader) :=
    SourceCurrentGeneratedUnionCases.retained_member reader ready values available raw parent cut filtered output result
      own environment member made retained cutCall parentFilter replacements outputCall called
  constructor
  · intro atom
    constructor
    · intro found
      obtain ⟨source,part,output,outputCall,inside⟩ := (outputParts.1 atom).mp found
      obtain ⟨raw,member,retained,part⟩ := selectAtom source part
      obtain ⟨cut,rebuilt,cutCall,storedCall⟩ := members raw member
      rw [cutCall] at part
      have child := SourceCurrentStoredLiteralExecutionParts.parts cut rebuilt environment reader ready
        (filtered_available reader ready own raw cut (available raw member) cutCall) replacements storedCall
      exact ⟨raw,member,retained,cut,rebuilt,cutCall,storedCall,(child.1 atom).mpr ⟨source,part,output,outputCall,inside⟩⟩
    · rintro ⟨raw,member,retained,cut,output,cutCall,outputCall,found⟩
      exact (below raw cut output member retained cutCall outputCall).1 atom found
  · intro row
    constructor
    · intro found
      rcases (outputParts.2 row).mp found with atom | ordinary
      · obtain ⟨source,part,output,outputCall,inside⟩ := atom
        obtain ⟨raw,member,retained,part⟩ := selectAtom source part
        obtain ⟨cut,rebuilt,cutCall,storedCall⟩ := members raw member
        rw [cutCall] at part
        have child := SourceCurrentStoredLiteralExecutionParts.parts cut rebuilt environment reader ready
          (filtered_available reader ready own raw cut (available raw member) cutCall) replacements storedCall
        exact ⟨raw,member,retained,cut,rebuilt,cutCall,storedCall,
          (child.2 row).mpr (Or.inl ⟨source,part,output,outputCall,inside⟩)⟩
      · obtain ⟨source,part,outputCall,live⟩ := ordinary
        have original := SourceCurrentLiteralFilterParts.row reader ready.semantic.1.normal own parent parentAvailable source
        rw [parentFilter] at original
        obtain ⟨raw,member,inside⟩ := (rawRows source).mp (original.mp part)
        have retained : raw ≠ .reference own ∨ parent = .reference own := by
          apply Or.inl
          intro same
          rw [same] at inside
          cases inside
        obtain ⟨cut,rebuilt,cutCall,storedCall⟩ := members raw member
        have selected := (SourceCurrentLiteralFilterParts.row reader ready.semantic.1.normal own raw
          (available raw member) source).mpr inside
        rw [cutCall] at selected
        have child := SourceCurrentStoredLiteralExecutionParts.parts cut rebuilt environment reader ready
          (filtered_available reader ready own raw cut (available raw member) cutCall) replacements storedCall
        exact ⟨raw,member,retained,cut,rebuilt,cutCall,storedCall,
          (child.2 row).mpr (Or.inr ⟨source,selected,outputCall,live⟩)⟩
    · rintro ⟨raw,member,retained,cut,output,cutCall,outputCall,found⟩
      exact (below raw cut output member retained cutCall outputCall).2 row found

/-- The parent is physically Empty exactly when every retained member reconstruction is Empty. -/
theorem empty_iff (reader : State Symbol Guard) (ready : Ready reader)
    (values : List (Value Symbol Guard)) (available : Values reader values)
    (parent filtered result : Value Symbol Guard) (own : Reference) (environment : Environment Symbol Guard)
    (made : run (makeUnion values) reader = (parent,reader))
    (parentFilter : run (withoutSelfReference own parent) reader = (filtered,reader))
    (replacements : Replacements reader environment)
    (called : execute filtered environment reader = .done result reader)
    (members : ∀ raw ∈ values, ∃ cut output,
      run (withoutSelfReference own raw) reader = (cut,reader) ∧
      execute cut environment reader = .done output reader) :
    result.referenceOf = .empty ↔ ∀ raw ∈ values,
      (raw ≠ .reference own ∨ parent = .reference own) → ∀ cut output,
      run (withoutSelfReference own raw) reader = (cut,reader) →
      execute cut environment reader = .done output reader → output.referenceOf = .empty := by
  have covered := parts reader ready values available parent filtered result own environment made parentFilter replacements called members
  constructor
  · intro empty raw member retained cut output cutCall outputCall
    have resultParts := empty_parts result empty
    apply no_parts_empty reader ready output
      (output_available reader ready cut output environment
        (filtered_available reader ready own raw cut (available raw member) cutCall) replacements outputCall)
    · intro atom found
      exact resultParts.1 atom ((covered.1 atom).mpr ⟨raw,member,retained,cut,output,cutCall,outputCall,found⟩)
    · intro row found
      exact resultParts.2 row ((covered.2 row).mpr ⟨raw,member,retained,cut,output,cutCall,outputCall,found⟩)
  · intro empty
    have parentAvailable : Available reader parent := by
      apply (InternedNestedFacts.union_verified values reader ready.semantic.1.normal.facts available).result parent reader
      simp only [work,made]
    apply no_parts_empty reader ready result
      (output_available reader ready filtered result environment
        (filtered_available reader ready own parent filtered parentAvailable parentFilter) replacements called)
    · intro atom found
      obtain ⟨raw,member,retained,cut,output,cutCall,outputCall,part⟩ := (covered.1 atom).mp found
      exact (empty_parts output (empty raw member retained cut output cutCall outputCall)).1 atom part
    · intro row found
      obtain ⟨raw,member,retained,cut,output,cutCall,outputCall,part⟩ := (covered.2 row).mp found
      exact (empty_parts output (empty raw member retained cut output cutCall outputCall)).2 row part

end MicroCFTA.SourceCurrentFilteredUnionCoverage
