import MicroCFTA.SourceCurrentGeneratedUnionPreparation

/-!
# Original union fragments at the actual parent reader

A warm normalized parent supplies literal-atom calls and full row calls
at its original reader. The original ordinary member groups need not have
warm stored calls there. Historical source members retain their indices.
This module proves literal coverage and actual calls, not a simulation law.
-/
namespace MicroCFTA.SourceCurrentFixedReaderUnionFragments
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentStoredNodeExpansion (RowCalls)
open SourceEqualityRequiredCache (Ready)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual warm union parent supplies original indexed fragments and calls at that same reader. -/
theorem source (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after reader : State Symbol Guard) (context : Context before inputs)
    (raw : Value Symbol Guard) (actual : build (.union expressions) inputs before = .done raw after)
    (ready : Ready reader) (growth : Grows after reader) (available : Available reader raw)
    (own : Reference) (environment : Environment Symbol Guard) (replacements : Replacements reader environment)
    (filtered result : Value Symbol Guard)
    (filterCall : run (withoutSelfReference own raw) reader = (filtered,reader))
    (storedCall : execute filtered environment reader = .done result reader) :
    ∃ values middle,
      buildMany expressions inputs before = .done values middle ∧ Context middle inputs ∧
      run (makeUnion values) middle = (raw,after) ∧ Grows middle reader ∧ Values reader values ∧
      buildMany expressions inputs reader = .done values reader ∧
      run (makeUnion values) reader = (raw,reader) ∧
      All₂ (fun expression value => ∃ current returned,
        Context current inputs ∧ build expression inputs current = .done value returned ∧
        Grows returned reader ∧ build expression inputs reader = .done value reader) expressions values ∧
      (∀ atom, Literal result atom ↔ ∃ (index : Nat) (member source output : Value Symbol Guard),
        values[index]? = some member ∧ Literal member source ∧
        (raw = .reference own ∨ source ≠ .reference own) ∧
        execute source environment reader = .done output reader ∧ Literal output atom) ∧
      (∀ row, Row result row ↔
        (∃ (index : Nat) (member source output : Value Symbol Guard),
          values[index]? = some member ∧ Literal member source ∧
          (raw = .reference own ∨ source ≠ .reference own) ∧
          execute source environment reader = .done output reader ∧ Row output row) ∨
        ∃ (index : Nat) (member : Value Symbol Guard) (original : EdgeValue Symbol Guard),
          values[index]? = some member ∧ Row member original ∧ RowCalls environment reader original row ∧
          (!(row.children.any (fun child => child.referenceOf == .empty))) = true) ∧
      (∀ (index : Nat) (member atom : Value Symbol Guard), values[index]? = some member →
        Literal member atom → (raw = .reference own ∨ atom ≠ .reference own) →
        ∃ output, execute atom environment reader = .done output reader) ∧
      (∀ (index : Nat) (member : Value Symbol Guard) (original : EdgeValue Symbol Guard),
        values[index]? = some member → Row member original → ∃ output, RowCalls environment reader original output) := by
  obtain ⟨values,middle,many,middleContext,made,middleGrowth,valuesAvailable,manyWarm,madeWarm,sources⟩ :=
    SourceCurrentGeneratedUnionPreparation.source_members expressions inputs before after reader context raw actual ready growth available
  have filteredAvailable : Available reader filtered := by
    apply (InternedNestedFacts.filter_verified own raw reader ready.semantic.1.normal.facts available).result filtered reader
    simp only [work,filterCall]
  have literals (atom : Value Symbol Guard) : Literal filtered atom ↔
      ∃ (index : Nat) (member : Value Symbol Guard), values[index]? = some member ∧ Literal member atom ∧
        (raw = .reference own ∨ atom ≠ .reference own) := by
    have cut := SourceCurrentLiteralFilterParts.literal reader ready.semantic.1.normal own raw available atom
    rw [filterCall] at cut
    have original := SourceCurrentLiteralUnionParts.literal reader ready.semantic.1.normal.facts values valuesAvailable atom
    rw [madeWarm] at original
    constructor
    · intro found
      obtain ⟨part,retained⟩ := cut.mp found
      obtain ⟨member,present,inside⟩ := original.mp part
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp present
      exact ⟨index,member,found,inside,retained⟩
    · rintro ⟨index,member,found,inside,retained⟩
      exact cut.mpr ⟨original.mpr ⟨member,List.mem_of_getElem? found,inside⟩,retained⟩
  have rows (row : EdgeValue Symbol Guard) : Row filtered row ↔
      ∃ (index : Nat) (member : Value Symbol Guard), values[index]? = some member ∧ Row member row := by
    have cut := SourceCurrentLiteralFilterParts.row reader ready.semantic.1.normal own raw available row
    rw [filterCall] at cut
    have original := SourceCurrentLiteralUnionParts.row reader ready.semantic.1.normal.facts
      ready.semantic.1.normal.live values valuesAvailable row
    rw [madeWarm] at original
    constructor
    · intro found
      obtain ⟨member,present,inside⟩ := original.mp (cut.mp found)
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp present
      exact ⟨index,member,found,inside⟩
    · rintro ⟨index,member,found,inside⟩
      exact cut.mpr (original.mpr ⟨member,List.mem_of_getElem? found,inside⟩)
  have parts := SourceCurrentStoredLiteralExecutionParts.parts filtered result environment reader
    ready filteredAvailable replacements storedCall
  refine ⟨values,middle,many,middleContext,made,middleGrowth,valuesAvailable,manyWarm,madeWarm,sources,?_,?_,?_,?_⟩
  · intro atom
    constructor
    · intro found
      obtain ⟨source,part,output,called,inside⟩ := (parts.1 atom).mp found
      obtain ⟨index,member,present,original,retained⟩ := (literals source).mp part
      exact ⟨index,member,source,output,present,original,retained,called,inside⟩
    · rintro ⟨index,member,source,output,present,original,retained,called,inside⟩
      exact (parts.1 atom).mpr ⟨source,(literals source).mpr ⟨index,member,present,original,retained⟩,output,called,inside⟩
  · intro row
    constructor
    · intro found
      rcases (parts.2 row).mp found with atom | ordinary
      · obtain ⟨source,part,output,called,inside⟩ := atom
        obtain ⟨index,member,present,original,retained⟩ := (literals source).mp part
        exact Or.inl ⟨index,member,source,output,present,original,retained,called,inside⟩
      · obtain ⟨original,part,called,live⟩ := ordinary
        obtain ⟨index,member,present,inside⟩ := (rows original).mp part
        exact Or.inr ⟨index,member,original,present,inside,called,live⟩
    · rintro (⟨index,member,source,output,present,original,retained,called,inside⟩ |
        ⟨index,member,original,present,inside,called,live⟩)
      · exact (parts.2 row).mpr (Or.inl
          ⟨source,(literals source).mpr ⟨index,member,present,original,retained⟩,output,called,inside⟩)
      · exact (parts.2 row).mpr (Or.inr
          ⟨original,(rows original).mpr ⟨index,member,present,inside⟩,called,live⟩)
  · intro index member atom found part retained
    exact SourceCurrentStoredLiteralExecutionParts.atom filtered result environment reader ready filteredAvailable replacements
      storedCall atom ((literals atom).mpr ⟨index,member,found,part,retained⟩)
  · intro index member original found part
    exact SourceCurrentStoredLiteralExecutionParts.row filtered result environment reader ready filteredAvailable replacements
      storedCall original ((rows original).mpr ⟨index,member,found,part⟩)

end MicroCFTA.SourceCurrentFixedReaderUnionFragments
