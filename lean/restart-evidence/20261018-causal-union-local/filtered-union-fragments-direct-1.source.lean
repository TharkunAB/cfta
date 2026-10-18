import MicroCFTA.SourceCurrentFilteredUnionCoverage

/-!
# Indexed original fragments of a filtered union result

Actual ordered member filters and stored calls retain their original
indices. The parent result has exactly the literal atoms and full rows
of those indexed outputs that satisfy the bare-self retention rule.
Mu atoms stay opaque. No returned-member comparison law is assumed.
-/
namespace MicroCFTA.SourceCurrentFilteredUnionFragments
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceEqualityRequiredCache (Ready)
open InternedBinderProtocol (Reference)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem indexed (reader : State Symbol Guard) (own : Reference) (environment : Environment Symbol Guard)
    {values filters outputs : List (Value Symbol Guard)}
    (filterCalls : All₂ (fun raw cut => run (withoutSelfReference own raw) reader = (cut,reader)) values filters)
    (storedCalls : All₂ (fun cut output => execute cut environment reader = .done output reader) filters outputs)
    (index : Nat) (raw : Value Symbol Guard) (found : values[index]? = some raw) :
    ∃ cut output, filters[index]? = some cut ∧ outputs[index]? = some output ∧
      run (withoutSelfReference own raw) reader = (cut,reader) ∧
      execute cut environment reader = .done output reader := by
  induction filterCalls generalizing outputs index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | @cons rawHead cut values filters first rest ih =>
      cases storedCalls with
      | @cons _ output _ outputs stored tail =>
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero,Option.some.injEq] at found
              subst raw
              exact ⟨cut,output,rfl,rfl,first,stored⟩
          | succ index => exact ih tail index found

/-- Both parent fragment kinds are exactly the fragments at retained original member indices. -/
theorem parts (reader : State Symbol Guard) (ready : Ready reader)
    (values filters outputs : List (Value Symbol Guard)) (available : Values reader values)
    (parent filtered result : Value Symbol Guard) (own : Reference) (environment : Environment Symbol Guard)
    (made : run (makeUnion values) reader = (parent,reader))
    (parentFilter : run (withoutSelfReference own parent) reader = (filtered,reader))
    (replacements : Replacements reader environment)
    (called : execute filtered environment reader = .done result reader)
    (filterCalls : All₂ (fun raw cut => run (withoutSelfReference own raw) reader = (cut,reader)) values filters)
    (storedCalls : All₂ (fun cut output => execute cut environment reader = .done output reader) filters outputs) :
    (∀ atom, Literal result atom ↔ ∃ index raw cut output,
      values[index]? = some raw ∧ filters[index]? = some cut ∧ outputs[index]? = some output ∧
      (raw ≠ .reference own ∨ parent = .reference own) ∧ Literal output atom) ∧
    ∀ row, Row result row ↔ ∃ index raw cut output,
      values[index]? = some raw ∧ filters[index]? = some cut ∧ outputs[index]? = some output ∧
      (raw ≠ .reference own ∨ parent = .reference own) ∧ Row output row := by
  have schedules (raw : Value Symbol Guard) (member : raw ∈ values) :
      ∃ cut output, run (withoutSelfReference own raw) reader = (cut,reader) ∧
        execute cut environment reader = .done output reader := by
    obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨cut,output,_,_,filterCall,storedCall⟩ := indexed reader own environment filterCalls storedCalls index raw found
    exact ⟨cut,output,filterCall,storedCall⟩
  have covered := SourceCurrentFilteredUnionCoverage.parts reader ready values available parent filtered result own environment
    made parentFilter replacements called schedules
  have select (raw cut output : Value Symbol Guard) (member : raw ∈ values)
      (filterCall : run (withoutSelfReference own raw) reader = (cut,reader))
      (storedCall : execute cut environment reader = .done output reader) :
      ∃ index, values[index]? = some raw ∧ filters[index]? = some cut ∧ outputs[index]? = some output := by
    obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨actualCut,actualOutput,cutFound,outputFound,actualFilter,actualStored⟩ :=
      indexed reader own environment filterCalls storedCalls index raw found
    have cutSame := congrArg Prod.fst (filterCall.symm.trans actualFilter)
    cases cutSame
    have outputSame := (Outcome.done.inj (storedCall.symm.trans actualStored)).1
    cases outputSame
    exact ⟨index,found,cutFound,outputFound⟩
  have calls (index : Nat) (raw cut output : Value Symbol Guard)
      (found : values[index]? = some raw) (cutFound : filters[index]? = some cut)
      (outputFound : outputs[index]? = some output) :
      run (withoutSelfReference own raw) reader = (cut,reader) ∧
      execute cut environment reader = .done output reader := by
    obtain ⟨actualCut,actualOutput,actualCutFound,actualOutputFound,filterCall,storedCall⟩ :=
      indexed reader own environment filterCalls storedCalls index raw found
    have sameCut := Option.some.inj (cutFound.symm.trans actualCutFound)
    cases sameCut
    have sameOutput := Option.some.inj (outputFound.symm.trans actualOutputFound)
    cases sameOutput
    exact ⟨filterCall,storedCall⟩
  constructor
  · intro atom
    constructor
    · intro found
      obtain ⟨raw,member,retained,cut,output,filterCall,storedCall,inside⟩ := (covered.1 atom).mp found
      obtain ⟨index,found,cutFound,outputFound⟩ := select raw cut output member filterCall storedCall
      exact ⟨index,raw,cut,output,found,cutFound,outputFound,retained,inside⟩
    · rintro ⟨index,raw,cut,output,found,cutFound,outputFound,retained,inside⟩
      obtain ⟨filterCall,storedCall⟩ := calls index raw cut output found cutFound outputFound
      exact (covered.1 atom).mpr ⟨raw,List.mem_of_getElem? found,retained,cut,output,filterCall,storedCall,inside⟩
  · intro row
    constructor
    · intro found
      obtain ⟨raw,member,retained,cut,output,filterCall,storedCall,inside⟩ := (covered.2 row).mp found
      obtain ⟨index,found,cutFound,outputFound⟩ := select raw cut output member filterCall storedCall
      exact ⟨index,raw,cut,output,found,cutFound,outputFound,retained,inside⟩
    · rintro ⟨index,raw,cut,output,found,cutFound,outputFound,retained,inside⟩
      obtain ⟨filterCall,storedCall⟩ := calls index raw cut output found cutFound outputFound
      exact (covered.2 row).mpr ⟨raw,List.mem_of_getElem? found,retained,cut,output,filterCall,storedCall,inside⟩

end MicroCFTA.SourceCurrentFilteredUnionFragments
