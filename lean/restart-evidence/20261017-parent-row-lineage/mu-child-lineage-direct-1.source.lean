import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.SourceCurrentNativeNormalizationInputs
import MicroCFTA.InternedFreshOrdinaryLiveInputReplay
import MicroCFTA.InternedStoredSubstitutionBindings

/-!
# Actual reconstruction of independent callback children

Pure source support identifies children that do not use a varying callback
argument. Their raw calls agree. Compatible replacement maps then construct
the same stored result in sequence, including arbitrary nested Mu records.
This is the independent-child case. Active children remain outside this law.
-/
namespace MicroCFTA.SourceCurrentStoredMuChildLineage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeNormalizationInputs (support)
open InternedBinderProtocol (Reference)
variable {Atom : Type}

private theorem live_supported (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (label : Sum Reference Atom)
    (member : label ∈ liveInputs expression inputs) : label ∈ support expression inputs := by
  apply InternedFreeNameInputSubset.evaluate_included expression _ _ _ ?_ label member
  intro index selected included
  cases found : inputs[index]? with
  | none => simp only [List.getElem?_map,found,Option.map_none,Option.getD_none,List.not_mem_nil] at included
  | some value =>
      simp only [List.getElem?_map,found,Option.map_some,Option.getD_some] at included ⊢
      cases value with
      | inl value => cases included
      | inr atom => exact included

/-- Independent source children construct one identical sequential stored result under compatible outer maps. -/
theorem independent [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference)
    (before after later final common : State Symbol Guard)
    (firstContext : Context before (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)))
    (secondContext : Context later (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)))
    (rawFirst rawSecond : Value Symbol Guard)
    (firstActual : build expression (inputs.map (InternedFreshOrdinaryLiveInputs.input firstNames)) before =
      .done rawFirst after)
    (secondActual : build expression (inputs.map (InternedFreshOrdinaryLiveInputs.input secondNames)) later =
      .done rawSecond final)
    (firstGrowth : Grows after common) (secondGrowth : Grows final common)
    (independent : ∀ atom, .inr atom ∉ support expression inputs)
    (firstEnvironment secondEnvironment : Environment Symbol Guard)
    (compatible : ∀ name, .inl name ∈ support expression inputs → firstEnvironment name = secondEnvironment name)
    (ready : Ready common) (available : Available common rawFirst)
    (replacements : Replacements common firstEnvironment) :
    ∃ result resultHeap, rawFirst = rawSecond ∧
      execute rawFirst firstEnvironment common = .done result resultHeap ∧
      execute rawSecond secondEnvironment resultHeap = .done result resultHeap ∧
      execute rawFirst firstEnvironment resultHeap = .done result resultHeap ∧
      Keeps common resultHeap ∧ Available resultHeap result ∧
      Nonempty (SourceCurrentNativeMuPublication.History common resultHeap) := by
  have agreement : ∀ label ∈ liveInputs expression inputs,
      Sum.elim id firstNames label = Sum.elim id secondNames label := by
    intro label member
    cases label with
    | inl name => rfl
    | inr atom => exact False.elim (independent atom (live_supported expression inputs _ member))
  have same := InternedFreshOrdinaryLiveInputReplay.build_same expression inputs firstNames secondNames agreement
    before later common after final firstContext secondContext ready.semantic.1.normal.facts.coherent
    rawFirst rawSecond firstActual secondActual firstGrowth secondGrowth
  have freeAgreement : ∀ name ∈ rawFirst.free, firstEnvironment name = secondEnvironment name := by
    intro name member
    obtain ⟨label,present,equal⟩ := List.mem_map.mp
      ((SourceCurrentNativeNormalizationInputs.actual_free expression inputs firstNames before after
        firstContext rawFirst firstActual name).mp member)
    cases label with
    | inl fixed => exact equal ▸ compatible fixed present
    | inr atom => exact False.elim (independent atom present)
  obtain ⟨result,resultHeap,done,kept,output,history⟩ :=
    SourceCurrentStoredReconstruction.execute rawFirst firstEnvironment common ready available replacements
  have replay : execute rawFirst firstEnvironment resultHeap = .done result resultHeap :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves rawFirst) [] rawFirst)
      ((leaves rawFirst).map (InternedStoredSubstitution.input firstEnvironment)) common resultHeap result resultHeap
      ready.semantic.1.normal.facts.coherent.valid done (grows_refl _)
  have changed := InternedStoredSubstitutionBindings.execute_congr rawFirst firstEnvironment secondEnvironment
    resultHeap kept.ready.semantic.1.normal.facts.coherent (kept.available rawFirst available) freeAgreement
  refine ⟨result,resultHeap,same,done,?_,replay,kept,output,history⟩
  rw [← same]
  exact changed.symm.trans replay

end MicroCFTA.SourceCurrentStoredMuChildLineage
