import MicroCFTA.InternedFreshOrdinaryLiveInputSupport
import MicroCFTA.InternedRecordDepthCompletion

/-!
# Actual original-input exchange from raw result absence

One completed source run determines agreement on its surviving inputs.
The changed run is constructed in a later complete semantic cache.
The premise concerns free names of the raw result. Absence from a normalized
callback result, or absence from its deep names, does not imply this premise.
-/
namespace MicroCFTA.SourceCurrentNativeInputExchange
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedBinderProtocol (Reference)

/-- Actual raw result absence supplies agreement on every surviving varying input. -/
theorem live_agreement [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input firstNames))) (value : Value Symbol Guard)
    (actual : build expression (inputs.map (input firstNames)) before = .done value after)
    (absent : ∀ atom, firstNames atom ≠ secondNames atom → firstNames atom ∉ value.free) :
    ∀ label ∈ liveInputs expression inputs,
      Sum.elim id firstNames label = Sum.elim id secondNames label := by
  intro label live
  cases label with
  | inl name => rfl
  | inr atom =>
      by_contra different
      have present := InternedFreshOrdinaryLiveInputSupport.live_free expression inputs firstNames (.inr atom) live
      have observed := (InternedFreshOrdinaryFreeNames.build_free expression _ before context.normal
        context.inputs context.freeNames context.profiles).result value after actual
      exact absent atom different ((observed (firstNames atom)).mpr present)

/-- Two completed original-input runs agree without an assumed live-input relation. -/
theorem of_completed [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference)
    (before after later final common : State Symbol Guard)
    (context : Context before (inputs.map (input firstNames)))
    (laterContext : Context later (inputs.map (input secondNames))) (coherent : Coherent common)
    (value changed : Value Symbol Guard)
    (actual : build expression (inputs.map (input firstNames)) before = .done value after)
    (changedActual : build expression (inputs.map (input secondNames)) later = .done changed final)
    (absent : ∀ atom, firstNames atom ≠ secondNames atom → firstNames atom ∉ value.free)
    (firstGrowth : Grows after common) (secondGrowth : Grows final common) : value = changed :=
  InternedFreshOrdinaryLiveInputReplay.build_same expression inputs firstNames secondNames
    (live_agreement expression inputs firstNames secondNames before after context value actual absent)
    before later common after final context laterContext coherent value changed actual changedActual firstGrowth secondGrowth

/-- A complete later cache constructs the changed original-input run with the same value. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (before after later : State Symbol Guard)
    (context : Context before (inputs.map (input firstNames)))
    (laterContext : Context later (inputs.map (input secondNames)))
    (depth : InternedFreshOrdinaryDepthHeap.Heap later) (covered : Covered [] later)
    (value : Value Symbol Guard)
    (actual : build expression (inputs.map (input firstNames)) before = .done value after)
    (absent : ∀ atom, firstNames atom ≠ secondNames atom → firstNames atom ∉ value.free)
    (growth : Grows after later) :
    ∃ final, build expression (inputs.map (input secondNames)) later = .done value final ∧
      Grows later final ∧ Context final (inputs.map (input secondNames)) := by
  obtain ⟨changed, final, changedActual⟩ := InternedRecordDepthCompletion.source_complete
    expression _ later laterContext depth covered
  have secondGrowth : Grows later final := by
    simpa only [changedActual, Outcome.state] using
      (build_correct expression _ later laterContext.normal.facts.coherent.valid).2
  have finalContext : Context final (inputs.map (input secondNames)) := by
    simpa only [changedActual, Outcome.state] using laterContext.build expression
  have same := of_completed expression inputs firstNames secondNames before after later final final
    context laterContext finalContext.normal.facts.coherent value changed actual changedActual absent
    (grows_trans growth secondGrowth) (grows_refl _)
  exact ⟨final, same.symm ▸ changedActual, secondGrowth, finalContext⟩

/-- One varying original local can change beside arbitrary fixed captured records. -/
theorem local_complete [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (captures : List (Value Symbol Guard))
    (first second : Reference) (before after later : State Symbol Guard)
    (context : Context before (.reference first :: captures))
    (laterContext : Context later (.reference second :: captures))
    (depth : InternedFreshOrdinaryDepthHeap.Heap later) (covered : Covered [] later)
    (value : Value Symbol Guard)
    (actual : build expression (.reference first :: captures) before = .done value after)
    (absent : first ∉ value.free) (growth : Grows after later) :
    ∃ final, build expression (.reference second :: captures) later = .done value final ∧
      Grows later final ∧ Context final (.reference second :: captures) := by
  let inputs : List (Sum (Value Symbol Guard) Unit) := .inr () :: captures.map Sum.inl
  have instantiate (name : Reference) : inputs.map (input (fun _ => name)) = .reference name :: captures := by
    simp [inputs, input, List.map_map, Function.comp_def]
  simpa only [instantiate] using complete expression inputs (fun _ => first) (fun _ => second)
    before after later (by simpa only [instantiate] using context)
    (by simpa only [instantiate] using laterContext) depth covered value
    (by simpa only [instantiate] using actual) (fun _ _ => absent) growth

end MicroCFTA.SourceCurrentNativeInputExchange
