import MicroCFTA.InternedFreshOrdinaryLiveInputs
import MicroCFTA.InternedObservedAbsence
import MicroCFTA.InternedNestedSpecialization

/-!
# Completed callback comparison with fixed captured values

Agreement is required only for the surviving varying reference labels.
Both actual source runs retain complete semantic contexts and grow to one
coherent cache. Fixed lexical values remain identical in both executions.
-/
namespace MicroCFTA.InternedFreshOrdinaryLiveInputContext
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work work_correct)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedNestedSpecialization
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedBinderProtocol (Reference)

/-- Completed source histories agree when their live abstract inputs have equal references. -/
def Replay [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) : Prop :=
  ∀ {Atom : Type} (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference),
    (∀ atom ∈ liveInputs expression inputs, Sum.elim id firstNames atom = Sum.elim id secondNames atom) →
    ∀ left right common afterLeft afterRight,
      Context left (inputs.map (input firstNames)) → Context right (inputs.map (input secondNames)) → Coherent common →
      ∀ first second,
        build expression (inputs.map (input firstNames)) left = .done first afterLeft →
        build expression (inputs.map (input secondNames)) right = .done second afterRight →
        Grows afterLeft common → Grows afterRight common → first = second

/-- Equal actual probe names preserve live-input agreement through the root filter. -/
theorem callback_same [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (recurse : Replay expression) (smart : Bool)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference) (name : Reference)
    (agree : ∀ atom ∈ liveInputs (.binder smart expression) inputs, Sum.elim id firstNames atom = Sum.elim id secondNames atom)
    (left right common afterLeft afterRight : State Symbol Guard)
    (lc : Context left (inputs.map (input firstNames))) (rc : Context right (inputs.map (input secondNames)))
    (coherent : Coherent common) (la : Available left (.reference name)) (ra : Available right (.reference name))
    (first second : Value Symbol Guard)
    (firstDone : callback expression (inputs.map (input firstNames)) name left = .done first afterLeft)
    (secondDone : callback expression (inputs.map (input secondNames)) name right = .done second afterRight)
    (lg : Grows afterLeft common) (rg : Grows afterRight common) : first = second := by
  obtain ⟨rawLeft, middleLeft, rawDoneLeft, filterDoneLeft⟩ := bind_done _ _ _ _ firstDone
  obtain ⟨rawRight, middleRight, rawDoneRight, filterDoneRight⟩ := bind_done _ _ _ _ secondDone
  have localLeft := lc.local name la
  have localRight := rc.local name ra
  have middleContext : Context middleLeft (.reference name :: inputs.map (input firstNames)) := by
    simpa only [List.map_cons, rawDoneLeft, Outcome.state] using localLeft.build expression
  have middleRightContext : Context middleRight (.reference name :: inputs.map (input secondNames)) := by
    simpa only [List.map_cons, rawDoneRight, Outcome.state] using localRight.build expression
  have leftFilterGrowth : Grows middleLeft afterLeft := by
    simpa only [filterDoneLeft, Outcome.state] using
      (work_correct (withoutSelfReference name rawLeft) middleLeft middleContext.normal.facts.coherent.valid).2
  have rightFilterGrowth : Grows middleRight afterRight := by
    simpa only [filterDoneRight, Outcome.state] using
      (work_correct (withoutSelfReference name rawRight) middleRight middleRightContext.normal.facts.coherent.valid).2
  have same := recurse (.inr (.inl ()) :: inputs.map liftInput)
    (Sum.elim (fun _ => name) firstNames) (Sum.elim (fun _ => name) secondNames)
    (callback_agreement expression smart inputs firstNames secondNames name agree)
    left right common middleLeft middleRight
    (by simpa only [local_inputs] using localLeft)
    (by simpa only [local_inputs] using localRight)
    coherent rawLeft rawRight
    (by simpa only [local_inputs] using rawDoneLeft)
    (by simpa only [local_inputs] using rawDoneRight)
    (grows_trans leftFilterGrowth lg) (grows_trans rightFilterGrowth rg)
  subst rawRight
  simp only [work, Outcome.done.injEq] at filterDoneLeft filterDoneRight
  have filtered := InternedObservedAbsence.run_shared (withoutSelfReference name rawLeft) middleLeft middleRight common
    middleContext.normal.facts.coherent.valid middleRightContext.normal.facts.coherent.valid
    (by simpa only [filterDoneLeft.2] using lg) (by simpa only [filterDoneRight.2] using rg)
  exact filterDoneLeft.1.symm.trans (filtered.trans filterDoneRight.1)

end MicroCFTA.InternedFreshOrdinaryLiveInputContext
