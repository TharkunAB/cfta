import MicroCFTA.InternedFreeAbsenceContext
import MicroCFTA.InternedRequestAgreement

/-!
# Exact source replay from live lexical input agreement

Abstract atoms identify lexical inputs before reference aliases occur.
Only atoms retained by the free-name interpreter must agree. A binder
adds one atom for its local input and keeps the external atoms separate.
-/
namespace MicroCFTA.InternedLiveInputContext
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedSpecialization
open InternedFreeAbsenceContext InternedFreeNameSemantics
open InternedBinderProtocol (Reference)

/-- Interpret the live lexical inputs with distinct abstract atoms. -/
def liveInputs (expression : Syntax Symbol Guard) (atoms : List Atom) : List Atom :=
  evaluate expression (atoms.map (fun atom => some [atom])) (atoms.map (fun atom => [atom]))

/-- Completed source histories agree when their live abstract inputs have equal references. -/
def Replay [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) : Prop :=
  ∀ {Atom : Type} (atoms : List Atom) (firstMap secondMap : Atom → Reference),
    (∀ atom ∈ liveInputs expression atoms, firstMap atom = secondMap atom) →
    ∀ left right common afterLeft afterRight,
      Context left (atoms.map firstMap) → Context right (atoms.map secondMap) → Coherent common →
      ∀ first second,
        build expression ((atoms.map firstMap).map Value.reference) left = .done first afterLeft →
        build expression ((atoms.map secondMap).map Value.reference) right = .done second afterRight →
        Grows afterLeft common → Grows afterRight common → first = second

/-- The same callback local extends any agreement on live external inputs. -/
theorem callback_agreement (expression : Syntax Symbol Guard) (smart : Bool)
    (atoms : List Atom) (firstMap secondMap : Atom → Reference) (name : Reference)
    (agree : ∀ atom ∈ liveInputs (.binder smart expression) atoms, firstMap atom = secondMap atom) :
    ∀ atom ∈ liveInputs expression (Sum.inl () :: atoms.map Sum.inr),
      Sum.elim (fun _ => name) firstMap atom = Sum.elim (fun _ => name) secondMap atom := by
  intro atom member
  cases atom with
  | inl bound => rfl
  | inr external =>
      apply agree external
      rw [liveInputs, evaluate, lower_member]
      simpa only [liveInputs, List.map_cons, List.map_map, Function.comp_def,
        InternedProfileSemantics.mapNames, Option.map_some, List.map_cons, List.map_nil] using member

/-- Equal actual probe names preserve live-input agreement through the root filter. -/
theorem callback_same [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (recurse : Replay expression) (smart : Bool)
    (atoms : List Atom) (firstMap secondMap : Atom → Reference) (name : Reference)
    (agree : ∀ atom ∈ liveInputs (.binder smart expression) atoms, firstMap atom = secondMap atom)
    (left right common afterLeft afterRight : State Symbol Guard)
    (lc : Context left (atoms.map firstMap)) (rc : Context right (atoms.map secondMap))
    (coherent : Coherent common) (la : Available left (.reference name)) (ra : Available right (.reference name))
    (first second : Value Symbol Guard)
    (firstDone : callback expression ((atoms.map firstMap).map Value.reference) name left = .done first afterLeft)
    (secondDone : callback expression ((atoms.map secondMap).map Value.reference) name right = .done second afterRight)
    (lg : Grows afterLeft common) (rg : Grows afterRight common) : first = second := by
  obtain ⟨rawLeft, middleLeft, rawDoneLeft, filterDoneLeft⟩ := bind_done _ _ _ _ firstDone
  obtain ⟨rawRight, middleRight, rawDoneRight, filterDoneRight⟩ := bind_done _ _ _ _ secondDone
  have localLeft := lc.local name la
  have localRight := rc.local name ra
  have middleContext : Context middleLeft (name :: atoms.map firstMap) := by
    simpa only [List.map_cons, rawDoneLeft, Outcome.state] using localLeft.build expression
  have middleRightContext : Context middleRight (name :: atoms.map secondMap) := by
    simpa only [List.map_cons, rawDoneRight, Outcome.state] using localRight.build expression
  have leftFilterGrowth : Grows middleLeft afterLeft := by
    simpa only [filterDoneLeft, Outcome.state] using
      (work_correct (withoutSelfReference name rawLeft) middleLeft middleContext.normal.facts.coherent.valid).2
  have rightFilterGrowth : Grows middleRight afterRight := by
    simpa only [filterDoneRight, Outcome.state] using
      (work_correct (withoutSelfReference name rawRight) middleRight middleRightContext.normal.facts.coherent.valid).2
  have same := recurse (Sum.inl () :: atoms.map Sum.inr)
    (Sum.elim (fun _ => name) firstMap) (Sum.elim (fun _ => name) secondMap)
    (callback_agreement expression smart atoms firstMap secondMap name agree)
    left right common middleLeft middleRight
    (by simpa only [List.map_cons, List.map_map, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using localLeft)
    (by simpa only [List.map_cons, List.map_map, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using localRight)
    coherent rawLeft rawRight
    (by simpa only [List.map_cons, List.map_map, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using rawDoneLeft)
    (by simpa only [List.map_cons, List.map_map, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using rawDoneRight)
    (grows_trans leftFilterGrowth lg) (grows_trans rightFilterGrowth rg)
  subst rawRight
  simp only [work, Outcome.done.injEq] at filterDoneLeft filterDoneRight
  have filtered := InternedObservedAbsence.run_shared (withoutSelfReference name rawLeft) middleLeft middleRight common
    middleContext.normal.facts.coherent.valid middleRightContext.normal.facts.coherent.valid
    (by simpa only [filterDoneLeft.2] using lg) (by simpa only [filterDoneRight.2] using rg)
  exact filterDoneLeft.1.symm.trans (filtered.trans filterDoneRight.1)

end MicroCFTA.InternedLiveInputContext
