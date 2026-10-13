import MicroCFTA.InternedNormalizedProfileReflection
import MicroCFTA.InternedNestedProfiles

/-!
# Source-derived paired callback empty and direct-local observations

The complete executor derives each normalized callback profile. The
name-map law then reflects EmptyNode and the exact paired bare locals.
This theorem includes arbitrary nested binders and actual cache hits.
It does not assume a relation between the completed callback values.
-/
namespace MicroCFTA.InternedCallbackReflection
open InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback
open InternedProbeProvenance InternedNestedProvenance InternedStoredMuOrigins
open InternedRootProfile InternedProfileSemantics InternedNestedProfiles InternedProfileExecutionFacts
open InternedBinderProtocol (Reference)

/-- Actual full nested callbacks reflect empty and direct-local results from mapped original lexical inputs. -/
theorem callback_reflects [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (function : Reference → Reference) (firstName secondName : Reference)
    (localName : ∀ name, function name = secondName ↔ name = firstName)
    (firstEnvironment secondEnvironment : List (Value Symbol Guard))
    (mapped : secondEnvironment.map profile = (firstEnvironment.map profile).map (mapNames function))
    (left right : State Symbol Guard) (ln : Normal left) (rn : Normal right)
    (li : Values left firstEnvironment) (ri : Values right secondEnvironment)
    (la : Available left (.reference firstName)) (ra : Available right (.reference secondName))
    (lh : InternedProfileHeap.Heap left) (rh : InternedProfileHeap.Heap right)
    (first second : Value Symbol Guard) (afterFirst afterSecond : State Symbol Guard)
    (firstDone : callback expression firstEnvironment firstName left = .done first afterFirst)
    (secondDone : callback expression secondEnvironment secondName right = .done second afterSecond) :
    (first.referenceOf = .empty ↔ second.referenceOf = .empty) ∧
      (first = .reference firstName ↔ second = .reference secondName) := by
  have firstInputs : Values left (.reference firstName :: firstEnvironment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact la
    · exact li value member
  have secondInputs : Values right (.reference secondName :: secondEnvironment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ra
    · exact ri value member
  have firstBody := build_profile expression (.reference firstName :: firstEnvironment) left ln firstInputs lh
  have secondBody := build_profile expression (.reference secondName :: secondEnvironment) right rn secondInputs rh
  have firstChecked := callback_checked expression firstEnvironment firstName left ln firstInputs
    (by simpa only [List.map_cons, profile] using firstBody)
  have secondChecked := callback_checked expression secondEnvironment secondName right rn secondInputs
    (by simpa only [List.map_cons, profile] using secondBody)
  have firstNormal : Normal afterFirst := by
    simpa only [firstDone, Outcome.state] using callback_normal expression firstEnvironment firstName left ln firstInputs
  have secondNormal : Normal afterSecond := by
    simpa only [secondDone, Outcome.state] using callback_normal expression secondEnvironment secondName right rn secondInputs
  exact InternedNormalizedProfileReflection.reflects expression function firstName secondName localName
    (firstEnvironment.map profile) (secondEnvironment.map profile) mapped first second afterFirst afterSecond firstNormal secondNormal
    ((callback_verified expression firstEnvironment firstName left ln.facts firstInputs).result first afterFirst firstDone)
    ((callback_verified expression secondEnvironment secondName right rn.facts secondInputs).result second afterSecond secondDone)
    (firstChecked.result first afterFirst firstDone) (secondChecked.result second afterSecond secondDone)

/-- A completed empty-cache prefix derives both source invariants needed by later callback comparison. -/
theorem completed_prefix [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (completed : build expression [] empty = .done value state) : Normal state ∧ InternedProfileHeap.Heap state := by
  constructor
  · simpa only [completed, Outcome.state] using build_normal expression [] empty empty_normal (by intro value member; cases member)
  · simpa only [completed, Outcome.state] using closed_heap expression

end MicroCFTA.InternedCallbackReflection
