import MicroCFTA.EnumerationPureSelection

/-! Selection can expand only a listed slot with a true candidate flag. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentSelectedEligibility

open EnumerationState
open EnumerationExpandableIndex (Cached)

private theorem pickNext_member (preference : List Nat → Option Nat)
    (offered : Option (List Nat)) (target : Nat)
    (selected : pickNext preference offered = .expand target) :
    ∃ choices, offered = some choices ∧ target ∈ choices := by
  cases offered with
  | none => simp [pickNext] at selected
  | some choices =>
      refine ⟨choices, rfl, ?_⟩
      cases choices with
      | nil => simp [pickNext] at selected
      | cons first rest =>
          cases preferred : preference (first :: rest) with
          | none =>
              have same : first = target := by simpa [pickNext, preferred] using selected
              exact same ▸ List.mem_cons_self
          | some chosen =>
              by_cases allowed : chosen ∈ first :: rest
              · have same : chosen = target := by
                  simpa [pickNext, preferred, allowed] using selected
                exact same ▸ allowed
              · have same : first = target := by
                  simpa [pickNext, preferred, allowed] using selected
                exact same ▸ List.mem_cons_self

/-- The literal selection gives the original slot bound and original eligibility flag. -/
theorem next_expand_eligible {Symbol Guard : Type}
    (preference : List Nat → Option Nat) (state : Cached Symbol Guard) (target : Nat)
    (selected : EnumerationPureSelection.next preference state = .expand target) :
    target < state.core.counter ∧ state.expandable target = true := by
  obtain ⟨choices, found, member⟩ :=
    pickNext_member preference (EnumerationPureSelection.find state) target selected
  unfold EnumerationPureSelection.find at found
  dsimp only at found
  split at found
  · contradiction
  · cases found
    have candidateMember := (List.mem_filter.mp member).1
    simpa only [EnumerationIndexSelection.candidates, List.mem_filter, List.mem_range] using
      candidateMember

end MicroCFTA.SourceCurrentSelectedEligibility
