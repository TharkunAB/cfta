import MicroCFTA.IntersectTotal
import MicroCFTA.IntersectDomainEquivalence

/-!
# Least successful semantic execution bounds

The least successful bound depends on the request and its domain
observations. A completed immediate child at the preceding bound has a
strictly smaller least bound. This measure does not depend on outer roots.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage

/-- One semantic request has a finite successful execution. -/
def Completes [DecidableEq Symbol] (view : View Symbol) (call : Call Symbol) : Prop :=
  ∃ fuel result, execute view fuel call = .ok result

noncomputable section
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- A finite successful request has a least successful natural bound. -/
private theorem least_successful [DecidableEq Symbol] (view : View Symbol) (call : Call Symbol) (complete : Completes view call) :
    ∃ fuel, (∃ result, execute view fuel call = .ok result) ∧
      ∀ bound, (∃ result, execute view bound call = .ok result) → fuel ≤ bound := by
  have search : ∀ bound, (∃ result, execute view bound call = .ok result) →
      ∃ fuel, (∃ result, execute view fuel call = .ok result) ∧
        ∀ other, (∃ result, execute view other call = .ok result) → fuel ≤ other := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
        intro done
        by_cases smaller : ∃ other, other < bound ∧ ∃ result, execute view other call = .ok result
        · obtain ⟨other, less, done⟩ := smaller
          exact ih other less done
        · refine ⟨bound, done, ?_⟩
          intro other accepted
          have apart : ¬other < bound := fun less => smaller ⟨other, less, accepted⟩
          omega
  obtain ⟨bound, done⟩ := complete
  exact search bound done

/-- Select the least successful bound for this exact semantic request. -/
def requiredFuel [DecidableEq Symbol] (view : View Symbol) (call : Call Symbol) (complete : Completes view call) : Nat :=
  Classical.choose (least_successful view call complete)

/-- The least selected bound has an actual exact successful result. -/
theorem requiredFuel_success [DecidableEq Symbol] (view : View Symbol) (call : Call Symbol) (complete : Completes view call) :
    ∃ result, execute view (requiredFuel view call complete) call = .ok result :=
  (Classical.choose_spec (least_successful view call complete)).1

/-- Any successful execution bounds the least required fuel. -/
theorem requiredFuel_le [DecidableEq Symbol] (view : View Symbol) (call : Call Symbol) (complete : Completes view call)
    (fuel : Nat) (result : Shape (Payload Symbol)) (done : execute view fuel call = .ok result) :
    requiredFuel view call complete ≤ fuel :=
  (Classical.choose_spec (least_successful view call complete)).2 fuel ⟨result, done⟩

/-- Every actual successful semantic request requires positive fuel. -/
theorem requiredFuel_positive [DecidableEq Symbol] (view : View Symbol) (call : Call Symbol) (complete : Completes view call) :
    0 < requiredFuel view call complete := by
  obtain ⟨result, done⟩ := requiredFuel_success view call complete
  by_cases zero : requiredFuel view call complete = 0
  · rw [zero] at done
    cases call <;> cases done
  · omega

/-- A child completed at the preceding least parent bound has a strictly smaller request measure. -/
theorem requiredFuel_child [DecidableEq Symbol] (view : View Symbol) (parent child : Call Symbol)
    (complete : Completes view parent) (result : Shape (Payload Symbol))
    (done : execute view (requiredFuel view parent complete - 1) child = .ok result) :
    ∃ childComplete : Completes view child,
      requiredFuel view child childComplete < requiredFuel view parent complete := by
  have childComplete : Completes view child := ⟨_, result, done⟩
  exact ⟨childComplete, Nat.lt_of_le_of_lt (requiredFuel_le view child childComplete _ result done)
    (by have := requiredFuel_positive view parent complete; omega)⟩

/-- Equivalent domain observations retain the exact least successful node bound. -/
theorem requiredFuel_domain [DecidableEq Symbol] (view : View Symbol) (before after : Domain)
    (same : DomainEquivalent before after) (left right : Input)
    (first : Completes view (.node before left right)) (second : Completes view (.node after left right)) :
    requiredFuel view (.node before left right) first = requiredFuel view (.node after left right) second := by
  apply Nat.le_antisymm
  · obtain ⟨result, done⟩ := requiredFuel_success view (.node after left right) second
    apply requiredFuel_le view (.node before left right) first _ result
    exact (run_domain_equivalent view _ before after same left right).trans done
  · obtain ⟨result, done⟩ := requiredFuel_success view (.node before left right) first
    apply requiredFuel_le view (.node after left right) second _ result
    exact (run_domain_equivalent view _ before after same left right).symm.trans done

end

/-- Each member of a successful ordered semantic traversal has an actual successful result. -/
theorem walk_member_success (action : A → Except Error B) (inputs : List A) (outputs : List B)
    (done : walk action inputs = .ok outputs) (input : A) (member : input ∈ inputs) : ∃ output, action input = .ok output := by
  have exactRows := walk_exact action inputs outputs done
  clear done
  induction exactRows with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | inside
      · exact ⟨_, head⟩
      · exact ih inside

end MicroCFTA.IntersectSchedule
