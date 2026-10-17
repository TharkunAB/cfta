import MicroCFTA.InternedFreshOrdinaryAllocationBudget
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution

/-!
# Initial allocation bounds for repaired stored substitution

Stored substitution uses the full fresh constructor schedule. Its initial
encoded syntax bounds all outcomes for every replacement environment.
Unfolding charges the literal stored body. These local bounds do not prove
an initial resource bound for a complete recursive head or query sequence.
-/
namespace MicroCFTA.InternedFreshOrdinaryStoredAllocationBudget
open InternedConstructorTemplates
open InternedStoredSubstitution (Environment leaves encode)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)

/-- The initial encoded value supplies separate node and edge charges. -/
def executeCharges (value : Value Symbol Guard) : Nat × Nat :=
  let expression := encode (leaves value) [] value
  (InternedFreshOrdinaryAllocationBudget.nodeBudget expression,
    InternedFreshOrdinaryAllocationBudget.edgeBudget expression)

/-- A recursive value charges its stored body; other values allocate nothing. -/
def unfoldCharges (value : Value Symbol Guard) : Nat × Nat :=
  match value with
  | .mu _ body _ _ => executeCharges body
  | _ => (0, 0)

/-- Every substitution outcome fits its initial charges, including pending outcomes. -/
theorem execute_bound [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) :
    (execute value environment before).state.nodes.next ≤ before.nodes.next + (executeCharges value).1 ∧
      (execute value environment before).state.edges.next ≤ before.edges.next + (executeCharges value).2 :=
  InternedFreshOrdinaryAllocationBudget.build_bound _ _ before

/-- Every actual unfolding outcome fits the literal input body's initial charges. -/
theorem unfold_bound [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before : State Symbol Guard) :
    (unfold value before).state.nodes.next ≤ before.nodes.next + (unfoldCharges value).1 ∧
      (unfold value before).state.edges.next ≤ before.edges.next + (unfoldCharges value).2 := by
  cases value with
  | mu => exact execute_bound _ _ before
  | empty | ref | node | union => exact ⟨Nat.le_refl _, Nat.le_refl _⟩

end MicroCFTA.InternedFreshOrdinaryStoredAllocationBudget
