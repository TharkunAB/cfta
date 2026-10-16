import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite

/-!
# Cached depth on available finite ordinary records

Coherent node fields give the maximum depth of the actual children.
The finite ordinary domain makes each child depth zero. Guards and
their equality classes have no restriction.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDepth
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
local notation "Domain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable {Symbol Guard : Type}

/-- Coherent available finite ordinary values have zero cached Mu depth. -/
theorem depth (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value) (domain : Domain value) :
    value.depth = 0 := by
  induction available with
  | intro value resident issued children ih =>
      cases domain with
      | empty => rfl
      | @ordinary edges entry level free rows =>
          obtain ⟨actual, _, fields⟩ := coherent.nodes entry.key _ (resident entry rfl)
          change level = 0
          rw [fields.2.2.1]
          apply Nat.le_zero.mp
          apply (maximumDepth_exact _ _).mpr
          intro child member
          obtain ⟨edge, inside, selected⟩ := List.mem_flatMap.mp member
          exact Nat.le_of_eq (ih child member ((rows.member edge inside).member child selected))

/-- Coherent available domain values satisfy the literal gate metadata shortcut. -/
theorem fast (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value) (domain : Domain value) :
    (value.depth == 0 && value.free.isEmpty) = true := by
  rw [depth state coherent value available domain,
    SourceCurrentAllocatedFiniteOrdinaryFinite.closed state coherent value available domain]
  rfl

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDepth
