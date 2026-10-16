import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntrySteps

/-!
# Numeric capacity on the full raw outer reach relation

Initial resource admission is invariant under each literal raw step.
Induction follows the original reflexive transitive closure.
The reached parent uses its own capacity before execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryReach
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Entry Reach)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs (Admitted)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Guard
variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
variable (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Every original raw reached entry retains its own current resource admission. -/
theorem reach {budget : Nat} {root entry : Entry (bits + 2)}
    (reached : Reach budget root entry) (initial : Admitted bits formulas solver root) :
    Admitted bits formulas solver entry := by
  revert initial
  induction reached with
  | refl => intro initial; exact initial
  | direct one => intro initial; exact SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntrySteps.step bits formulas solver one initial
  | trans _ _ firstIH restIH => intro initial; exact restIH (firstIH initial)

/-- Initial resources derive the existing universal raw Reach numeric Plan. -/
theorem numeric_plan {budget : Nat} {root : Entry (bits + 2)}
    (initial : Admitted bits formulas solver root) :
    SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan bits budget root := by
  intro request before reached
  exact SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs.edge_body_capacity
    (reach bits formulas solver reached initial)

/-- The same initial resources derive the older reached parent machine ranges. -/
theorem ranges {budget : Nat} {root : Entry (bits + 2)}
    (initial : Admitted bits formulas solver root) :
    SourceCurrentAllocatedFiniteOrdinaryOuterEntries.Plan budget root := by
  intro request before reached
  have admitted := reach bits formulas solver reached initial
  obtain ⟨inventory, memos, rows, arity, bound, limits, context, stored, inherited,
    resident, domain, _profile, _guards, _heightBound, _room, _active⟩ := admitted
  exact SourceCurrentAllocatedFiniteOrdinaryParentCapacity.resident_ranges bits formulas solver budget request
    context inherited resident domain stored.structural
    (SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryDefs.edge_body_capacity
      (reach bits formulas solver reached initial))

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryReach
