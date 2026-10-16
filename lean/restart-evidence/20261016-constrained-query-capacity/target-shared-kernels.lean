import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedCapacity

namespace MicroCFTA.FiniteOrdinarySharedCapacityChecks
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinarySharedCapacity
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "Force" => SourceCurrentAllocatedSharedTargetForce.Force
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryShared.Stored
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A warm slot needs no target-query capacity at any earlier or future state. -/
theorem force_hit_capacity (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path) (before : Shared (bits + 2))
    (value : Value Symbol Guard) (present : before.targets path = some value) :
    ForceCapacity bits record values path before := by
  intro absent
  rw [present] at absent
  cases absent

/-- A warm leaf checks only its current native-query entry; the force cannot change that state. -/
theorem leaf_hit_capacity (bits : Nat) (record : SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path) (input : Value Symbol Guard)
    (before : Shared (bits + 2)) (value : Value Symbol Guard)
    (present : before.targets path = some value) (capacity : Capacity bits before.checked) :
    LeafCapacity bits record values path input before := by
  refine ⟨force_hit_capacity bits record values path before value present, ?_⟩
  intro target middle actual
  cases actual with
  | hit => exact capacity
  | miss absent _ => rw [present] at absent; cases absent

/-- The public finite force preserves the whole warm shared state without a numeric capacity premise. -/
theorem force_hit_finite (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (path : EqualityNormalize.Path)
    (before : Shared (bits + 2)) (value : Value Symbol Guard)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Children values) (stored : Stored before)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (present : before.targets path = some value)
    (memos : EndpointMemoGateTrace.Memos) (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) :
    ∃ next final, SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record values base path before value before memos final ∧
      Stored before ∧ SourceCurrentAllocatedFiniteOrdinaryDomain.Node value := by
  obtain ⟨result, after, next, final, receipt, retained, resultDomain⟩ :=
    SourceCurrentAllocatedFiniteOrdinarySharedCapacity.force_finite bits formulas solver inventory ready known domain stored
      coherent active member (force_hit_capacity bits record values path before value present) memos valid
  have same : result = value ∧ after = before := by
    cases receipt.actual with
    | hit found => exact ⟨Option.some.inj (found.symm.trans present), rfl⟩
    | miss absent _ => rw [present] at absent; cases absent
  rcases same with ⟨rfl, rfl⟩
  exact ⟨next, final, receipt, retained, resultDomain⟩
end MicroCFTA.FiniteOrdinarySharedCapacityChecks

#print axioms MicroCFTA.FiniteOrdinarySharedCapacityChecks.force_hit_capacity
#check @MicroCFTA.FiniteOrdinarySharedCapacityChecks.force_hit_capacity
#print axioms MicroCFTA.FiniteOrdinarySharedCapacityChecks.leaf_hit_capacity
#check @MicroCFTA.FiniteOrdinarySharedCapacityChecks.leaf_hit_capacity
#print axioms MicroCFTA.FiniteOrdinarySharedCapacityChecks.force_hit_finite
#check @MicroCFTA.FiniteOrdinarySharedCapacityChecks.force_hit_finite
