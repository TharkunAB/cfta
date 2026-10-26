import MicroCFTA.SourcePruningEnumerationExpansionAdmission

/-!
# Exact suspended mass at pending-slot writes

Assimilation moves the source bucket into a distinct target and removes
its old occurrence. Incoming replacement adds only the incoming bucket.
These equations count every suspended occurrence, including duplicates.
-/
namespace MicroCFTA.SourcePruningEnumerationSuspendedMass
open EnumerationState EnumerationCorrectness
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint

private theorem sum_map_set_balance {α : Type} (weight : α → Nat)
    (values : List α) (index : Nat) (old new : α)
    (stored : values[index]? = some old) :
    ((values.set index new).map weight).sum + weight old =
      (values.map weight).sum + weight new := by
  induction values generalizing index with
  | nil => simp at stored
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at stored
          subst first
          simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
          omega
      | succ index =>
          simp only [List.getElem?_cons_succ] at stored
          have balance := ih index stored
          simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
          omega

/-- Distinct pending-slot assimilation preserves the total suspended mass. -/
theorem assimilated_mass
    (before : Core) (source target : Nat) (sourceNode targetNode merged : Option Nat)
    (sourceScs targetScs : List Suspended)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs))
    (different : target ≠ source) :
    suspendedBound (assimilated before target source
      (.unenumerated merged (sourceScs ++ targetScs))) = suspendedBound before := by
  let weight : UVarValue Symbol → Nat := fun value => match value with
    | .unenumerated _ scs => scs.length
    | _ => 0
  have targetBalance := sum_map_set_balance weight before.values target
    (.unenumerated targetNode targetScs)
    (.unenumerated merged (sourceScs ++ targetScs)) targetStored
  have sourceAfter : (before.values.set target
      (.unenumerated merged (sourceScs ++ targetScs)))[source]? =
      some (.unenumerated sourceNode sourceScs) := by
    rw [List.getElem?_set_ne different]
    exact sourceStored
  have sourceBalance := sum_map_set_balance weight
    (before.values.set target (.unenumerated merged (sourceScs ++ targetScs))) source
    (.unenumerated sourceNode sourceScs) .eliminated sourceAfter
  change (((before.values.set target (.unenumerated merged (sourceScs ++ targetScs))).set
    source .eliminated).map weight).sum = (before.values.map weight).sum
  simp only [weight, List.length_append] at targetBalance sourceBalance ⊢
  omega

/-- Appending incoming constraints adds exactly their length to the suspended mass. -/
theorem incoming_mass
    (before : Core) (target : Nat) (oldNode newNode : Option Nat)
    (incomingScs oldScs : List Suspended)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs)) :
    suspendedBound {before with values := before.values.set target (.unenumerated newNode (incomingScs ++ oldScs))} =
      suspendedBound before + incomingScs.length := by
  let weight : UVarValue Symbol → Nat := fun value => match value with
    | .unenumerated _ scs => scs.length
    | _ => 0
  have balance := sum_map_set_balance weight before.values target
    (.unenumerated oldNode oldScs) (.unenumerated newNode (incomingScs ++ oldScs)) stored
  change ((before.values.set target (.unenumerated newNode (incomingScs ++ oldScs))).map weight).sum =
    (before.values.map weight).sum + incomingScs.length
  simp only [weight, List.length_append] at balance ⊢
  omega

end MicroCFTA.SourcePruningEnumerationSuspendedMass


namespace MicroCFTA.SourcePruningEnumerationPrefixAdmission
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint

/-- Equal stored slots retain the complete pending-bucket mass, including repeated entries. -/
theorem suspendedBound_values (before after : Core) (values : after.values = before.values) :
    suspendedBound after = suspendedBound before := by
  simp only [suspendedBound, values]

end MicroCFTA.SourcePruningEnumerationPrefixAdmission

namespace MicroCFTA.SourcePruningEnumerationExpansionAdmission
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint

/-- Equal stored slots retain the expansion count fixed at the original native seed. -/
theorem count_values (seed : Seed) (before after : Core) (values : after.values = before.values) :
    count seed after = count seed before := by
  unfold count
  rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before after values]

/-- The original reservation applies after a callback that retains every stored slot. -/
theorem reserved_values (bits : Nat) (seed : Seed) (before after : Core)
    (values : after.values = before.values)
    (reserved : Reserved bits (narrowSeed seed) (count seed before)) :
    Reserved bits (narrowSeed seed) (count seed after) := by
  rw [count_values seed before after values]
  exact reserved

end MicroCFTA.SourcePruningEnumerationExpansionAdmission
