import MicroCFTA.SourceSortedQueries

/-!
# Contract names are disjoint from allocated actual names

The two concrete source prefixes differ. This fact extends the constructed
environment transport to positional relational contracts without assuming a
fresh-name side condition for those generated names.
-/
namespace MicroCFTA.SourceContractNames
open FullSyntax FormulaSubstitution SourceFormula SourceScopeStack FreshEnvironment

/-- The source contract and actual streams cannot contain the same name. -/
theorem contract_ne_actual (contractIndex actualIndex : Nat) :
    SourceGuards.contractName contractIndex ≠ "__cfta_actual_" ++ toString actualIndex := by
  intro same
  have different := congrArg (fun name : String => name.toList[12]?) same
  simp [SourceGuards.contractName, String.toList_append] at different

/-- Source actual allocation never returns a generated contract name. -/
theorem contract_not_fresh (index : Nat) (avoid : List Name) (count : Nat) :
    SourceGuards.contractName index ∉ SourceGuards.freshNames avoid count := by
  intro member
  have filtered := List.mem_of_mem_take member
  obtain ⟨actualIndex, _, equal⟩ := List.mem_map.mp (List.mem_filter.mp filtered).1
  exact contract_ne_actual index actualIndex equal.symm

/-- A generated contract name is absent from both sides of the actual source spelling map. -/
theorem contract_outside (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula) (index : Nat) :
    SourceGuards.contractName index ∉ (SourceFreshTables.tableRenaming operations guard first second).map Prod.fst ∧
      SourceGuards.contractName index ∉ (SourceFreshTables.tableRenaming operations guard first second).map Prod.snd := by
  unfold SourceFreshTables.tableRenaming
  rw [fresh_keys, fresh_targets]
  exact ⟨contract_not_fresh index _ _, contract_not_fresh index _ _⟩

/-- Actual fresh-name transport keeps each positional contract variable fixed. -/
theorem contract_fixed (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula) (index : Nat) :
    renameName (SourceFreshTables.tableRenaming operations guard first second) (SourceGuards.contractName index) =
      SourceGuards.contractName index :=
  FormulaBinders.rename_absent _ _ (contract_outside guard first second index).1

/-- Track all positional contract variables used by one Holds query. -/
def live (guard : SourceGuards.Guard Formula) (observed : SourceGuards.Observations Formula) (count : Nat) : List Name :=
  SourceSemanticNames.live operations observed guard ++ (List.range count).map SourceGuards.contractName

/-- The actual table avoids every unmapped name in the extended finite set. -/
theorem live_avoid (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (count : Nat)
    (name : Name) (member : name ∈ live guard first count)
    (unmapped : name ∉ (SourceFreshTables.tableRenaming operations guard first second).map Prod.fst) :
    name ∉ (SourceFreshTables.tableRenaming operations guard first second).map Prod.snd := by
  rcases List.mem_append.mp member with original | contract
  · exact SourceSemanticNames.live_avoid operations guard first second reads name original unmapped
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp contract
    exact (contract_outside guard first second index).2

/-- Actual-name transport is injective on all names needed by a Holds query. -/
theorem live_injective (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (count : Nat) :
    ∀ left ∈ live guard first count, ∀ right ∈ live guard first count,
      renameName (SourceFreshTables.tableRenaming operations guard first second) left =
        renameName (SourceFreshTables.tableRenaming operations guard first second) right → left = right :=
  SourceScopeEnvironment.injective_live _ _ (SourceFreshTables.renaming_unique operations guard first second).2
    (live_avoid guard first second reads count)

/-- The constructed reverse environment retains the extended finite relation. -/
theorem lift_related (model : Interpretation Value)
    (guard : SourceGuards.Guard Formula) (first second : SourceGuards.Observations Formula)
    (reads : SourceReadAgreement.Reads guard first second) (count : Nat) (env : Name → Value) :
    SourceScopeEnvironment.Related (SourceFreshTables.tableRenaming operations guard first second)
      (live guard first count) env (liftEnvironment (SourceFreshTables.tableRenaming operations guard first second) env) :=
  SourceScopeEnvironment.lift_related model _ _
    (SourceFreshTables.renaming_unique operations guard first second).1
    (SourceFreshTables.renaming_unique operations guard first second).2
    (live_avoid guard first second reads count) env

end MicroCFTA.SourceContractNames
