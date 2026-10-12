import MicroCFTA.GuardBuilders
import MicroCFTA.ParentGuardFormula
import MicroCFTA.FreshEnvironment

/-!
# Contract conjuncts and compact positional names

The source flattens outer conjunctions, removes literal Top, selects only
the child names free in each remaining conjunct, and renumbers them from
zero. Name substitution uses the complete checked formula implementation.
-/
namespace MicroCFTA.ContractAssembly
open FullSyntax
open SourceGuards (contractName)

/-- Flatten only outer conjunction nodes, in source order. -/
def conjuncts : Formula → List Formula
  | .and parts => parts.flatMap conjuncts
  | formula => [formula]

/-- Removing literal Top does not simplify any other formula syntax. -/
def parts (formula : Formula) : List Formula :=
  (conjuncts formula).filter (fun part => decide (part ≠ .top))

/-- Each selected source child index has a free positional name in this conjunct. -/
def named (arity : Nat) (formula : Formula) : List Nat :=
  (List.range arity).filter (fun index => (freeNames formula).contains (contractName index))

/-- Name selection is exact, including formulas below quantifiers and applications. -/
theorem named_member (arity index : Nat) (formula : Formula) :
    index ∈ named arity formula ↔ index < arity ∧ contractName index ∈ formulaNames formula := by
  simp [named, freeNames]

/-- Source argument order and filtering cannot introduce a repeated selected index. -/
theorem named_nodup (arity : Nat) (formula : Formula) : (named arity formula).Nodup :=
  List.nodup_range.filter _

/-- A compact positional vector never has more positions than the original builder. -/
theorem named_length (arity : Nat) (formula : Formula) : (named arity formula).length ≤ arity := by
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- Pair each selected old name with its zero-based position in the compact target list. -/
def renamingTable (selected : List Nat) : List (Name × Name) :=
  (selected.map contractName).zip ((List.range selected.length).map contractName)

/-- Every selected old formal is present in the source substitution domain. -/
theorem renaming_keys (selected : List Nat) :
    (renamingTable selected).map Prod.fst = selected.map contractName := by
  apply List.map_fst_zip
  simp

/-- Every new formal is one consecutive compact target name. -/
theorem renaming_targets (selected : List Nat) :
    (renamingTable selected).map Prod.snd = (List.range selected.length).map contractName := by
  apply List.map_snd_zip
  simp

/-- Distinct source positions have distinct generated old names. -/
theorem renaming_keys_nodup (selected : List Nat) (distinct : selected.Nodup) :
    ((renamingTable selected).map Prod.fst).Nodup := by
  rw [renaming_keys]
  exact List.pairwise_map.mpr (distinct.imp
    (fun different same => different (ParentGuardFormula.contractName_injective same)))

/-- Every compact formal has a unique new name. -/
theorem renaming_targets_nodup (selected : List Nat) : ((renamingTable selected).map Prod.snd).Nodup := by
  rw [renaming_targets]
  exact ParentGuardFormula.contractNames_distinct selected.length

/-- A compact name cannot capture an unmapped free name of its own conjunct. -/
theorem compact_avoids (arity : Nat) (formula : Formula) (name : Name)
    (live : name ∈ formulaNames formula)
    (unmapped : name ∉ (renamingTable (named arity formula)).map Prod.fst) :
    name ∉ (renamingTable (named arity formula)).map Prod.snd := by
  rw [renaming_keys] at unmapped
  rw [renaming_targets]
  intro captured
  obtain ⟨index, present, same⟩ := List.mem_map.mp captured
  have below := List.mem_range.mp present
  have length := named_length arity formula
  have selected := (named_member arity index formula).mpr ⟨by omega, by simpa [same] using live⟩
  exact unmapped (List.mem_map.mpr ⟨index, selected, same⟩)

/-- Execute exactly the checked name-only substitution used by the builder. -/
def renumber (arity : Nat) (formula : Formula) : Formula :=
  SourceFormula.substitute (renamingTable (named arity formula)) formula

/-- Contract renumbering cannot raise the source checked-substitution error. -/
theorem renumber_checked (arity : Nat) (formula : Formula) :
    FormulaSubstitution.checked (SourceFormula.replacements (renamingTable (named arity formula))) formula =
      .ok (renumber arity formula) := SourceFormula.substitute_checked _ _

/-- Compact names retain every original free value through the explicit reverse table. -/
theorem lifted_names (model : Interpretation Value) (env : Name → Value) (arity : Nat) (formula : Formula) :
    FormulaSemantics.Agree (formulaNames formula)
      (SourceFormula.renamedEnvironment model
        (FreshEnvironment.liftEnvironment (renamingTable (named arity formula)) env) (renamingTable (named arity formula))) env :=
  FreshEnvironment.lift_agree model _ _ (renaming_keys_nodup _ (named_nodup arity formula))
    (renaming_targets_nodup _) (compact_avoids arity formula) env

/-- Full sorted formula truth is unchanged when selected children receive their compact names. -/
theorem renumber_exact (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (env : Name → Value) (arity : Nat) (formula : Formula) :
    Holds model (FreshEnvironment.liftEnvironment (renamingTable (named arity formula)) env) (renumber arity formula) ↔
      Holds model env formula := by
  rw [renumber, SourceFormula.substitute_semantics model nullary]
  exact FormulaSemantics.formula_ext model formula _ _ (lifted_names model env arity formula)

/-- Each compact target receives exactly the value of the selected original child. -/
theorem compact_value (selected : List Nat) (env : Name → Value) (index old : Nat)
    (found : selected[index]? = some old) :
    FreshEnvironment.liftEnvironment (renamingTable selected) env (contractName index) = env (contractName old) := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have read := (List.getElem?_eq_some_iff.mp found).2
  have pair : (contractName old, contractName index) ∈ renamingTable selected := by
    apply List.mem_of_getElem? (i := index)
    simp [renamingTable, bound, read]
  have reverse := FreshEnvironment.rename_of_member ((renamingTable selected).map Prod.swap)
    (by simpa only [List.map_map, Function.comp_def, Prod.swap] using renaming_targets_nodup selected)
    (contractName index) (contractName old) (List.mem_map.mpr ⟨_, pair, rfl⟩)
  simp [FreshEnvironment.liftEnvironment, reverse]

/-- One source contract clause names only its selected immediate children. -/
def clause (arity : Nat) (formula : Formula) : SourceGuards.Guard Formula :=
  .holds ((named arity formula).map GuardBuilders.argumentPath) (renumber arity formula)

/-- The exact pre-conjunction clause list used by contract. -/
def clauses (arity : Nat) (formula : Formula) : List (SourceGuards.Guard Formula) :=
  (parts formula).map (clause arity)

/-- Each contract target is one in-range child whose old name is free in that conjunct. -/
theorem clause_target (arity : Nat) (formula : Formula) (path : SourceGuards.Path) :
    path ∈ SourceGuards.paths (clause arity formula) ↔
      ∃ index, path = [index] ∧ index < arity ∧ contractName index ∈ formulaNames formula := by
  simp only [clause, SourceGuards.paths, List.mem_map, GuardBuilders.argumentPath, named_member]
  constructor
  · rintro ⟨index, selected, same⟩
    exact ⟨index, same.symm, selected⟩
  · rintro ⟨index, same, selected⟩
    exact ⟨index, selected, same.symm⟩

/-- Clauses preserve the source conjunct order and exclude only literal Top. -/
theorem clauses_member (arity : Nat) (formula : Formula) (guard : SourceGuards.Guard Formula) :
    guard ∈ clauses arity formula ↔
      ∃ part ∈ conjuncts formula, part ≠ .top ∧ clause arity part = guard := by
  simp only [clauses, parts, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨part, ⟨member, notTop⟩, same⟩
    exact ⟨part, member, notTop, same⟩
  · rintro ⟨part, member, notTop, same⟩
    exact ⟨part, ⟨member, notTop⟩, same⟩

/-- The source arity scan reads exactly the selected original child positions. -/
theorem clause_indices (arity : Nat) (formula : Formula) :
    GuardBuilders.indices (clause arity formula) = named arity formula := by
  simp [GuardBuilders.indices, GuardBuilders.targets, GuardBuilders.atoms, clause,
    GuardBuilders.argumentPath, List.filterMap_map, Function.comp_def]

/-- Contract reach collects every clause's child positions in order. -/
theorem clauses_indices (arity : Nat) (formula : Formula) :
    GuardBuilders.indices (.and (clauses arity formula)) = (parts formula).flatMap (named arity) := by
  simp [GuardBuilders.indices, GuardBuilders.targets, GuardBuilders.atoms, clauses, clause,
    GuardBuilders.argumentPath, List.flatMap_assoc, List.filterMap_flatMap,
    List.filterMap_map, List.flatMap_map, Function.comp_def]

/-- Every generated contract fits the original builder's complete child arity. -/
theorem contract_arity (arity : Nat) (formula : Formula) :
    GuardBuilders.transitionCheck none arity (.and (clauses arity formula)) = .ok () := by
  apply (GuardBuilders.transition_success none arity _).mpr
  refine ⟨by simp, ?_⟩
  intro index present
  rw [clauses_indices] at present
  obtain ⟨part, _, selected⟩ := List.mem_flatMap.mp present
  exact ((named_member arity index part).mp selected).1

/-- Flattening source conjunctions preserves full sorted formula truth. -/
theorem conjuncts_exact (model : Interpretation Value) (env : Name → Value) (formula : Formula) :
    (∀ part ∈ conjuncts formula, Holds model env part) ↔ Holds model env formula := by
  cases formula with
  | and children =>
      constructor
      · intro allParts
        rw [conjuncts] at allParts
        simp only [Holds]
        apply (FormulaSimplify.all_iff model env children).mpr
        intro child present
        apply (conjuncts_exact model env child).mp
        intro part found
        exact allParts part (List.mem_flatMap.mpr ⟨child, present, found⟩)
      · intro allParts part found
        rw [conjuncts] at found
        simp only [Holds] at allParts
        obtain ⟨child, present, member⟩ := List.mem_flatMap.mp found
        exact (conjuncts_exact model env child).mpr
          ((FormulaSimplify.all_iff model env children).mp allParts child present) part member
  | _ => simp [conjuncts]
termination_by sizeOf formula

/-- Dropping only literal Top retains every nontrivial requirement and full truth. -/
theorem parts_exact (model : Interpretation Value) (env : Name → Value) (formula : Formula) :
    (∀ part ∈ parts formula, Holds model env part) ↔ Holds model env formula := by
  rw [← conjuncts_exact model env formula]
  constructor
  · intro kept part member
    by_cases top : part = .top
    · simp [top, Holds]
    · exact kept part (by simp [parts, member, top])
  · intro allParts part member
    exact allParts part (List.mem_filter.mp member).1

/-- Every compacted conjunct has the same meaning in its explicit selected-child environment. -/
theorem contract_formula_exact (model : Interpretation Value) (nullary : ∀ value, model.apply value [] = value)
    (env : Name → Value) (arity : Nat) (formula : Formula) :
    (∀ part ∈ parts formula,
      Holds model (FreshEnvironment.liftEnvironment (renamingTable (named arity part)) env) (renumber arity part)) ↔
      Holds model env formula := by
  simpa only [renumber_exact model nullary env arity] using parts_exact model env formula

example : named 4 (.atom .eq (.var (contractName 3)) (.var (contractName 1))) = [1, 3] := by cbv
example : renamingTable [1, 3] = [(contractName 1, contractName 0), (contractName 3, contractName 1)] := rfl

end MicroCFTA.ContractAssembly
