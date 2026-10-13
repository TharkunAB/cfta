import MicroCFTA.SourceSolverNameSemantics

/-!
# Free symbols under injective solver name encoding

The list model retains traversal order and duplicates. Quantifiers remove
their bound names before the adapter forms its free-symbol sets.
-/
namespace MicroCFTA.SourceSolverNamePreparation
open FullSyntax (Name)
open FormulaLowering SolverAdapter SourceSolverNameSemantics

/-- Encoding retains exactly the membership of each original name. -/
theorem mem_map_names (rename : Name → Name) (injective : Function.Injective rename)
    (names : List Name) (name : Name) :
    rename name ∈ names.map rename ↔ name ∈ names := by
  simp only [List.mem_map, injective.eq_iff]
  exact ⟨fun ⟨_, member, equal⟩ => equal ▸ member, fun member => ⟨name, member, rfl⟩⟩

/-- Encoded equality is the same Boolean test. -/
theorem beq_names (rename : Name → Name) (injective : Function.Injective rename)
    (first second : Name) : (rename first == rename second) = (first == second) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, injective.eq_iff]

/-- The HashSet membership model commutes with encoding. -/
theorem contains_names (rename : Name → Name) (injective : Function.Injective rename)
    (names : List Name) (name : Name) :
    (names.map rename).contains (rename name) = names.contains name := by
  apply Bool.eq_iff_iff.mpr
  simpa only [List.contains_iff_mem] using mem_map_names rename injective names name

/-- Removing a bound-name set commutes with encoding in the original order. -/
theorem filter_names (rename : Name → Name) (injective : Function.Injective rename)
    (bound names : List Name) :
    ((names.map rename).filter fun name => !(bound.map rename).contains name) =
      (names.filter fun name => !bound.contains name).map rename := by
  simp only [List.filter_map, Function.comp_def, contains_names rename injective]

/-- First-occurrence duplicate removal retains exactly the encoded list. -/
theorem eraseDups_names (rename : Name → Name) (injective : Function.Injective rename)
    (names : List Name) : (names.map rename).eraseDups = names.eraseDups.map rename := by
  cases names with
  | nil => rfl
  | cons first rest =>
    simp only [List.map_cons, List.eraseDups_cons, List.map_cons]
    rw [List.filter_map]
    simp only [Function.comp_def, beq_names rename injective]
    rw [eraseDups_names rename injective (rest.filter fun name => !(name == first))]
termination_by names.length
decreasing_by simp_wf; have := List.length_filter_le (fun name => !(name == first)) rest; omega

mutual
/-- Value symbols retain their traversal order under encoding. -/
theorem termSymbols_rename (rename : Name → Name) (injective : Function.Injective rename)
    (term : FormulaLowering.Term) :
    termSymbols (renameTerm rename term) = (termSymbols term).map rename := by
  cases term with
  | integer _ | «variable» _ => simp only [renameTerm, termSymbols, List.map_nil, List.map_cons]
  | negative inner | cast inner _ =>
    simpa only [renameTerm, termSymbols] using termSymbols_rename rename injective inner
  | binary _ left right | application left right =>
    simp only [renameTerm, termSymbols, termSymbols_rename rename injective left,
      termSymbols_rename rename injective right, List.map_append]
  | conditional condition yes no =>
    simp only [renameTerm, termSymbols, formulaSymbols_rename rename injective condition,
      termSymbols_rename rename injective yes, termSymbols_rename rename injective no, List.map_append]
termination_by sizeOf term

/-- Quantified scopes remove precisely the encoded original binders. -/
theorem formulaSymbols_rename (rename : Name → Name) (injective : Function.Injective rename)
    (formula : FormulaLowering.Formula) :
    formulaSymbols (renameFormula rename formula) = (formulaSymbols formula).map rename := by
  cases formula with
  | true | false => simp only [renameFormula, formulaSymbols, List.map_nil]
  | and parts | or parts =>
    simpa only [renameFormula, formulaSymbols] using partsSymbols_rename rename injective parts
  | not inner =>
    simpa only [renameFormula, formulaSymbols] using formulaSymbols_rename rename injective inner
  | atom _ left right =>
    simp only [renameFormula, formulaSymbols, termSymbols_rename rename injective left,
      termSymbols_rename rename injective right, List.map_append]
  | «forall» bound inner | «exists» bound inner =>
    simp only [renameFormula, formulaSymbols, formulaSymbols_rename rename injective inner]
    have names : (bound.map (fun binding => (rename binding.1, binding.2))).map Prod.fst =
        (bound.map Prod.fst).map rename := by simp only [List.map_map, Function.comp_def]
    rw [names, filter_names rename injective]
termination_by sizeOf formula

/-- Ambient conjunctions retain all free names, including repeated occurrences. -/
theorem partsSymbols_rename (rename : Name → Name) (injective : Function.Injective rename)
    (parts : List FormulaLowering.Formula) :
    partsSymbols (renameParts rename parts) = (partsSymbols parts).map rename := by
  cases parts with
  | nil => simp only [renameParts, partsSymbols, List.map_nil]
  | cons first rest =>
    simp only [renameParts, partsSymbols, formulaSymbols_rename rename injective first,
      partsSymbols_rename rename injective rest, List.map_append]
termination_by sizeOf parts
end

/-- The assertion list map distributes over ambient and query parts. -/
theorem renameParts_append (rename : Name → Name) (first second : List FormulaLowering.Formula) :
    renameParts rename (first ++ second) = renameParts rename first ++ renameParts rename second := by
  induction first with
  | nil => simp only [List.nil_append, renameParts]
  | cons head tail ih => simp only [List.cons_append, renameParts, ih]

end MicroCFTA.SourceSolverNamePreparation
