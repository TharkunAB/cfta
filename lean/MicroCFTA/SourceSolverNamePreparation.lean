import MicroCFTA.SourceSolverNamePreparationSymbols
import MicroCFTA.SourceSolverNameFastEncoding
import MicroCFTA.SourceSizedLiquidAmbientRepair

/-!
# Complete preflight after solver name encoding

The encoded adapter repeats the source declaration and free-symbol checks.
The comparison preserves first-match lookup and all duplicate declarations.
As in SolverAdapter, a list represents each HashSet. Equality concerns this
ordered list model; native HashSet iteration order is not specified here.
-/
namespace MicroCFTA.SourceSolverNamePreparation
open FullSyntax (Name)
open FormulaLowering SolverAdapter SourceSolverNameSemantics SourceSizedLiquidProgram

/-- Apply the same name encoding to a declaration and retain its sort. -/
def mapDeclaration (rename : Name → Name) (binding : Declaration) : Declaration :=
  (rename binding.1, binding.2)

/-- Both generated and original binding names pass through nameSymbol. -/
def mapBinding (rename : Name → Name) (binding : Name × Name) : Name × Name :=
  (rename binding.1, rename binding.2)

/-- The distinguished value name uses the same encoding as explicit declarations. -/
def encodedDeclarations (rename : Name → Name) (given : List Declaration) : List Declaration :=
  let encoded := given.map (mapDeclaration rename)
  if rename valueName ∈ encoded.map Prod.fst then encoded else (rename valueName, .int) :: encoded

/-- Free names are collected after every expression name and binder is encoded. -/
def encodedMentioned (rename : Name → Name) (assumptions : List FullSyntax.Formula)
    (antecedent consequent : FullSyntax.Formula) : List Name :=
  (formulaSymbols (renameFormula rename (lowerFormula antecedent)) ++
    formulaSymbols (renameFormula rename (lowerFormula consequent)) ++
    partsSymbols (renameParts rename (lowerParts assumptions))).eraseDups

/-- The assertion retains the source ambient, antecedent, and negated-consequent order. -/
def encodedAssertion (rename : Name → Name) (assumptions : List FullSyntax.Formula)
    (antecedent consequent : FullSyntax.Formula) : FormulaLowering.Formula :=
  .and (renameParts rename (lowerParts assumptions) ++
    [renameFormula rename (lowerFormula antecedent), .not (renameFormula rename (lowerFormula consequent))])

/-- Fresh checks use the union of declared names and encoded ambient free symbols. -/
def reservedFreshAt (ambient : List Declaration) (assumptions : List FormulaLowering.Formula)
    (binding : Name × Name) : Option Declaration :=
  if binding.1 ∈ ambient.map Prod.fst ∨ binding.1 ∈ partsSymbols assumptions then none
  else some (binding.1, (lookupSort binding.2 ambient).getD .int)

/-- Traverse bindings in order without deduplicating generated declarations. -/
def reservedFreshListAt (ambient : List Declaration) (assumptions : List FormulaLowering.Formula) :
    List (Name × Name) → Option (List Declaration)
  | [] => some []
  | binding :: rest => do
    let first ← reservedFreshAt ambient assumptions binding
    let tail ← reservedFreshListAt ambient assumptions rest
    pure (first :: tail)

/-- Execute the source preflight using encoded declarations and lowered expressions. -/
def prepareRenamed (rename : Name → Name) (given : List Declaration)
    (assumptions : List FullSyntax.Formula) (query : Query) : Option Prepared := do
  let ambient := encodedDeclarations rename given
  let fresh ← reservedFreshListAt ambient (renameParts rename (lowerParts assumptions))
    (query.bindings.map (mapBinding rename))
  pure ⟨ambient ++ fresh ++ undeclared ambient fresh
    (encodedMentioned rename assumptions query.antecedent query.consequent),
    encodedAssertion rename assumptions query.antecedent query.consequent⟩

/-- Projecting encoded declarations yields exactly the encoded name list. -/
theorem declaration_names (rename : Name → Name) (given : List Declaration) :
    (given.map (mapDeclaration rename)).map Prod.fst = (given.map Prod.fst).map rename := by
  simp only [List.map_map, Function.comp_def, mapDeclaration]

/-- The default value declaration is added in exactly the same cases. -/
theorem declarations_rename (rename : Name → Name) (injective : Function.Injective rename)
    (given : List Declaration) :
    encodedDeclarations rename given = (declarations given).map (mapDeclaration rename) := by
  simp only [encodedDeclarations, declaration_names, mem_map_names rename injective, declarations]
  split <;> simp only [List.map_cons, mapDeclaration]

/-- First-match lookup retains the supplied sort even with repeated declarations. -/
theorem lookupSort_rename (rename : Name → Name) (injective : Function.Injective rename)
    (ambient : List Declaration) (name : Name) :
    lookupSort (rename name) (ambient.map (mapDeclaration rename)) = lookupSort name ambient := by
  induction ambient with
  | nil => rfl
  | cons binding rest ih =>
    rcases binding with ⟨key, sort⟩
    simp only [List.map_cons, mapDeclaration, lookupSort, injective.eq_iff, ih]

/-- All ambient and query free-name sets are the images of the original sets. -/
theorem mentioned_rename (rename : Name → Name) (injective : Function.Injective rename)
    (assumptions : List FullSyntax.Formula) (antecedent consequent : FullSyntax.Formula) :
    encodedMentioned rename assumptions antecedent consequent =
      (mentioned assumptions antecedent consequent).map rename := by
  simp only [encodedMentioned, mentioned, formulaSymbols_rename rename injective,
    partsSymbols_rename rename injective, ←List.map_append, eraseDups_names rename injective]

/-- Encoding each emitted part gives exactly the encoded complete assertion. -/
theorem assertion_rename (rename : Name → Name) (assumptions : List FullSyntax.Formula)
    (antecedent consequent : FullSyntax.Formula) :
    encodedAssertion rename assumptions antecedent consequent =
      renameFormula rename (assertion assumptions antecedent consequent) := by
  simp only [encodedAssertion, assertion, renameFormula, renameParts_append, renameParts]

/-- Both reserved-name rejection and inherited sort lookup commute with encoding. -/
theorem reservedFresh_rename (rename : Name → Name) (injective : Function.Injective rename)
    (ambient : List Declaration) (assumptions : List FullSyntax.Formula) (binding : Name × Name) :
    reservedFreshAt (ambient.map (mapDeclaration rename)) (renameParts rename (lowerParts assumptions))
      (mapBinding rename binding) =
      (SourceSizedLiquidAmbientRepair.reservedFresh ambient assumptions binding).map (mapDeclaration rename) := by
  simp only [reservedFreshAt, mapBinding, declaration_names, partsSymbols_rename rename injective,
    mem_map_names rename injective, lookupSort_rename rename injective,
    SourceSizedLiquidAmbientRepair.reservedFresh]
  split <;> rfl

/-- The entire fresh-binding traversal preserves rejection and duplicate positions. -/
theorem reservedFreshList_rename (rename : Name → Name) (injective : Function.Injective rename)
    (ambient : List Declaration) (assumptions : List FullSyntax.Formula) (bindings : List (Name × Name)) :
    reservedFreshListAt (ambient.map (mapDeclaration rename)) (renameParts rename (lowerParts assumptions))
      (bindings.map (mapBinding rename)) =
      (SourceSizedLiquidAmbientRepair.reservedFreshList ambient assumptions bindings).map
        (List.map (mapDeclaration rename)) := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    simp only [List.map_cons, reservedFreshListAt, SourceSizedLiquidAmbientRepair.reservedFreshList,
      reservedFresh_rename rename injective, ih]
    cases SourceSizedLiquidAmbientRepair.reservedFresh ambient assumptions binding <;>
      cases SourceSizedLiquidAmbientRepair.reservedFreshList ambient assumptions rest <;> rfl

/-- Default integer declarations contain precisely the encoded undeclared names. -/
theorem undeclared_rename (rename : Name → Name) (injective : Function.Injective rename)
    (ambient fresh : List Declaration) (names : List Name) :
    undeclared (ambient.map (mapDeclaration rename)) (fresh.map (mapDeclaration rename)) (names.map rename) =
      (undeclared ambient fresh names).map (mapDeclaration rename) := by
  unfold undeclared
  rw [eraseDups_names rename injective, declaration_names, declaration_names, ←List.map_append,
    filter_names rename injective]
  simp only [List.map_map]
  rfl

/-- Complete preparation is derived from the primitive source operations. -/
theorem sourcePrepare_rename (rename : Name → Name) (injective : Function.Injective rename)
    (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query) :
    prepareRenamed rename given assumptions query =
      (SourceSizedLiquidAmbientRepair.sourcePrepare given assumptions query).map (renamePrepared rename) := by
  simp only [prepareRenamed, declarations_rename rename injective,
    reservedFreshList_rename rename injective, SourceSizedLiquidAmbientRepair.sourcePrepare]
  cases SourceSizedLiquidAmbientRepair.reservedFreshList (declarations given) assumptions query.bindings with
  | none => rfl
  | some fresh =>
    simp only [Option.map_some, bind, Option.bind, pure, Option.some.injEq]
    simp only [mentioned_rename rename injective, undeclared_rename rename injective,
      assertion_rename, renamePrepared, List.map_append]
    rfl

/-- The current two-form native codec is applied before every preflight operation. -/
def encodedPrepare (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query) :
    Option Prepared := prepareRenamed SourceSolverNameFastEncoding.encode given assumptions query

/-- The actual codec gives exactly the encoded successful request or the original rejection. -/
theorem sourcePrepare_encode (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query) :
    encodedPrepare given assumptions query =
      (SourceSizedLiquidAmbientRepair.prepareQuery given assumptions query).map
        (renamePrepared SourceSolverNameFastEncoding.encode) := by
  rw [encodedPrepare, sourcePrepare_rename _ (fun _ _ same => SourceSolverNameFastEncoding.encode_injective same),
    SourceSizedLiquidAmbientRepair.sourcePrepare_exact]

/-- Encoding does not change which queries return Unknown during preflight. -/
theorem encoded_rejected (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query) :
    encodedPrepare given assumptions query = none ↔
      SourceSizedLiquidAmbientRepair.prepareQuery given assumptions query = none := by
  rw [sourcePrepare_encode]
  simp only [Option.map_eq_none_iff]

end MicroCFTA.SourceSolverNamePreparation
