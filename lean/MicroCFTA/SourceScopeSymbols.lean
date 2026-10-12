import MicroCFTA.SourceQueryDecisions

/-!
# Structural comparison through paired source scopes

Logical actual names can change. Literal symbol replacements do not change
between read-equivalent cells. This gives exact sparse structural comparison.
-/
namespace MicroCFTA.SourceScopeSymbols
open SourceGuards SourceObservations SourceScopeStack

/-- Both successful source stacks have the exact per-record metadata relation. -/
theorem aligned (guard : Guard FullSyntax.Formula) (first second : Observations FullSyntax.Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other) :
    Language.All₂ (Language.All₂ (SourceResolvedTables.Aligned (SourceFreshTables.tableRenaming SourceFormula.operations guard first second))) scopes other := by
  induction resolved generalizing other with
  | nil => cases otherResolved; exact .nil
  | @cons recipe scope recipes scopes head tail ih =>
      cases otherResolved with
      | cons otherHead otherTail =>
          have each := SourceResolvedTables.resolveMany_aligned SourceFormula.operations guard first second reads recipe head.2
          change SourceResolvedTables.OptionRel _ (SourceScopeStack.resolve guard first recipe) (SourceScopeStack.resolve guard second recipe) at each
          rw [head.1, otherHead.1] at each
          exact .cons each (ih _ otherTail)

/-- Symbol replacement lists preserve their order and all repeated formal names. -/
theorem replacements (renamed : List (Name × Name)) (first second : List (Resolved Formula))
    (paired : Language.All₂ (SourceResolvedTables.Aligned renamed) first second) :
    first.map Resolved.symbolReplacement = second.map Resolved.symbolReplacement := by
  induction paired with
  | nil => rfl
  | cons head tail ih => simp [head.2.1, ih]

/-- Every scope performs exactly the same literal constructor and annotation replacement. -/
theorem root (formulas : Formulas Formula) (renamed : List (Name × Name))
    (first second : List (List (Resolved Formula)))
    (paired : Language.All₂ (Language.All₂ (SourceResolvedTables.Aligned renamed)) first second) (label : Label Formula) :
    renameRoot formulas first label = renameRoot formulas second label := by
  induction paired generalizing label with
  | nil => rfl
  | @cons first second rest other head tail ih =>
      have entries : symbolEntries first = symbolEntries second := by rw [symbolEntries, symbolEntries, replacements renamed first second head]
      have maps : symbolMap first = symbolMap second := by simp only [symbolMap, entries]
      simp only [renameRoot, List.foldl_cons, entries, maps]
      exact ih _

/-- Read agreement and paired metadata give exact sameShape results through every nested scope. -/
theorem same (guard : Guard FullSyntax.Formula) (first second : Observations FullSyntax.Formula)
    (reads : SourceReadAgreement.Reads guard first second) (recipes : List Recipe) (scopes other : List Scope)
    (resolved : Resolves guard first recipes scopes) (otherResolved : Resolves guard second recipes other)
    (left right : Path) (leftRequested : left ∈ sensitive guard) (rightRequested : right ∈ sensitive guard) :
    sameShape SourceFormula.operations first scopes left right = sameShape SourceFormula.operations second other left right := by
  have roots := root SourceFormula.operations _ scopes other (aligned guard first second reads recipes scopes other resolved otherResolved)
  unfold sameShape
  rw [reads.symbols left leftRequested, reads.symbols right rightRequested]
  simp only [renameObserved, roots]

end MicroCFTA.SourceScopeSymbols
