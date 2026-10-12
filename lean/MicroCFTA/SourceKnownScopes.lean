import MicroCFTA.SourceQueryTransport

/-!
# Unambiguous source scopes retain known identity flags

The repaired sparse gate excludes the ambiguous table before any query.
Every successfully resolved nested scope then has all identity flags set.
-/
namespace MicroCFTA.SourceKnownScopes
open SourceGuards SourceObservations

/-- A successful resolution with no ambiguous paths records a known actual identity. -/
theorem resolve_known (formulas : Formulas Formula) (observed : Observations Formula)
    (fresh : List (Path × (Name × Name))) (entry : Substitution) (value : Resolved Formula)
    (found : resolve formulas observed fresh [] entry = some value) : value.identityKnown = true := by
  obtain ⟨actual, formal, atActual, atFormal⟩ := SourceActuals.resolve_exists formulas observed fresh [] entry value found
  simp [resolve, atActual, atFormal] at found
  subst value
  rfl

/-- Every successful source scope has all flags set when its ambiguity table is empty. -/
theorem resolveMany_known (formulas : Formulas Formula) (observed : Observations Formula)
    (fresh : List (Path × (Name × Name))) (recipe : List Substitution) (scope : List (Resolved Formula))
    (found : resolveMany formulas observed fresh [] recipe = some scope) : scope.all Resolved.identityKnown = true := by
  induction recipe generalizing scope with
  | nil => simp [resolveMany] at found; subst scope; rfl
  | cons entry rest ih =>
      cases first : resolve formulas observed fresh [] entry <;>
        cases tail : resolveMany formulas observed fresh [] rest <;>
        simp [resolveMany, first, tail] at found
      subst scope
      simp [resolve_known formulas observed fresh entry _ first, ih _ tail]

/-- The actual global table and every source-resolved stack inherit the repaired gate's invariant. -/
theorem scopes_known (guard : Guard FullSyntax.Formula) (observed : Observations FullSyntax.Formula)
    (unambiguous : ambiguous observed (sameShape SourceFormula.operations observed []) guard = [])
    (recipes : List SourceScopeStack.Recipe) (scopes : List SourceScopeStack.Scope)
    (resolved : SourceScopeStack.Resolves guard observed recipes scopes) :
    scopes.all (fun scope => scope.all Resolved.identityKnown) = true := by
  induction resolved with
  | nil => rfl
  | @cons recipe scope recipes scopes head tail ih =>
      have found := head.1
      change resolveMany SourceFormula.operations observed _
        (ambiguous observed (sameShape SourceFormula.operations observed []) guard) recipe = some scope at found
      rw [unambiguous] at found
      simp [resolveMany_known SourceFormula.operations observed _ recipe scope found, ih]

/-- Equal guard reads preserve the global ambiguity table used by the gate. -/
theorem reads_known (guard : Guard FullSyntax.Formula) (first second : Observations FullSyntax.Formula)
    (reads : SourceReadAgreement.Reads guard first second)
    (unambiguous : ambiguous first (sameShape SourceFormula.operations first []) guard = []) :
    ambiguous second (sameShape SourceFormula.operations second []) guard = [] :=
  (SourceIdentityReads.ambiguous_reads SourceFormula.operations guard first second reads).symm.trans unambiguous

end MicroCFTA.SourceKnownScopes
