import MicroCFTA.SourceEqualityDemandTarget

/-!
# Equality-satisfying subterms survive demanded target construction

Projection and general merging retain the selected original subterm.
Each native request retains the intersection of its two actual operands.
Their first-seeded fold therefore retains every common selected subterm.
-/
namespace MicroCFTA.SourceEqualityDemandTargetLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityNativeScoped SourceEqualityDemandTarget
open InternedGuardedLanguage (meaning)

/-- Each actual source target fold retains a term selected at every one of its original operand paths. -/
theorem _root_.MicroCFTA.SourceEqualityDemandTarget.Fold.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values)
    (nonroot : ∀ path ∈ seed :: paths, path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) (accepted : All₂ (meaning holds ambient) values terms)
    (selected : ∀ path ∈ seed :: paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) : meaning holds ambient result part := by
  induction trace with
  | nil seedDemand =>
      exact seedDemand.included ready available closed (nonroot _ List.mem_cons_self) holds ambient clearTrue topTrue symbol terms part accepted
        (selected _ List.mem_cons_self)
  | @cons path before value middle paths tail later result after operand rest step ih =>
      have first := operand.effects ready available closed
      have tailInputs : Values middle.machine.heap values := fun value member => first.2.1.available value (available value member)
      have tailNonroot : ∀ own ∈ seed :: paths, own ≠ [] := by
        intro own member
        rcases List.mem_cons.mp member with rfl | member
        · exact nonroot _ List.mem_cons_self
        · exact nonroot own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
      have tailSelected : ∀ own ∈ seed :: paths, SymbolicSignedPaths.lookup (.node symbol terms) own = some part := by
        intro own member
        rcases List.mem_cons.mp member with rfl | member
        · exact selected _ List.mem_cons_self
        · exact selected own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
      have tailAccepted := ih first.1 tailInputs tailNonroot tailSelected
      have ownAccepted := operand.included ready available closed (nonroot path (by simp)) holds ambient clearTrue topTrue symbol terms part accepted
        (selected path (by simp))
      have remaining := rest.effects first.1 tailInputs closed
      have checked := step.verified remaining.1 (remaining.2.1.available value first.2.2.1) remaining.2.2.1
        first.2.2.2.1 remaining.2.2.2 holds conjoined
      exact (checked.2.2.2.2 ambient part).mpr ⟨tailAccepted, ownAccepted⟩

/-- Every nonempty actual target retains any common selected original subterm. -/
theorem _root_.MicroCFTA.SourceEqualityDemandTarget.Target.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (closed : ClosedValues values) (nonempty : paths ≠ []) (nonroot : ∀ path ∈ paths, path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol) (accepted : All₂ (meaning holds ambient) values terms)
    (selected : ∀ path ∈ paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) : meaning holds ambient result part := by
  cases trace with
  | nil => exact False.elim (nonempty rfl)
  | cons fold => exact fold.included ready available closed nonroot holds ambient clearTrue topTrue conjoined symbol terms part accepted selected

end MicroCFTA.SourceEqualityDemandTargetLanguage
