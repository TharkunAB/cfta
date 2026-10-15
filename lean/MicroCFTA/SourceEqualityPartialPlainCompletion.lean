import MicroCFTA.SourceEqualityPartialPlainCompletionCases

/-!
# Finite recursive caller execution for equality-free ordinary regions

Mutual structural induction derives a completed outer graph. Mu and union
branches stop at the actual source boundary. Every ordinary row retains
the actual empty native prefix, smaller structural children, and returned
warm state. No outer success or traversal bound is supplied.
-/
namespace MicroCFTA.SourceEqualityPartialPlainCompletion
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialPlainRegion SourceEqualityPartialPlainCompletionCases
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Every equality-free ordinary region has a finite actual completed caller graph at each closed available scope. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) {value : Value Symbol Guard} (plain : Region value) :
    NodeComplete (width := width) value := by
  exact Region.rec
    (motive_1 := fun value _ => NodeComplete (width := width) value)
    (motive_2 := fun edges _ => RowsComplete (width := width) edges)
    (motive_3 := fun values _ => ChildrenComplete (width := width) values)
    (fun _ _ _ _ => ⟨_, _, .empty⟩)
    (fun {_ _ _ _} => SourceEqualityPartialPlainCompletionCases.binder _ _ _ _)
    (fun {_ _ _ _} _ _ _ _ => ⟨_, _, .union⟩)
    (fun {_ _ _ _} _ ih => SourceEqualityPartialPlainCompletionCases.ordinary _ _ _ _ ih)
    (fun _ _ _ _ => ⟨_, _, .nil⟩)
    (fun {_ _} physical _ _ childIH tailIH => rows_cons formulas solver ambient _ _ physical childIH tailIH)
    (fun _ _ _ _ _ => ⟨_, _, .nil⟩)
    (fun {_ _} _ _ headIH tailIH => children_cons formulas solver ambient _ _ headIH tailIH) plain

end MicroCFTA.SourceEqualityPartialPlainCompletion
