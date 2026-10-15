import MicroCFTA.SourceEqualityPartialInheritedPlainCases

/-!
# Finite equality-free caller regions for every inherited payload

Mutual structural induction follows the original ordinary child regions.
Every actual empty-own prefix keeps those children or erases all slots.
Literal contradiction and erased graphs need no smaller-call premise.
All scopes come from the real returned native and constructor effects.
-/
namespace MicroCFTA.SourceEqualityPartialInheritedPlainCompletion
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialPlainRegion SourceEqualityPartialInheritedPlainChildren SourceEqualityPartialInheritedPlainCases
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Every equality-free ordinary region completes for any actual inherited payload and closed available scope. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) {value : Value Symbol Guard} (plain : Region value) :
    NodeComplete (width := width) value := by
  exact Region.rec
    (motive_1 := fun value _ => NodeComplete (width := width) value)
    (motive_2 := fun edges _ => RowsComplete (width := width) edges)
    (motive_3 := fun values _ => ChildrenComplete (width := width) values)
    (fun _ _ _ _ _ => ⟨_, _, .empty⟩)
    (fun {_ _ _ _} => SourceEqualityPartialInheritedPlainCases.binder _ _ _ _)
    (fun {_ _ _ _} _ _ _ _ _ => ⟨_, _, .union⟩)
    (fun {_ _ _ _} _ ih => SourceEqualityPartialInheritedPlainCases.ordinary _ _ _ _ ih)
    (fun _ _ _ _ _ => ⟨_, _, .nil⟩)
    (fun {_ _} physical _ _ childIH tailIH => rows_cons formulas solver ambient _ _ physical childIH tailIH)
    (fun _ _ _ _ _ _ => ⟨_, _, .nil⟩)
    (fun {_ _} _ _ headIH tailIH => SourceEqualityPartialInheritedPlainChildren.cons formulas solver ambient _ _ headIH tailIH) plain

end MicroCFTA.SourceEqualityPartialInheritedPlainCompletion
