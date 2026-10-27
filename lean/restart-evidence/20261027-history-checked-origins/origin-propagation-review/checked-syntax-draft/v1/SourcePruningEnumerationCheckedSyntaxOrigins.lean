import MicroCFTA.SourcePruningEnumerationArityOrigins

/-!
# Original source checks supply the initial arity invariant

Each syntactic edge has normalized equalities and passes the source check
at its original child count. These original checks derive projected arity.
The actual raw build then preserves that derived invariant.
-/
namespace MicroCFTA.SourcePruningEnumerationArityOrigins
open InternedConstructorTemplates
open EnumerationState (arityAllows)
open EnumerationCorrectness
open InternedNestedConstruction (Syntax EdgeSyntax)
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {Symbol : Type}

/-- The actual source constructor check derives projected arity at the same child count. -/
theorem Fits.of_accepted (constraint : Constraint) (arity : Nat)
    (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (accepted : SourceEqualityMkEdgeAllocation.accepted constraint arity = true) :
    Fits constraint arity := by
  have fits : SourceEqualityMkEdgeAllocation.fits arity
      (SourceCompactGuards.sourceEqualities constraint) = true := by
    by_cases rejected : SourceEqualityMkEdgeAllocation.contradictory constraint = true
    · simp only [SourceEqualityMkEdgeAllocation.accepted, rejected, ↓reduceIte,
        Bool.false_eq_true] at accepted
    · simpa only [SourceEqualityMkEdgeAllocation.accepted, rejected, Bool.false_eq_true,
        ↓reduceIte] using accepted
  obtain ⟨classes, source, rootBounds⟩ := (SourceEqualityMkEdgeArity.fits_exact arity
    (SourceCompactGuards.sourceEqualities constraint)).mp fits
  obtain ⟨canonicalProjection, _validTries, pathReadback, _meaning⟩ :=
    (source ▸ SourcePruningEnumerationConstraint.project_complete constraint cached)
  intro tries residual projected start
  have projectionSame := Option.some.inj (canonicalProjection.symm.trans projected)
  have triesSame : EnumerationEquality.readClasses classes = tries := congrArg Prod.fst projectionSame
  rw [← triesSame]
  apply (fresh_arity_iff arity start (EnumerationEquality.readClasses classes)).mpr
  intro trie trieMember index suffix path
  obtain ⟨paths, pathsMember, same⟩ := List.mem_map.mp trieMember
  subst trie
  exact rootBounds paths pathsMember (index :: suffix)
    ((pathReadback paths pathsMember (index :: suffix)).mp path)

mutual
/-- Every original edge has normalized fields and passes the actual source constructor test. -/
def SourceChecked : Syntax Symbol Constraint → Prop
  | .empty | .var _ => True
  | .node edges => SourceEdgesChecked edges
  | .union members => SourceManyChecked members
  | .binder _ body => SourceChecked body

/-- Every original child plan retains its source constructor tests. -/
def SourceManyChecked : List (Syntax Symbol Constraint) → Prop
  | [] => True
  | first :: rest => SourceChecked first ∧ SourceManyChecked rest

/-- Each original edge uses its original number of child plans in the source test. -/
def SourceEdgesChecked : List (EdgeSyntax Symbol Constraint) → Prop
  | [] => True
  | .mk _ constraint children :: rest =>
      (SourceEqualityGuardReadback.Cached constraint.equalities ∧
        SourceEqualityMkEdgeAllocation.accepted constraint children.length = true) ∧
      SourceManyChecked children ∧ SourceEdgesChecked rest
end

mutual
/-- Original source checks derive the checked plan used by actual construction. -/
theorem source_checked (expression : Syntax Symbol Constraint) (checked : SourceChecked expression) :
    Checked expression := by
  cases expression with
  | empty | var => trivial
  | node edges => exact source_edges_checked edges checked
  | union members => exact source_many_checked members checked
  | binder smart body => exact source_checked body checked
termination_by sizeOf expression

/-- Original ordered child checks derive every nested projected-arity check. -/
theorem source_many_checked (expressions : List (Syntax Symbol Constraint))
    (checked : SourceManyChecked expressions) : ManyChecked expressions := by
  cases expressions with
  | nil => trivial
  | cons first rest =>
      exact ⟨source_checked first checked.1, source_many_checked rest checked.2⟩
termination_by sizeOf expressions

/-- Each actual source edge test derives its original syntactic arity check. -/
theorem source_edges_checked (expressions : List (EdgeSyntax Symbol Constraint))
    (checked : SourceEdgesChecked expressions) : EdgesChecked expressions := by
  cases expressions with
  | nil => trivial
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          exact ⟨Fits.of_accepted constraint children.length checked.1.1 checked.1.2,
            source_many_checked children checked.2.1,
            source_edges_checked rest checked.2.2⟩
termination_by sizeOf expressions
end

/-- The actual closed initial build derives stored arity from original source checks. -/
theorem constructed_heap_of_source [DecidableEq (EdgeKey Symbol Constraint)]
    (expression : Syntax Symbol Constraint) (checked : SourceChecked expression)
    (value : Value Symbol Constraint) (state : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state) :
    Heap state :=
  constructed_heap expression (source_checked expression checked) value state built

end MicroCFTA.SourcePruningEnumerationArityOrigins
