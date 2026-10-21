import MicroCFTA.SourceEqualityNativeDemandCellValidity
import MicroCFTA.SourceEqualityPCSConstructors

/-!
# Independent language of accepted checked edges

Ordered child intersection laws give the exact forest intersection.
Matching original symbols and actual conjoined constraints then give the
edge law. Closed child receipts supply these laws in the empty domain.
Actual ready-prefix execution derives literal combined constraint readback.
-/
namespace MicroCFTA.SourceEqualityNativeDemandAcceptedLanguage
open Language Cache InternedConstructorTemplates SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemandProvenance

/-- Ordered original child pairs and exact child results retain precisely their common term forests. -/
theorem forest_zip (holds : Guard → Term Symbol → Bool)
    (left right results : List (Value Symbol Guard)) (arity : left.length = right.length)
    (children : All₂ (fun pair result => ∀ ambient term,
      InternedGuardedLanguage.meaning holds ambient result term ↔
        InternedGuardedLanguage.meaning holds ambient pair.1 term ∧ InternedGuardedLanguage.meaning holds ambient pair.2 term)
      (left.zip right) results) (ambient : InternedGuardedLanguage.Env Symbol) (terms : List (Term Symbol)) :
    All₂ (InternedGuardedLanguage.meaning holds ambient) results terms ↔
      All₂ (InternedGuardedLanguage.meaning holds ambient) left terms ∧ All₂ (InternedGuardedLanguage.meaning holds ambient) right terms := by
  induction left generalizing right results terms with
  | nil =>
      have empty : right = [] := List.length_eq_zero_iff.mp arity.symm
      subst right
      cases children
      cases terms <;> constructor <;> intro runs
      · exact ⟨.nil, .nil⟩
      · exact .nil
      · cases runs
      · cases runs.1
  | cons first rest ih =>
      cases right with
      | nil => simp at arity
      | cons second tail =>
          cases children with
          | cons head remaining =>
              have nextArity : rest.length = tail.length := Nat.succ.inj arity
              cases terms with
              | nil =>
                  constructor
                  · intro runs; cases runs
                  · rintro ⟨runs, _⟩; cases runs
              | cons term terms =>
                  constructor
                  · intro runs
                    cases runs with
                    | cons accepted later =>
                        have both := (head ambient term).mp accepted
                        have tails := (ih tail _ nextArity remaining terms).mp later
                        exact ⟨.cons both.1 tails.1, .cons both.2 tails.2⟩
                  · rintro ⟨leftRuns, rightRuns⟩
                    cases leftRuns with
                    | cons leftHead leftTail => cases rightRuns with
                      | cons rightHead rightTail =>
                          exact .cons ((head ambient term).mpr ⟨leftHead, rightHead⟩)
                            ((ih tail _ nextArity remaining terms).mpr ⟨leftTail, rightTail⟩)

/-- Matching symbols, actual guard conjunction, and ordered child laws give exact complete edge intersection. -/
theorem edge_exact (holds : Guard → Term Symbol → Bool) (left right result : EdgeValue Symbol Guard)
    (arity : left.children.length = right.children.length) (symbols : left.entry.key.symbol = right.entry.key.symbol)
    (label : result.entry.key.symbol = left.entry.key.symbol)
    (guards : ∀ term, holds result.entry.key.constraint term = (holds left.entry.key.constraint term && holds right.entry.key.constraint term))
    (children : All₂ (fun pair child => ∀ ambient term,
      InternedGuardedLanguage.meaning holds ambient child term ↔
        InternedGuardedLanguage.meaning holds ambient pair.1 term ∧ InternedGuardedLanguage.meaning holds ambient pair.2 term)
      (left.children.zip right.children) result.children) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.edgeMeaning holds ambient result term ↔
      InternedGuardedLanguage.edgeMeaning holds ambient left term ∧ InternedGuardedLanguage.edgeMeaning holds ambient right term := by
  rw [InternedGuardedLanguage.edgeMeaning_all, InternedGuardedLanguage.edgeMeaning_all, InternedGuardedLanguage.edgeMeaning_all]
  constructor
  · rintro ⟨terms, shape, forest, guard⟩
    have both := (forest_zip holds _ _ _ arity children ambient terms).mp forest
    have gates := Bool.and_eq_true_iff.mp ((guards term).symm.trans guard)
    exact ⟨⟨terms, by rw [← label]; exact shape, both.1, gates.1⟩,
      ⟨terms, by rw [← symbols, ← label]; exact shape, both.2, gates.2⟩⟩
  · rintro ⟨⟨terms, shape, first, firstGuard⟩, ⟨other, secondShape, second, secondGuard⟩⟩
    have equal : other = terms := by
      rw [shape, ← symbols] at secondShape
      exact (Term.node.inj secondShape).2.symm
    subst other
    refine ⟨terms, by rw [label]; exact shape,
      (forest_zip holds _ _ _ arity children ambient terms).mpr ⟨first, second⟩, ?_⟩
    rw [guards term, firstGuard, secondGuard]
    rfl

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Actual ready-prefix execution derives literal raw-field conjunction at the original complete edge constraints. -/
theorem ready_readback (request : EdgeRequest Symbol Guard) (state : SourceEqualityNativeDemand.State width)
    (first second combined : Allocated) (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (ready : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined)) :
    SourceEqualityConjoinAllocation.readback combined = SourceEqualityConstraintConstructors.conjoin GuardStructuralOrder.le
      request.left.entry.key.constraint request.right.entry.key.constraint := by
  obtain ⟨firstReady, firstFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints leftCached first left
  obtain ⟨secondReady, secondFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints rightCached second right
  obtain ⟨branch, completed, source, _, _, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct GuardStructuralOrder.le
    first second request.left.children.length request.right.children.length state.operations valid firstReady secondReady
  have same : branch = .ready combined := Except.ok.inj (completed.symm.trans ready)
  rw [same] at source
  simp only [SourceEqualityIntersectionEdgeAllocation.Branch.map, SourceEqualityIntersectionEdgeAllocation.source,
    firstFields, secondFields, arity, ne_eq, not_true_eq_false, ↓reduceIte] at source
  split at source
  · exact SourceEqualityIntersectionEdgeAllocation.Branch.ready.inj source
  · cases source

/-- Ordered checked child receipts derive the closed empty-domain language of actual accepted edge fields. -/
theorem edgeMeaning_of_nodes (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard)
    (arity : request.left.children.length = request.right.children.length)
    (symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
    (label : result.entry.key.symbol = request.left.entry.key.symbol)
    (constraint : result.entry.key.constraint = SourceEqualityConstraintConstructors.conjoin GuardStructuralOrder.le
      request.left.entry.key.constraint request.right.entry.key.constraint)
    (children : All₂ (fun pair child => NodeMeaning (SourceEqualityPCSGuard.holds formulas solver)
      ⟨request.domain, pair.1, pair.2⟩ child) (request.left.children.zip request.right.children) result.children) :
    EdgeMeaning (SourceEqualityPCSGuard.holds formulas solver) request result := by
  intro domain leftClosed rightClosed ambient term
  apply edge_exact (SourceEqualityPCSGuard.holds formulas solver) request.left request.right result arity symbols label
  · intro term
    rw [constraint]
    exact SourceEqualityPCSConstructors.conjoined GuardStructuralOrder.le formulas solver _ _ term
  · apply MergedPhysicalGroupCalls.all₂_left_imp _ _ _ _ children
    intro pair member child meaning ambient term
    have originals := List.of_mem_zip member
    exact meaning domain (leftClosed pair.1 originals.1) (rightClosed pair.2 originals.2) ambient term

end MicroCFTA.SourceEqualityNativeDemandAcceptedLanguage
