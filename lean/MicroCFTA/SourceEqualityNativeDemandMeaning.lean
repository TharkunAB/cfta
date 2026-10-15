import MicroCFTA.SourceEqualityNativeDemandControl

/-!
# Independent language of stopped native edge demand

Arity mismatch has no common accepted term. An actual rejected checked
prefix also has no common accepted term. These facts use the original
complete constraints and independent guarded record semantics. They do not
need a child callback, replayed effects, or a future memo result law.
-/
namespace MicroCFTA.SourceEqualityNativeDemand
open Language InternedConstructorTemplates SourceRecursiveIntersectionThunks
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Independent guarded edge acceptance supplies original arity and full public constraint acceptance. -/
theorem edge_public (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (edge : EdgeValue Symbol Guard) (term : Term Symbol)
    (cached : SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities)
    (accepted : InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term) :
    ∃ terms, term = .node edge.entry.key.symbol terms ∧ terms.length = edge.children.length ∧
      SourceSymbolicIndex.acceptsConstraint formulas solver edge.entry.key.constraint term = true := by
  cases edge with
  | mk entry values =>
      rw [InternedGuardedLanguage.edgeMeaning] at accepted
      obtain ⟨terms, shape, forest, guard⟩ := accepted
      refine ⟨terms, shape, (InternedGuardedLanguage.forest_all _ ambient values terms |>.mp forest).length_eq.symm, ?_⟩
      rwa [SourceEqualityPCSGuard.public_eq formulas solver entry.key.constraint (SourceEqualityGuardReadback.active cached) term] at guard

/-- Different original edge arities reject every common finite term. -/
theorem mismatch_disjoint (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (left right : EdgeValue Symbol Guard)
    (leftCached : SourceEqualityGuardReadback.Cached left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached right.entry.key.constraint.equalities)
    (mismatch : left.children.length ≠ right.children.length) (term : Term Symbol) :
    ¬ (InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term) := by
  rintro ⟨first, second⟩
  obtain ⟨firstTerms, firstShape, firstLength, _⟩ := edge_public formulas solver ambient left term leftCached first
  obtain ⟨secondTerms, secondShape, secondLength, _⟩ := edge_public formulas solver ambient right term rightCached second
  have sameTerms := (Term.node.inj (firstShape.symm.trans secondShape)).2
  exact mismatch (firstLength.symm.trans ((congrArg List.length sameTerms).trans secondLength))

/-- A rejected source constructor check cannot discard a complete satisfying conjunction at its original arity. -/
theorem rejected_no_term (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (first second : Guard) (firstArity secondArity : Nat)
    (firstCached : SourceEqualityGuardReadback.Cached first.equalities)
    (secondCached : SourceEqualityGuardReadback.Cached second.equalities)
    (rejected : SourceEqualityIntersectionEdgeAllocation.source GuardStructuralOrder.le first second firstArity secondArity = .rejected)
    (symbol : Symbol) (terms : List (Term Symbol)) (arity : terms.length = firstArity) :
    ¬ (SourceSymbolicIndex.acceptsConstraint formulas solver first (.node symbol terms) = true ∧
      SourceSymbolicIndex.acceptsConstraint formulas solver second (.node symbol terms) = true) := by
  rintro ⟨firstAccepted, secondAccepted⟩
  let combined := SourceEqualityConstraintConstructors.conjoin GuardStructuralOrder.le first second
  have combinedAccepted : SourceSymbolicIndex.acceptsConstraint formulas solver combined (.node symbol terms) = true := by
    rw [SourceEqualityConstraintConstructors.conjoined GuardStructuralOrder.le formulas solver first second
      (SourceEqualityGuardReadback.active firstCached) (SourceEqualityGuardReadback.active secondCached), firstAccepted, secondAccepted]
    rfl
  have keep := SourceEqualityMkEdgeArity.accepted_of_source formulas solver combined
    (SourceEqualityGuardReadback.active (SourceEqualityConstraintConstructors.conjoin_cached GuardStructuralOrder.le first second))
    symbol terms combinedAccepted
  rw [arity] at keep
  unfold SourceEqualityIntersectionEdgeAllocation.source at rejected
  split at rejected
  · cases rejected
  · change (if SourceEqualityMkEdgeAllocation.accepted combined firstArity then
        SourceEqualityIntersectionEdgeAllocation.Branch.ready combined else .rejected) = .rejected at rejected
    rw [keep] at rejected
    cases rejected

/-- An actual completed allocation rejection has empty intersection language before any child demand. -/
theorem rejected_disjoint (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (request : EdgeRequest Symbol Guard) (state : State width)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (first second : Allocated)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint state.operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok .rejected) (term : Term Symbol) :
    ¬ (InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.left term ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient request.right term) := by
  obtain ⟨firstReady, firstFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints leftCached first left
  obtain ⟨secondReady, secondFields⟩ := SourceEqualityConstraintFieldLookup.load_ready _ _ valid.constraints rightCached second right
  obtain ⟨branch, done, source, _, _, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct GuardStructuralOrder.le first second
    request.left.children.length request.right.children.length state.operations valid firstReady secondReady
  have same : branch = .rejected := Except.ok.inj (done.symm.trans rejected)
  rw [same] at source
  have sourceRejected : SourceEqualityIntersectionEdgeAllocation.source GuardStructuralOrder.le
      request.left.entry.key.constraint request.right.entry.key.constraint request.left.children.length request.right.children.length = .rejected := by
    simpa only [SourceEqualityIntersectionEdgeAllocation.Branch.map, firstFields, secondFields] using source.symm
  rintro ⟨firstMeaning, secondMeaning⟩
  obtain ⟨terms, shape, arity, firstAccepted⟩ := edge_public formulas solver ambient request.left term leftCached firstMeaning
  obtain ⟨_, _, _, secondAccepted⟩ := edge_public formulas solver ambient request.right term rightCached secondMeaning
  rw [shape] at firstAccepted secondAccepted
  exact rejected_no_term formulas solver _ _ _ _ leftCached rightCached sourceRejected _ terms arity ⟨firstAccepted, secondAccepted⟩

end MicroCFTA.SourceEqualityNativeDemand
