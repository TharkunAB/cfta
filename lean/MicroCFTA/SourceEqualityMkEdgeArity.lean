import MicroCFTA.SourceEqualityMkEdgeAllocation

/-!
# Meaning of the checked source edge arity test

Represented natural paths pass the signed source test exactly when their
first child index is in range. The test accepts the root path. A complete
term that satisfies a source constraint passes both constructor checks.
This result needs the source active-class invariant. Machine index bounds
and the relation between represented children and heap nodes are separate.
-/
namespace MicroCFTA.SourceEqualityMkEdgeArity
open Language EqualityNormalize SourceObservations SourceGuards SourceSymbolicIndex SourceCompactGuards
open SourceEqualityMkEdgeAllocation SourceEqualityGuardReadback

/-- Natural paths contain no negative source indices; only the first index is checked here. -/
theorem fitsPath_cast (arity : Nat) (path : List Nat) :
    SymbolicSignedPaths.fitsPath arity (path.map Int.ofNat) =
      match path with
      | [] => true
      | first :: _ => decide (first < arity) := by
  cases path with
  | nil => rfl
  | cons first rest => simp [SymbolicSignedPaths.fitsPath, List.all_map, List.all_eq_true]

/-- The exact source test checks root bounds on every represented natural path. -/
theorem fits_exact (arity : Nat) (classes : Option Constraints) :
    fits arity classes = true ↔
      ∃ records, classes = some records ∧
        ∀ paths ∈ records, ∀ path ∈ paths,
          match path with
          | [] => True
          | first :: _ => first < arity := by
  cases classes with
  | none => simp [fits, signed, SymbolicSignedPaths.fitsArity]
  | some records =>
      simp only [fits, signed, Option.map_some, SymbolicSignedPaths.fitsArity,
        List.all_map, List.all_eq_true, Option.some.injEq, exists_eq_left']
      apply forall₂_congr
      intro paths member
      simp only [Function.comp_apply, List.all_map, List.all_eq_true]
      apply forall₂_congr
      intro path present
      rw [fitsPath_cast]
      cases path <;> simp

/-- An existing represented subtree supplies the root-child bound needed by the source test. -/
theorem lookup_root_bound (symbol : Symbol) (children : List (Term Symbol))
    (first : Nat) (rest : List Nat) (part : Term Symbol)
    (found : (Term.node symbol children).atPath (first :: rest) = some part) :
    first < children.length := by
  by_cases inside : first < children.length
  · exact inside
  · simp [Term.atPath, List.getElem?_eq_none (by omega : children.length ≤ first)] at found

/-- Satisfied active source classes pass the actual signed arity check after natural-index casts. -/
theorem fits_of_sat (symbol : Symbol) (children : List (Term Symbol)) (classes : Option Constraints)
    (active : ActiveOption classes) (satisfied : Sat (.node symbol children) classes) :
    fits children.length classes = true := by
  apply (fits_exact children.length classes).mpr
  cases classes with
  | none => exact False.elim satisfied
  | some records =>
      refine ⟨records, rfl, ?_⟩
      intro paths member path present
      obtain ⟨part, found⟩ := SourceCompactGuards.satisfied_path (.node symbol children) paths
        (SymbolicEqualityBridge.pcs_implies_common _ paths (active records rfl paths member)
          (satisfied paths member)) path present
      cases path with
      | nil => trivial
      | cons first rest => exact lookup_root_bound symbol children first rest part found

/-- Complete public acceptance excludes both stored contradiction and the outer Bottom guard. -/
theorem not_contradictory [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (term : Term (Label Formula))
    (accepted : acceptsConstraint formulas solver constraint term = true) :
    contradictory constraint = false := by
  have stored := (Bool.and_eq_true_iff.mp accepted).1
  have guard := (Bool.and_eq_true_iff.mp accepted).2
  cases constraint with
  | mk equalities termGuard =>
      cases equalities with
      | none => simp [ConstraintIndicators.equalityValue] at stored
      | some records =>
          cases termGuard <;> first
            | rfl
            | simp [SourceBooleanEntry.evaluateGuard, SourceBooleanEntry.evaluateGuardWithSame,
                SourceBooleanEntry.evaluate, SourceBooleanEntry.scoped_eq, SourceGuards.evaluateWith,
                SourceGuards.polarize] at guard

/-- The exact checked source constructor retains every satisfying complete term at its represented arity. -/
theorem accepted_of_source [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (active : ActiveOption constraint.equalities)
    (symbol : Label Formula) (children : List (Term (Label Formula)))
    (source : acceptsConstraint formulas solver constraint (.node symbol children) = true) :
    accepted constraint children.length = true := by
  have possible := not_contradictory formulas solver constraint (.node symbol children) source
  simp only [accepted, possible, Bool.false_eq_true, ↓reduceIte]
  exact fits_of_sat symbol children (sourceEqualities constraint) (sourceEqualities_active constraint active)
    (accepted_sat formulas solver constraint active (.node symbol children) source)

/-- A ready physical value supplies the source active-class condition without another representation premise. -/
theorem ready_active (stored : SourceEqualityConstraintAllocation.Value) (guard : Guard Formula)
    (ready : SourceEqualityConstraintAllocation.Ready cache stored) :
    ActiveOption (SourceEqualityAccessorAllocation.constraint stored guard).equalities := by
  cases stored with
  | contradiction => intro classes same; cases same
  | live identity records =>
      intro classes same paths member
      have identical : records.map SourceEqualityClassOrder.Record.paths = classes := Option.some.inj same
      subst classes
      obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
      exact (ready.2 records rfl record present).2.2

/-- A satisfying complete term makes the actual accessor allocation check return true. -/
theorem check_of_source [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (stored : SourceEqualityConstraintAllocation.Value) (guard : Guard Formula)
    (symbol : Label Formula) (children : List (Term (Label Formula)))
    (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (ready : SourceEqualityConstraintAllocation.Ready before.constraints stored)
    (source : acceptsConstraint formulas solver (SourceEqualityAccessorAllocation.constraint stored guard)
      (.node symbol children) = true) :
    (check stored guard children.length before).1 = .ok true ∧
      SourceEqualityConstraintMemoAllocation.Valid (check stored guard children.length before).2 ∧
      SourceEqualityConstraintMemoAllocation.Grows before (check stored guard children.length before).2 := by
  have kept := accepted_of_source formulas solver (SourceEqualityAccessorAllocation.constraint stored guard)
    (ready_active stored guard ready) symbol children source
  simpa only [kept] using check_correct stored guard children.length before valid ready

/-- A satisfying term at the represented child arity selects the original complete edge request. -/
theorem build_of_source [DecidableEq Formula]
    [DecidableEq (InternedConstructorTemplates.EdgeKey (Label Formula) (Constraint Formula))]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (stored : SourceEqualityConstraintAllocation.Value) (guard : Guard Formula) (symbol : Label Formula)
    (children : List (InternedConstructorTemplates.Value (Label Formula) (Constraint Formula)))
    (terms : List (Term (Label Formula))) (arity : children.length = terms.length)
    (before : SourceEqualityConstraintMemoAllocation.State)
    (heap : InternedConstructorTemplates.State (Label Formula) (Constraint Formula))
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (ready : SourceEqualityConstraintAllocation.Ready before.constraints stored)
    (source : acceptsConstraint formulas solver (SourceEqualityAccessorAllocation.constraint stored guard)
      (.node symbol terms) = true) :
    let built := InternedConstructorTemplates.run
      (InternedConstructorTemplates.makeEdge symbol (SourceEqualityAccessorAllocation.constraint stored guard) children) heap
    build symbol stored guard children before heap =
      (.ok built.1, (check stored guard children.length before).2, built.2) ∧
      SourceEqualityConstraintMemoAllocation.Valid (build symbol stored guard children before heap).2.1 ∧
      SourceEqualityConstraintMemoAllocation.Grows before (build symbol stored guard children before heap).2.1 := by
  have kept : accepted (SourceEqualityAccessorAllocation.constraint stored guard) children.length = true := by
    rw [arity]
    exact accepted_of_source formulas solver _ (ready_active stored guard ready) symbol terms source
  simpa only [kept, work, outputState, ↓reduceIte] using build_receipt symbol stored guard children before heap valid ready

end MicroCFTA.SourceEqualityMkEdgeArity
