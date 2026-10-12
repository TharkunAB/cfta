import MicroCFTA.EqualityLeafProjectionAdmission
import MicroCFTA.SymbolicSignedPaths

/-!
# Derive leaf admission from the source constructor check

A canonical nullary guard that passes source equality arity checking has
no nontrivial positive equality. The admitted leaf carrier therefore covers
every surviving canonical row with empty stored equalities.
-/
namespace MicroCFTA.EqualityLeafProjectionAdmittedSource
open Language SourceGuards FullSyntax SourceCompactGuards SymbolicDriver
open EqualityLeafProjectionAdmission

/-- The natural-path view of source arity zero accepts only root paths. -/
def fitsLeaf : Option (List (List (List Nat))) → Bool
  | none => false
  | some classes => classes.all fun paths => paths.all List.isEmpty

/-- Signed source path checking at arity zero is exactly empty-path checking. -/
theorem fitsPath_zero (path : List Nat) :
    SymbolicSignedPaths.fitsPath 0 (path.map Int.ofNat) = path.isEmpty := by
  cases path <;> simp [SymbolicSignedPaths.fitsPath]

/-- The copied natural check agrees with the actual signed source arity test. -/
theorem fitsLeaf_source (classes : Option (List (List (List Nat)))) :
    fitsLeaf classes = SymbolicSignedPaths.fitsArity 0
      (classes.map fun groups => groups.map fun paths => paths.map fun path => path.map Int.ofNat) := by
  cases classes <;> simp [fitsLeaf, SymbolicSignedPaths.fitsArity, List.all_map, Function.comp_def, fitsPath_zero]

/-- A nullary term has no proper subtree. -/
theorem leaf_path (path : List Nat) (value : Term Unit)
    (found : (Term.node () []).atPath path = some value) : path = [] := by
  cases path with
  | nil => rfl
  | cons index rest => simp [Term.atPath] at found

/-- The only two existing equal paths in a nullary term are both root paths. -/
theorem leaf_pair (left right : List Nat)
    (accepted : classTest (Term.node () []) [left, right] = true) : left = right := by
  classical
  have common : Symbolic.ClassSatisfied (.node () []) [left, right] := of_decide_eq_true accepted
  obtain ⟨value, first, others⟩ := common
  exact (leaf_path left value first).trans (leaf_path right value (others right (by simp))).symm

/-- All paths admitted at arity zero select the same leaf term. -/
theorem class_leaf (paths : List (List Nat)) (fits : paths.all List.isEmpty = true) :
    classTest (Term.node () []) paths = true := by
  classical
  apply decide_eq_true
  cases paths with
  | nil => trivial
  | cons first rest =>
      have all : ∀ path ∈ first :: rest, path = [] := by
        intro path member
        exact List.isEmpty_iff.mp (List.all_eq_true.mp fits path member)
      refine ⟨.node () [], ?_, ?_⟩
      · simp [all first (by simp), Term.atPath]
      · intro path member
        simp [all path (by simp [member]), Term.atPath]

/-- A successful source arity-zero check implies satisfaction by the leaf. -/
theorem fitsLeaf_value (classes : Option (List (List (List Nat)))) (fits : fitsLeaf classes = true) :
    ConstraintIndicators.equalityValue (classTest (Term.node () [])) classes = true := by
  cases classes with
  | none => cases fits
  | some groups =>
      apply List.all_eq_true.mpr
      intro paths member
      exact class_leaf paths (List.all_eq_true.mp fits paths member)

mutual
  /-- A positive guard satisfied by a leaf has no remaining outer guard atom. -/
  theorem positive_leaf_atoms (guard : Guard Formula) (raw : List (List (List Nat)))
      (extracted : positive guard = some raw) (accepted : raw.all (classTest (Term.node () [])) = true) :
      GuardConjunction.atoms guard = [] := by
    cases guard with
    | top => simp [GuardConjunction.atoms]
    | same left right =>
        simp only [positive] at extracted
        split at extracted
        next different =>
          cases Option.some.inj extracted
          have same := leaf_pair left right (by simpa using accepted)
          exact False.elim (different same)
        next equal => cases extracted
    | and parts => simpa only [GuardConjunction.atoms] using positive_leaf_atoms_list parts raw extracted accepted
    | bottom | entails | satisfies | holds | substitute | not | or => cases extracted

  /-- Every accepted positive conjunct has an empty outer atom list. -/
  theorem positive_leaf_atoms_list (guards : List (Guard Formula)) (raw : List (List (List Nat)))
      (extracted : positiveList guards = some raw) (accepted : raw.all (classTest (Term.node () [])) = true) :
      guards.flatMap GuardConjunction.atoms = [] := by
    cases guards with
    | nil => rfl
    | cons first rest =>
        simp only [positiveList, Bind.bind, Pure.pure, Option.bind_eq_some_iff, Option.some.injEq] at extracted
        obtain ⟨initial, head, remaining, tail, rfl⟩ := extracted
        have both : initial.all (classTest (Term.node () [])) = true ∧
            remaining.all (classTest (Term.node () [])) = true := by
          simpa only [List.all_append, Bool.and_eq_true] using accepted
        simp [positive_leaf_atoms first initial head both.1,
          positive_leaf_atoms_list rest remaining tail both.2]
end

/-- Reading stored-empty source equalities agrees with the raw positive guard classes. -/
theorem source_leaf_value (guard : Guard Formula) (raw : List (List (List Nat)))
    (extracted : positive guard = some raw) :
    ConstraintIndicators.equalityValue (classTest (Term.node () []))
        (sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) guard)) =
      raw.all (classTest (Term.node () [])) := by
  obtain ⟨added, found, active, same⟩ := positiveNormalized_exact (Symbol := Unit) guard raw extracted
  have emptyActive : ActiveOption (some []) := by simp [ActiveOption, EqualityNormalize.Active]
  unfold sourceEqualities
  rw [found]
  cases added with
  | none => simpa [combineEqualities, ConstraintIndicators.equalityValue] using same (.node () [])
  | some classes =>
      cases classes with
      | nil => exact same (.node () [])
      | cons first rest =>
          rw [combine_value (some []) (some (first :: rest)) emptyActive active]
          simpa [ConstraintIndicators.equalityValue] using same (.node () [])

/-- Every canonical source leaf that passes arity checking satisfies the admission condition. -/
theorem source_admitted (guard : Guard Formula)
    (canonical : GuardConjunction.normalize GuardStructuralOrder.le guard = guard)
    (fits : fitsLeaf (sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) guard)) = true) :
    NoLeafEquality guard := by
  cases positiveFound : (positive guard).isSome with
  | false => exact Or.inl positiveFound
  | true =>
      obtain ⟨raw, extracted⟩ := Option.isSome_iff_exists.mp positiveFound
      have accepted := fitsLeaf_value _ fits
      rw [source_leaf_value guard raw extracted] at accepted
      have empty := positive_leaf_atoms guard raw extracted accepted
      right
      rw [← canonical, GuardConjunction.normalize, empty]
      simp [GuardConjunction.canonical, GuardConjunction.conjoin]

/-- The actual signed source check also derives admission after natural-path readback. -/
theorem signed_source_admitted (guard : Guard Formula)
    (canonical : GuardConjunction.normalize GuardStructuralOrder.le guard = guard)
    (fits : SymbolicSignedPaths.fitsArity 0
      ((sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) guard)).map
        fun groups => groups.map fun paths => paths.map fun path => path.map Int.ofNat) = true) :
    NoLeafEquality guard :=
  source_admitted guard canonical (by simpa only [fitsLeaf_source] using fits)

/-- The carrier's equality condition is exactly source arity-zero admission for canonical guards. -/
theorem admitted_iff (guard : Guard Formula)
    (canonical : GuardConjunction.normalize GuardStructuralOrder.le guard = guard) :
    NoLeafEquality guard ↔ fitsLeaf (sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) guard)) = true := by
  constructor
  · intro admitted
    rw [source_equalities guard admitted]
    rfl
  · exact source_admitted guard canonical

/-- Package every surviving canonical source row in the physical finite carrier. -/
def fromSource (initial : List (Guard Formula)) (guard : Guard Formula)
    (canonical : GuardConjunction.normalize GuardStructuralOrder.le guard = guard)
    (atoms : ∀ atom ∈ GuardConjunction.atoms guard, atom ∈ SourceLeafRowProgress.basis initial)
    (survives : guard ≠ .bottom)
    (fits : fitsLeaf (sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) guard)) = true) :
    Row initial :=
  ⟨⟨⟨guard, canonical, atoms⟩, survives⟩, source_admitted guard canonical fits⟩

/-- Admission preserves the complete original residual guard exactly. -/
theorem fromSource_guard (initial : List (Guard Formula)) (guard : Guard Formula) (canonical atoms survives fits) :
    (fromSource initial guard canonical atoms survives fits).val.val.val = guard := rfl

end MicroCFTA.EqualityLeafProjectionAdmittedSource
