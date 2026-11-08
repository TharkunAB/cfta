import MicroCFTA.SourceSynthesisVariablePaths
import MicroCFTA.EqualityNormalizePrefixFree

/-!
# Original paths in the actual normalized generalization field

The computed eqGuard field retains only original recognized leaf paths.
Failure returns no classes. Both branches are handled from the computation.
The results do not extend to later inherited-constraint conjunctions.
-/
namespace MicroCFTA.SourceSynthesisNormalizedVariablePaths
open SourceSynthesisTypeSyntax (Ty)
open SourceSynthesisGeneralizeSyntax
open SourceSynthesisVariablePaths

private theorem raw_prefix_free (typ : Ty) :
    ∀ first ∈ EqualityNormalize.members (equalityClasses typ),
      ∀ second ∈ EqualityNormalize.members (equalityClasses typ), first.IsPrefix second → first = second := by
  intro first firstMember second secondMember pfx
  obtain ⟨firstClass, firstIncluded, firstFound⟩ := (EqualityNormalize.mem_members _ _).mp firstMember
  obtain ⟨secondClass, secondIncluded, secondFound⟩ := (EqualityNormalize.mem_members _ _).mp secondMember
  exact equalityClasses_prefix_free typ firstClass secondClass firstIncluded secondIncluded firstFound secondFound pfx

/-- Every path in the computed stored field belongs to the original raw classes. -/
theorem eqGuard_mem_original (typ : Ty) (path : List Nat)
    (member : path ∈ EqualityNormalize.members ((eqGuard (equalityClasses typ)).equalities.getD [])) :
    path ∈ EqualityNormalize.members (equalityClasses typ) := by
  cases computed : SourceCompactGuards.normalize (equalityClasses typ) with
  | none =>
      simp [eqGuard_eq_source, computed, EqualityNormalize.members] at member
  | some output =>
      have outputMember : path ∈ EqualityNormalize.members output := by
        simpa only [eqGuard_eq_source, computed, Option.getD] using member
      exact EqualityNormalizePrefixFree.normalize_mem_original (equalityClasses typ) output
        (raw_prefix_free typ) computed path outputMember

/-- Every stored normalized endpoint is an exact original recognized variable occurrence. -/
theorem eqGuard_occurrence (typ : Ty) (path : List Nat)
    (member : path ∈ EqualityNormalize.members ((eqGuard (equalityClasses typ)).equalities.getD [])) :
    ∃ name, (name, path) ∈ occurrences typ := by
  obtain ⟨paths, included, found⟩ := (EqualityNormalize.mem_members _ _).mp (eqGuard_mem_original typ path member)
  exact equalityClasses_occurrence typ paths included path found

/-- All stored normalized endpoints are jointly prefix-free. -/
theorem eqGuard_prefix_free (typ : Ty) (first second : List Nat)
    (firstMember : first ∈ EqualityNormalize.members ((eqGuard (equalityClasses typ)).equalities.getD []))
    (secondMember : second ∈ EqualityNormalize.members ((eqGuard (equalityClasses typ)).equalities.getD []))
    (pfx : first.IsPrefix second) : first = second := by
  obtain ⟨firstName, firstFound⟩ := eqGuard_occurrence typ first firstMember
  obtain ⟨secondName, secondFound⟩ := eqGuard_occurrence typ second secondMember
  exact occurrences_prefix_free typ firstFound secondFound pfx

/-- The actual normalized field retains the original type-size path bound. -/
theorem eqGuard_length_lt_sizeOf (typ : Ty) (path : List Nat)
    (member : path ∈ EqualityNormalize.members ((eqGuard (equalityClasses typ)).equalities.getD [])) :
    path.length < sizeOf typ := by
  obtain ⟨name, found⟩ := eqGuard_occurrence typ path member
  exact occurrences_length_lt_sizeOf typ name path found

/-- A literal stored-class endpoint has its original occurrence and size bound. -/
theorem eqGuard_class_paths (typ : Ty) (paths : List (List Nat))
    (included : paths ∈ (eqGuard (equalityClasses typ)).equalities.getD [])
    (path : List Nat) (member : path ∈ paths) :
    (∃ name, (name, path) ∈ occurrences typ) ∧ path.length < sizeOf typ := by
  have stored := (EqualityNormalize.mem_members _ _).mpr ⟨paths, included, member⟩
  exact ⟨eqGuard_occurrence typ path stored, eqGuard_length_lt_sizeOf typ path stored⟩

end MicroCFTA.SourceSynthesisNormalizedVariablePaths
