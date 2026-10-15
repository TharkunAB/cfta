import MicroCFTA.SourceEqualityConstraintGeometry
import MicroCFTA.SourceEqualityConstraintOrigins

/-!
# Finite stored equality payloads from original literal paths

Original paths supply a finite anchor list, alphabet, and segment bound.
Actual conjunction preserves this geometry through normalization. Successful
normalized components have bounded count and path lengths. Explicit bounded
lists therefore contain every derived physical equality payload.
-/
namespace MicroCFTA.SourceEqualityConstraintPathInventory
open Language EqualityNormalize EqualitySaturation EqualityTermination
open SourceEqualityConstraintOrigins SourceEqualityConstraintGeometry
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "sourceTop" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Retain every original physical class occurrence, including classes in stored binder bodies. -/
def inputs (literals : List Constraint) : Constraints :=
  literals.flatMap (fun literal => literal.equalities.getD [])

/-- Original path occurrences supply the fixed finite anchor list. -/
def anchors (literals : List Constraint) : List Path := (inputs literals).flatten

/-- Bound each original unmarked path segment by the original path budget. -/
def gap (literals : List Constraint) : Nat := EqualityTrie.pathBudget (anchors literals)

/-- Actual equality normalization introduces no child index outside this original alphabet. -/
def alphabet (literals : List Constraint) : List Nat := (anchors literals).flatten.eraseDups

/-- All successful derived paths lie in this fixed finite word domain. -/
def domain (literals : List Constraint) : List Path :=
  words (alphabet literals) (gap literals * ((anchors literals).length + 1))

/-- Every recorded literal path occurs in the original anchor list. -/
theorem literal_path (literals : List Constraint) (literal : Constraint) (included : literal ∈ literals)
    (classes : Constraints) (stored : literal.equalities = some classes) (path : Path) (member : path ∈ members classes) :
    path ∈ anchors literals := by
  obtain ⟨paths, present, atPath⟩ := (mem_members path classes).mp member
  apply List.mem_flatten.mpr
  refine ⟨paths, List.mem_flatMap.mpr ⟨literal, included, ?_⟩, atPath⟩
  simpa only [stored, Option.getD_some] using present

/-- Original normalized literal fields supply the shared segment, anchor, and alphabet invariants. -/
theorem literal_region (literals : List Constraint) (literal : Constraint) (included : literal ∈ literals)
    (cached : SourceEqualityGuardReadback.Cached literal.equalities) (classes : Constraints)
    (stored : literal.equalities = some classes) : Region (gap literals) (anchors literals) (alphabet literals) classes := by
  have active := (cached classes stored).1
  refine ⟨active, ?_, ?_, ?_⟩
  · intro path member
    exact .short (by simp) (by
      simpa only [List.length_nil, Nat.zero_add, gap] using Nat.le_of_lt
        (EqualityTrie.pathBudget_sufficient (anchors literals) path (literal_path literals literal included classes stored path member)))
  · intro paths present
    obtain ⟨path, atPath, _, _, _⟩ := active paths present
    exact ⟨path, atPath, literal_path literals literal included classes stored path ((mem_members path classes).mpr ⟨paths, present, atPath⟩)⟩
  · intro path member index atIndex
    simp only [alphabet, List.mem_eraseDups, List.mem_flatten]
    exact ⟨path, literal_path literals literal included classes stored path member, atIndex⟩

/-- Every actual derived payload retains its cached class representation and original path geometry. -/
theorem derived_regions (literals : List Constraint)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (constraint : Constraint) (derived : Derived literals sourceTop conjoin constraint) :
    SourceEqualityGuardReadback.Cached constraint.equalities ∧
      ∀ classes, constraint.equalities = some classes → Region (gap literals) (anchors literals) (alphabet literals) classes := by
  induction derived with
  | literal member => exact ⟨normalized _ member, literal_region literals _ member (normalized _ member)⟩
  | top =>
      refine ⟨SourceEqualityConstraintConstructors.top_cached, ?_⟩
      intro classes stored
      have same : classes = [] := Option.some.inj stored.symm
      subst classes
      exact SourceEqualityConstraintGeometry.empty _ _ _
  | @conjunction first second _ _ firstIH secondIH =>
      refine ⟨SourceEqualityConstraintConstructors.conjoin_cached _ first second, ?_⟩
      intro classes stored
      exact (SourceEqualityConstraintGeometry.combine (gap literals) (anchors literals) (alphabet literals)
        first.equalities second.equalities firstIH.1 secondIH.1 firstIH.2 secondIH.2 classes stored).1

/-- Enumerate all lists over a finite inventory up to a supplied length. -/
def lists {α : Type} (items : List α) : Nat → List (List α)
  | 0 => [[]]
  | bound + 1 => [] :: items.flatMap (fun item => (lists items bound).map (item :: ·))

/-- Bounded list enumeration has exactly its stated length and membership conditions. -/
theorem mem_lists {α : Type} (items : List α) (bound : Nat) (selected : List α) :
    selected ∈ lists items bound ↔ selected.length ≤ bound ∧ ∀ item ∈ selected, item ∈ items := by
  induction bound generalizing selected with
  | zero => cases selected <;> simp [lists]
  | succ bound ih =>
      cases selected with
      | nil => simp [lists]
      | cons item rest => simp [lists, ih, and_assoc, and_left_comm, and_comm]

/-- Retain literal payloads and enumerate every bounded normalized list of bounded classes. -/
def inventory (literals : List Constraint) : List (Option Constraints) :=
  literals.map (·.equalities) ++ none ::
    (lists (lists (domain literals) (domain literals).length) (anchors literals).length).map some

/-- An actual normalized component list belongs to the concrete finite payload inventory. -/
theorem normalized_mem_inventory (literals : List Constraint) (classes : Constraints)
    (cached : SourceEqualityGuardReadback.NormalClasses classes)
    (region : Region (gap literals) (anchors literals) (alphabet literals) classes)
    (normal : NormalState classes) (consistent : isContradicting classes = false) :
    some classes ∈ inventory literals := by
  have within := bounded_state (gap literals) (anchors literals) (alphabet literals) classes
    normal consistent region.segmented region.anchored region.allowed
  have classBound := anchored_class_bound (anchors literals) classes region.anchored normal.2.1
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  apply List.mem_map.mpr
  refine ⟨classes, (mem_lists _ _ _).mpr ⟨classBound, ?_⟩, rfl⟩
  intro paths present
  have unique : paths.Nodup := by
    rw [← cached.2.2 paths present]
    exact canonicalClass_nodup _
  have subset : ∀ path ∈ paths, path ∈ domain literals :=
    fun path atPath => within path ((mem_members path classes).mpr ⟨paths, present, atPath⟩)
  exact (mem_lists _ _ _).mpr ⟨unique.length_le_of_subset subset, subset⟩

/-- Every actual derived physical equality field occurs in the fixed original payload inventory. -/
theorem derived_mem_inventory (literals : List Constraint)
    (normalized : ∀ literal ∈ literals, SourceEqualityGuardReadback.Cached literal.equalities)
    (constraint : Constraint) (derived : Derived literals sourceTop conjoin constraint) :
    constraint.equalities ∈ inventory literals := by
  cases derived with
  | literal member => exact List.mem_append_left _ (List.mem_map.mpr ⟨_, member, rfl⟩)
  | top =>
      apply List.mem_append_right
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      refine ⟨[], (mem_lists _ _ _).mpr ⟨by simp, by simp⟩, rfl⟩
  | @conjunction first second firstDerived secondDerived =>
      cases stored : (conjoin first second).equalities with
      | none => exact List.mem_append_right _ List.mem_cons_self
      | some classes =>
          have firstFacts := derived_regions literals normalized first firstDerived
          have secondFacts := derived_regions literals normalized second secondDerived
          have combined := SourceEqualityConstraintGeometry.combine (gap literals) (anchors literals) (alphabet literals)
            first.equalities second.equalities firstFacts.1 secondFacts.1 firstFacts.2 secondFacts.2 classes stored
          exact normalized_mem_inventory literals classes
            (SourceEqualityConstraintConstructors.conjoin_cached _ first second classes stored) combined.1 combined.2.1 combined.2.2

end MicroCFTA.SourceEqualityConstraintPathInventory
