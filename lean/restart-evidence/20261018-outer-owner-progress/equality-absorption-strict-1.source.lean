import MicroCFTA.SourceCurrentEqualityNormalizationFixed

/-!
# Exact normalization with covered additional classes

A fixed inherited payload already contains every path and equality in a
covered own class. Adding those classes retains the exact ordered payload.
The result uses the actual array normalizer, not only logical equivalence.
-/
namespace MicroCFTA.SourceCurrentEqualityAbsorption
open EqualityNormalize EqualitySaturation
open SourceCurrentEqualityNormalizationFixed (Fixed)

private theorem connected_covered (first second : Constraints) (covered : Covers first second)
    (left right : Path) (connected : Connected first left right) : Connected second left right := by
  induction connected with
  | edge paths member firstPath secondPath =>
      obtain ⟨component,present,included⟩ := covered paths member
      exact .edge component present (included _ firstPath) (included _ secondPath)
  | trans _ _ firstIH secondIH => exact .trans firstIH secondIH

private theorem prepared_covers (first second : Constraints) (covered : Covers first second) :
    Covers (prepare first) second := by
  intro paths member
  obtain ⟨source,present,rfl⟩ := List.mem_map.mp (List.mem_filter.mp member).1
  obtain ⟨component,known,included⟩ := covered source present
  exact ⟨component,known,fun path member => included path (List.mem_eraseDups.mp member)⟩

private theorem prepared_edge (classes : Constraints) (paths : Class) (member : paths ∈ classes)
    (active : Nontrivial paths) (left right : Path) (first : left ∈ paths) (second : right ∈ paths) :
    Connected (prepare classes) left right := by
  have retained : Nontrivial paths.eraseDups := by
    obtain ⟨a,first,b,second,different⟩ := active
    exact ⟨a,List.mem_eraseDups.mpr first,b,List.mem_eraseDups.mpr second,different⟩
  exact .edge paths.eraseDups (List.mem_filter.mpr
    ⟨List.mem_map.mpr ⟨paths,member,rfl⟩,(nontrivialB_correct _).mpr retained⟩)
    (List.mem_eraseDups.mpr first) (List.mem_eraseDups.mpr second)

/-- Covered own classes do not change the exact normalized inherited class list. -/
theorem normalize_append (inherited own : Constraints) (fixed : Fixed inherited)
    (covered : Covers own inherited) :
    SourceCompactGuards.normalize (inherited ++ own) = some inherited := by
  have invariant := SourceCurrentEqualityNormalizationFixed.invariants inherited fixed
  have normal := step_normal inherited inherited invariant.1 invariant.2.2.2
  have coverage : Covers (inherited ++ own) inherited := by
    intro paths member
    rcases List.mem_append.mp member with old | added
    · exact ⟨paths,old,fun _ present => present⟩
    · exact covered paths added
  have completed : complete (prepare (inherited ++ own)) = inherited := by
    apply complete_matches_partition _ inherited (prepare_active _) normal.1 normal.2.1
      normal.2.2.1 normal.2.2.2
    intro left right
    constructor
    · rintro ⟨paths,member,first,second⟩
      exact prepared_edge (inherited ++ own) paths (List.mem_append_left _ member)
        (normal.1 paths member) left right first second
    · intro connected
      exact (inSame_correct inherited left right).mp
        ((normal_connected inherited normal left right).mpr
          (connected_covered _ _ (prepared_covers _ _ coverage) left right connected))
  have one : mkEqConstraints 1 (inherited ++ own) = .normalized inherited := by
    simp only [mkEqConstraints,completed,fixMaybe,invariant.2.2.2,ite_true]
  have array := SourceEqualityNormalizationReceipt.array_eq 1 (inherited ++ own)
    (by rw [one]; intro impossible; cases impossible)
  unfold SourceCompactGuards.normalize
  rw [array,one]
  rfl

/-- Actual source combination absorbs covered own classes in either empty-list branch. -/
theorem combine (inherited own : Constraints) (fixed : Fixed inherited)
    (covered : Covers own inherited) :
    SourceCompactGuards.combineEqualities (some inherited) (some own) = some inherited := by
  cases inherited with
  | nil =>
      have empty : own = [] := by
        cases own with
        | nil => rfl
        | cons first rest =>
            obtain ⟨component,impossible,_⟩ := covered first List.mem_cons_self
            cases impossible
      subst own
      rfl
  | cons first rest => exact normalize_append (first :: rest) own fixed covered

end MicroCFTA.SourceCurrentEqualityAbsorption
