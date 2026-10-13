import Std

/-!
# Shared rows in a projected binary equality class

Projection takes the union of endpoint occurrences. Each occurrence keeps
the source whole-node identity shortcut. Cartesian rows use a relation, so
symbol mismatch and constructor rejection can produce no row.

The diagonal premise applies to admitted canonical rows. It does not hold
for every raw guard before normalization. These results do not assert that
the complete equality schedule terminates.
-/
namespace MicroCFTA.EqualityFixedProjectionInvariant

/-- A complete set of canonical outgoing rows. -/
abbrev Rows (Row : Type u) := Row → Prop

/-- The outgoing rows of all occurrences selected by one path. -/
def project (group : Index → Rows Row) : Rows Row := fun row => ∃ index, group index row

/-- Apply the row relation to every pair of outgoing rows. -/
def product (join : Row → Row → Row → Prop) (left right : Rows Row) : Rows Row :=
  fun row => ∃ first second, left first ∧ right second ∧ join first second row

/-- Preserve an identical complete endpoint before the Cartesian product. -/
noncomputable def narrow (join : Row → Row → Row → Prop)
    (left right : Rows Row) : Rows Row := by
  classical
  exact if left = right then left else product join left right

/-- Edit each original occurrence with the same projected target. -/
noncomputable def edit (join : Row → Row → Row → Prop)
    (group : Index → Rows Row) (target : Rows Row) : Index → Rows Row :=
  fun index => narrow join (group index) target

/-- A shared row survives the diagonal pair or the whole-node shortcut. -/
theorem common_retained (join : Row → Row → Row → Prop)
    (diagonal : ∀ row, join row row row) (left right : Rows Row) (row : Row)
    (inLeft : left row) (inRight : right row) : narrow join left right row := by
  classical
  unfold narrow
  split
  · exact inLeft
  · exact ⟨row, row, inLeft, inRight, diagonal row⟩

/-- The whole-node shortcut only removes Cartesian output rows. -/
theorem narrow_subset_product (join : Row → Row → Row → Prop)
    (diagonal : ∀ row, join row row row) (left right : Rows Row) (row : Row)
    (present : narrow join left right row) : product join left right row := by
  classical
  unfold narrow at present
  split at present
  next same => exact ⟨row, row, present, same ▸ present, diagonal row⟩
  next => exact present

/-- An occurrence expands when its rows are contained in the target. -/
theorem occurrence_expands (join : Row → Row → Row → Prop)
    (diagonal : ∀ row, join row row row) (left right : Rows Row)
    (included : ∀ row, left row → right row) (row : Row) (present : left row) :
    narrow join left right row :=
  common_retained join diagonal left right row present (included row present)

/-- Each edited projection is contained in the full projected product. -/
theorem edited_subset_product (join : Row → Row → Row → Prop)
    (diagonal : ∀ row, join row row row) (group : Index → Rows Row)
    (target : Rows Row) (row : Row) (present : project (edit join group target) row) :
    product join (project group) target row := by
  rcases present with ⟨index, found⟩
  rcases narrow_subset_product join diagonal (group index) target row found with
    ⟨first, second, inFirst, inSecond, combined⟩
  exact ⟨first, second, ⟨index, inFirst⟩, inSecond, combined⟩

/-- Without a whole-node shortcut, projection distributes over the edit. -/
theorem edited_product (join : Row → Row → Row → Prop)
    (group : Index → Rows Row) (target : Rows Row)
    (distinct : ∀ index, group index ≠ target) :
    project (edit join group target) = product join (project group) target := by
  classical
  funext row
  apply propext
  constructor
  · rintro ⟨index, found⟩
    have pair : product join (group index) target row := by
      simpa only [edit, narrow, ite_eq_right (distinct index)] using found
    rcases pair with ⟨first, second, inFirst, inSecond, combined⟩
    exact ⟨first, second, ⟨index, inFirst⟩, inSecond, combined⟩
  · rintro ⟨first, second, ⟨index, inFirst⟩, inSecond, combined⟩
    refine ⟨index, ?_⟩
    simpa only [edit, narrow, ite_eq_right (distinct index)] using
      (show product join (group index) target row from
        ⟨first, second, inFirst, inSecond, combined⟩)

/-- A missing Cartesian result requires an occurrence equal to the whole target. -/
theorem missing_product_requires_target (join : Row → Row → Row → Prop)
    (group : Index → Rows Row) (target : Rows Row)
    (different : project (edit join group target) ≠ product join (project group) target) :
    ∃ index, group index = target := by
  classical
  apply Classical.byContradiction
  intro absent
  apply different
  exact edited_product join group target (fun index same => absent ⟨index, same⟩)

/-- A whole-target occurrence makes the target a subset of its projection. -/
theorem target_subset (group : Index → Rows Row) (target : Rows Row)
    (whole : ∃ index, group index = target) (row : Row) (present : target row) :
    project group row := by
  rcases whole with ⟨index, same⟩
  exact ⟨index, same ▸ present⟩

/-- Every row shared by both peer projections survives in each edited projection. -/
theorem peer_common_retained (join : Row → Row → Row → Prop)
    (diagonal : ∀ row, join row row row) (left : Left → Rows Row) (right : Right → Rows Row)
    (row : Row) (inLeft : project left row) (inRight : project right row) :
    project (edit join left (project right)) row ∧
      project (edit join right (project left)) row := by
  rcases inLeft with ⟨leftIndex, foundLeft⟩
  rcases inRight with ⟨rightIndex, foundRight⟩
  exact ⟨⟨leftIndex, common_retained join diagonal _ _ row foundLeft ⟨rightIndex, foundRight⟩⟩,
    ⟨rightIndex, common_retained join diagonal _ _ row foundRight ⟨leftIndex, foundLeft⟩⟩⟩

/-- Equal aggregate projections make every individual occurrence expand. -/
theorem equal_peers_expand (join : Row → Row → Row → Prop)
    (diagonal : ∀ row, join row row row) (left : Left → Rows Row) (right : Right → Rows Row)
    (same : project left = project right) (index : Left) (row : Row) (present : left index row) :
    edit join left (project right) index row :=
  common_retained join diagonal _ _ row present (same ▸ ⟨index, present⟩)

/-- Commutative row intersection gives the same full projected product in either order. -/
theorem product_comm (join : Row → Row → Row → Prop)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (left right : Rows Row) : product join left right = product join right left := by
  funext row
  apply propext
  constructor
  · rintro ⟨first, second, inFirst, inSecond, combined⟩
    exact ⟨second, first, inSecond, inFirst, (symmetric first second row).mp combined⟩
  · rintro ⟨second, first, inSecond, inFirst, combined⟩
    exact ⟨first, second, inFirst, inSecond, (symmetric second first row).mp combined⟩

/-- Incomparable projections cannot use a whole-target occurrence shortcut. -/
theorem incomparable_equalizes (join : Row → Row → Row → Prop)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (left : Left → Rows Row) (right : Right → Rows Row)
    (leftOutside : ∃ row, project left row ∧ ¬ project right row)
    (rightOutside : ∃ row, project right row ∧ ¬ project left row) :
    project (edit join left (project right)) = project (edit join right (project left)) := by
  have leftDistinct : ∀ index, left index ≠ project right := by
    intro index same
    rcases rightOutside with ⟨row, present, absent⟩
    exact absent (target_subset left (project right) ⟨index, same⟩ row present)
  have rightDistinct : ∀ index, right index ≠ project left := by
    intro index same
    rcases leftOutside with ⟨row, present, absent⟩
    exact absent (target_subset right (project left) ⟨index, same⟩ row present)
  rw [edited_product join left _ leftDistinct, edited_product join right _ rightDistinct]
  exact product_comm join symmetric _ _

/-- Every original occurrence expands after the first reciprocal binary edit. -/
theorem post_first_expands (join : Row → Row → Row → Prop)
    (diagonal : ∀ row, join row row row)
    (symmetric : ∀ first second row, join first second row ↔ join second first row)
    (left : Left → Rows Row) (right : Right → Rows Row) (index : Left) (row : Row)
    (present : edit join left (project right) index row) :
    edit join (edit join left (project right))
      (project (edit join right (project left))) index row := by
  classical
  by_cases inPeer : project (edit join right (project left)) row
  · exact common_retained join diagonal _ _ row present inPeer
  · rcases narrow_subset_product join diagonal (left index) (project right) row present with
      ⟨first, second, inFirst, ⟨peerIndex, inSecond⟩, combined⟩
    have whole : right peerIndex = project left := by
      apply Classical.byContradiction
      intro distinct
      apply inPeer
      refine ⟨peerIndex, ?_⟩
      simp only [edit, narrow, ite_eq_right distinct]
      exact ⟨second, first, inSecond, ⟨index, inFirst⟩,
        (symmetric first second row).mp combined⟩
    have firstInPeer : project right first :=
      target_subset right (project left) ⟨peerIndex, whole⟩ first ⟨index, inFirst⟩
    have firstKept : edit join left (project right) index first :=
      common_retained join diagonal _ _ first inFirst firstInPeer
    have secondKept : project (edit join right (project left)) second :=
      ⟨peerIndex, common_retained join diagonal _ _ second inSecond (whole ▸ inSecond)⟩
    change narrow join (edit join left (project right) index)
      (project (edit join right (project left))) row
    rw [narrow]
    split
    · exact present
    · exact ⟨first, second, firstKept, secondKept, combined⟩

end MicroCFTA.EqualityFixedProjectionInvariant
