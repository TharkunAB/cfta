import MicroCFTA.EqualityLeafProjectionProgress

/-!
# Removing dead occurrence rows

Trimming may replace an occurrence by empty and remove original ancestor
rows. It retains leaf payloads, surviving row tags, and child positions.
Every trim has decreasing occurrence weight unless its syntax is unchanged.
-/
namespace MicroCFTA.EqualityLeafProjectionTrim
open EqualityLeafProjectionSyntax

mutual
/-- A retained occurrence has the same leaf payload or a trimmed ancestor. -/
inductive Trim : Tree Tag Leaf → Tree Tag Leaf → Prop where
  | empty (before) : Trim .empty before
  | leaf (value) : Trim (.leaf value) (.leaf value)
  | node : TrimEdges after before → Trim (.node after) (.node before)

/-- Surviving ancestor rows retain their tag and original relative order. -/
inductive TrimEdges : List (Edge Tag Leaf) → List (Edge Tag Leaf) → Prop where
  | nil : TrimEdges [] []
  | keep : TrimForest children original → TrimEdges rest before →
      TrimEdges (.mk tag children :: rest) (.mk tag original :: before)
  | drop : TrimEdges after before → TrimEdges after (edge :: before)

/-- Trimming preserves every child position of a surviving row. -/
inductive TrimForest : List (Tree Tag Leaf) → List (Tree Tag Leaf) → Prop where
  | nil : TrimForest [] []
  | cons : Trim child original → TrimForest rest before → TrimForest (child :: rest) (original :: before)
end

mutual
/-- A trimmed occurrence has smaller weight or identical syntax. -/
theorem progress (rank : Leaf → Nat) {after before : Tree Tag Leaf} (trim : Trim after before) :
    Progress (weight rank) after before := by
  cases trim with
  | empty before =>
      cases before <;> simp [Progress, weight]
  | leaf value => exact progress_refl _ _
  | node trimmed =>
      have checked := edges_progress rank trimmed
      constructor
      · simpa only [weight, Nat.add_le_add_iff_right] using checked.1
      · intro same
        exact congrArg Tree.node (checked.2 (Nat.add_right_cancel same))

/-- Deleting a row strictly decreases its positive constructor contribution. -/
theorem edges_progress (rank : Leaf → Nat) {after before : List (Edge Tag Leaf)} (trim : TrimEdges after before) :
    Progress (edgesWeight rank) after before := by
  cases trim with
  | nil => exact progress_refl _ _
  | @keep children original rest before tag childTrim tailTrim =>
      obtain ⟨childLe, childEq⟩ := forest_progress rank childTrim
      obtain ⟨tailLe, tailEq⟩ := edges_progress rank tailTrim
      constructor
      · simp only [edgesWeight]
        omega
      · intro same
        simp only [edgesWeight] at same
        have headEqual : forestWeight rank children = forestWeight rank original := by omega
        have tailEqual : edgesWeight rank rest = edgesWeight rank before := by omega
        rw [childEq headEqual, tailEq tailEqual]
  | @drop after before edge tailTrim =>
      obtain ⟨tailLe, tailEq⟩ := edges_progress rank tailTrim
      cases edge with
      | mk tag children =>
          constructor
          · simp only [edgesWeight]
            omega
          · intro same
            simp only [edgesWeight] at same
            omega

/-- Child trimming preserves exact ordered forest syntax when weight is unchanged. -/
theorem forest_progress (rank : Leaf → Nat) {after before : List (Tree Tag Leaf)} (trim : TrimForest after before) :
    Progress (forestWeight rank) after before := by
  cases trim with
  | nil => exact progress_refl _ _
  | @cons child original rest before headTrim tailTrim =>
      obtain ⟨headLe, headEq⟩ := progress rank headTrim
      obtain ⟨tailLe, tailEq⟩ := forest_progress rank tailTrim
      constructor
      · simp only [forestWeight]
        omega
      · intro same
        simp only [forestWeight] at same
        have headEqual : weight rank child = weight rank original := by omega
        have tailEqual : forestWeight rank rest = forestWeight rank before := by omega
        rw [headEq headEqual, tailEq tailEqual]
end

mutual
/-- Removing occurrences cannot introduce a selected ancestor endpoint. -/
theorem leafAt {after before : Tree Tag Leaf} (trim : Trim after before) (path : Path)
    (endpoint : LeafAt path before) : LeafAt path after := by
  cases trim with
  | empty => trivial
  | leaf value => exact endpoint
  | node rows =>
      cases path with
      | nil => exact endpoint
      | cons index path => exact leavesAt rows index path endpoint

/-- Dropping rows preserves the leaf endpoint condition in every retained row. -/
theorem leavesAt {after before : List (Edge Tag Leaf)} (trim : TrimEdges after before)
    (index : Nat) (path : Path) (endpoint : LeavesAt index path before) : LeavesAt index path after := by
  cases trim with
  | nil => trivial
  | keep children rest => exact ⟨childAt children index path endpoint.1, leavesAt rest index path endpoint.2⟩
  | @drop after before edge rest =>
      cases edge with
      | mk tag children => exact leavesAt rest index path endpoint.2

/-- Retained child positions keep their selected leaf endpoint condition. -/
theorem childAt {after before : List (Tree Tag Leaf)} (trim : TrimForest after before)
    (index : Nat) (path : Path) (endpoint : ChildAt index path before) : ChildAt index path after := by
  cases trim with
  | nil => trivial
  | cons first rest =>
      cases index with
      | zero => exact leafAt first path endpoint
      | succ index => exact childAt rest index path endpoint
end

/-- Every admissible edit remains admissible after occurrence trimming. -/
theorem admissible {after before : Tree Tag Leaf} (trim : Trim after before)
    (edits : List (Path × Leaf)) (valid : Admissible edits before) : Admissible edits after :=
  fun path target member => leafAt trim path (valid path target member)

end MicroCFTA.EqualityLeafProjectionTrim
