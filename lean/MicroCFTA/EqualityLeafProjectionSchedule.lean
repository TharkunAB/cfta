import MicroCFTA.EqualityLeafProjectionInvariant

/-!
# Fixed source schedules over projected leaf domains

Each class reads all targets from its input forest. Its edits retain the
original occurrence structure. Required paths precede the class right fold.
Empty propagation can erase roots that have no selected leaf occurrence.
-/
namespace MicroCFTA.EqualityLeafProjectionSchedule
open EqualityLeafProjectionSyntax

/-- The source keeps the first projected operand as the right-fold seed. -/
def intersectList (meet : Leaf → Leaf → Leaf) (empty : Leaf) : List Leaf → Leaf
  | [] => empty
  | first :: rest => rest.foldr meet first

/-- Every target reads the other class positions from the same original forest. -/
noncomputable def classEdits (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (paths : List Path) (before : List Node) : List (Path × Leaf) := by
  classical
  exact paths.map fun path => (path, intersectList meet empty ((paths.filter (· != path)).map (fun other => read other before)))

/-- The target calculation introduces no new editable path. -/
theorem classEdits_member (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (paths : List Path) (before : List Node)
    (path : Path) (target : Leaf) (member : (path, target) ∈ classEdits meet empty read paths before) : path ∈ paths := by
  obtain ⟨original, present, same⟩ := List.mem_map.mp member
  exact (Prod.mk.inj same).1 ▸ present

/-- One source class edits the original ordered child forest. -/
noncomputable def sourceClass (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (paths : List Path) (before : List Node) : List Node :=
  mapChildren (fun index => source.edit (descendEdits (classEdits meet empty read paths before) index)) 0 before

/-- The occurrence class computes the same targets from the canonical lowered forest. -/
noncomputable def reduceClass (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (paths : List Path) (before : List (Tree Tag Leaf)) : List (Tree Tag Leaf) :=
  editChildren meet (classEdits meet empty read paths (lowerForest source before)) 0 before

/-- Constructor-local equations derive the complete snapshot-class correspondence. -/
theorem class_lower (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (laws : ConstructorLaws source meet) (read : Path → List Node → Leaf) (paths : List Path)
    (before : List (Tree Tag Leaf)) (valid : Endpoints paths before) :
    lowerForest source (reduceClass source meet empty read paths before) =
      sourceClass source meet empty read paths (lowerForest source before) := by
  apply edit_children_lower source meet laws _ 0 before
  intro index path target present
  exact valid _ (classEdits_member meet empty read paths _ _ target (by simpa using present))

/-- Every class improves the finite occurrence forest, even when projected targets differ. -/
theorem class_progress (source : Source Tag Leaf Node) (rank : Leaf → Nat) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (leafProgress : ∀ target before, Progress rank (meet target before) before)
    (read : Path → List Node → Leaf) (paths : List Path) (before : List (Tree Tag Leaf)) :
    Progress (forestWeight rank) (reduceClass source meet empty read paths before) before :=
  edit_children_progress rank meet leafProgress _ 0 before

/-- A class retains all selected leaf-only endpoint invariants. -/
theorem class_endpoints (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (paths selected : List Path) (before : List (Tree Tag Leaf))
    (valid : Endpoints selected before) : Endpoints selected (reduceClass source meet empty read paths before) :=
  edit_endpoints meet _ selected before valid

/-- The source applies classes in its original right-fold order. -/
noncomputable def sourceSchedule (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (classes : List (List Path)) (before : List Node) : List Node :=
  classes.foldr (sourceClass source meet empty read) before

/-- The occurrence schedule uses the same class order. -/
noncomputable def schedule (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (classes : List (List Path)) (before : List (Tree Tag Leaf)) : List (Tree Tag Leaf) :=
  classes.foldr (reduceClass source meet empty read) before

/-- Every class composition preserves the finite occurrence progress relation. -/
theorem schedule_progress (source : Source Tag Leaf Node) (rank : Leaf → Nat) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (leafProgress : ∀ target before, Progress rank (meet target before) before)
    (read : Path → List Node → Leaf) (classes : List (List Path)) (before : List (Tree Tag Leaf)) :
    Progress (forestWeight rank) (schedule source meet empty read classes before) before := by
  induction classes with
  | nil => exact progress_refl _ _
  | cons paths rest ih => exact progress_trans _ _ _ _ ih (class_progress source rank meet empty leafProgress read paths _)

/-- Fixed selected endpoints remain leaf-only throughout the schedule. -/
theorem schedule_endpoints (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (classes : List (List Path)) (selected : List Path)
    (before : List (Tree Tag Leaf)) (valid : Endpoints selected before) :
    Endpoints selected (schedule source meet empty read classes before) := by
  induction classes with
  | nil => exact valid
  | cons paths rest ih => exact class_endpoints source meet empty read paths selected _ ih

/-- Class correspondence composes without a supplied whole-schedule equation. -/
theorem schedule_lower (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (laws : ConstructorLaws source meet) (read : Path → List Node → Leaf) (classes : List (List Path))
    (before : List (Tree Tag Leaf)) (valid : Endpoints classes.flatten before) :
    lowerForest source (schedule source meet empty read classes before) =
      sourceSchedule source meet empty read classes (lowerForest source before) := by
  induction classes with
  | nil => rfl
  | cons paths rest ih =>
      have tailValid : Endpoints rest.flatten before := fun path present => valid path (by simp [present])
      have headValid : Endpoints paths before := fun path present => valid path (by simp [present])
      change lowerForest source (reduceClass source meet empty read paths (schedule source meet empty read rest before)) = _
      rw [class_lower source meet empty laws read paths _ (schedule_endpoints source meet empty read rest paths before headValid), ih tailValid]
      rfl

/-- Explicit root erasure retains the original forest arity. -/
def erase (before : List (Tree Tag Leaf)) : List (Tree Tag Leaf) := before.map (fun _ => .empty)

/-- Erasing the occurrence roots lowers to the actual all-empty source forest. -/
theorem erase_lower (source : Source Tag Leaf Node) (before : List (Tree Tag Leaf)) :
    lowerForest source (erase before) = (lowerForest source before).map (fun _ => source.empty) := by
  induction before with
  | nil => rfl
  | cons child rest ih => simp only [erase, List.map_cons, lowerForest, lower]; exact congrArg (source.empty :: ·) ih

/-- Root erasure decreases every nonempty representation, including roots with no selected coordinate. -/
theorem erase_progress (rank : Leaf → Nat) (before : List (Tree Tag Leaf)) :
    Progress (forestWeight rank) (erase before) before := by
  induction before with
  | nil => exact progress_refl _ _
  | cons child rest ih =>
      have head := empty_progress rank child
      have hle := head.1
      have tle := ih.1
      refine ⟨by change weight rank .empty + forestWeight rank (erase rest) ≤ weight rank child + forestWeight rank rest; omega, fun same => ?_⟩
      change weight rank .empty + forestWeight rank (erase rest) = weight rank child + forestWeight rank rest at same
      have heq : weight rank (.empty : Tree Tag Leaf) = weight rank child := by omega
      have teq : forestWeight rank (erase rest) = forestWeight rank rest := by omega
      change .empty :: erase rest = child :: rest
      rw [head.2 heq, ih.2 teq]

/-- The source propagates any empty child to the entire forest. -/
noncomputable def sourcePropagate (source : Source Tag Leaf Node) (before : List Node) : List Node := by
  classical
  exact if source.empty ∈ before then before.map (fun _ => source.empty) else before

/-- Detect emptiness after canonical lowering, including dropped or merged ancestor rows. -/
noncomputable def propagate (source : Source Tag Leaf Node) (before : List (Tree Tag Leaf)) : List (Tree Tag Leaf) := by
  classical
  exact if source.empty ∈ lowerForest source before then erase before else before

/-- Explicit empty roots exactly model source forest-wide empty propagation. -/
theorem propagate_lower (source : Source Tag Leaf Node) (before : List (Tree Tag Leaf)) :
    lowerForest source (propagate source before) = sourcePropagate source (lowerForest source before) := by
  classical
  unfold propagate sourcePropagate
  split
  · exact erase_lower source before
  · rfl

/-- Canonical empty propagation preserves occurrence progress. -/
theorem propagate_progress (source : Source Tag Leaf Node) (rank : Leaf → Nat) (before : List (Tree Tag Leaf)) :
    Progress (forestWeight rank) (propagate source before) before := by
  unfold propagate
  split
  · exact erase_progress rank before
  · exact progress_refl _ _

/-- All fixed endpoints remain leaf-only after canonical empty propagation. -/
theorem propagate_endpoints (source : Source Tag Leaf Node) (paths : List Path) (before : List (Tree Tag Leaf))
    (valid : Endpoints paths before) : Endpoints paths (propagate source before) := by
  unfold propagate
  split
  · exact empty_endpoints paths before
  · exact valid

/-- A complete source pass preserves the skip, contradiction, require, schedule, and empty order. -/
noncomputable def sourcePass (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (skip contradiction : Bool) (classes : List (List Path)) (before : List Node) : List Node :=
  if skip then before else if contradiction then before.map (fun _ => source.empty) else
    sourcePropagate source (sourceSchedule source meet empty read classes
      (mapChildren (fun index => source.require (descend classes.flatten index)) 0 before))

/-- The lifted pass uses only original occurrences and explicit root deletion. -/
noncomputable def pass (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (skip contradiction : Bool) (classes : List (List Path))
    (before : List (Tree Tag Leaf)) : List (Tree Tag Leaf) :=
  if skip then before else if contradiction then erase before else
    propagate source (schedule source meet empty read classes (requireChildren classes.flatten 0 before))

/-- Constructor equations and the endpoint invariant derive exact complete-pass lowering. -/
theorem pass_lower (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (laws : ConstructorLaws source meet) (read : Path → List Node → Leaf) (skip contradiction : Bool)
    (classes : List (List Path)) (before : List (Tree Tag Leaf)) (valid : Endpoints classes.flatten before) :
    lowerForest source (pass source meet empty read skip contradiction classes before) =
      sourcePass source meet empty read skip contradiction classes (lowerForest source before) := by
  cases skip <;> cases contradiction
  · simp only [pass, sourcePass, Bool.false_eq_true, ↓reduceIte]
    rw [propagate_lower, schedule_lower source meet empty laws read classes _ (require_endpoints _ _ before valid),
      require_children_lower source meet laws classes.flatten 0 before]
  · exact erase_lower source before
  · rfl
  · rfl

/-- Every pass preserves its original leaf endpoint invariant. -/
theorem pass_endpoints (source : Source Tag Leaf Node) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (read : Path → List Node → Leaf) (skip contradiction : Bool) (classes : List (List Path))
    (before : List (Tree Tag Leaf)) (valid : Endpoints classes.flatten before) :
    Endpoints classes.flatten (pass source meet empty read skip contradiction classes before) := by
  cases skip <;> cases contradiction
  · exact propagate_endpoints source _ _ (schedule_endpoints source meet empty read classes _ _ (require_endpoints _ _ before valid))
  · exact empty_endpoints _ before
  · exact valid
  · exact valid

/-- A changed lifted pass strictly decreases a finite occurrence potential. -/
theorem pass_progress (source : Source Tag Leaf Node) (rank : Leaf → Nat) (meet : Leaf → Leaf → Leaf) (empty : Leaf)
    (leafProgress : ∀ target before, Progress rank (meet target before) before)
    (read : Path → List Node → Leaf) (skip contradiction : Bool) (classes : List (List Path))
    (before : List (Tree Tag Leaf)) : Progress (forestWeight rank) (pass source meet empty read skip contradiction classes before) before := by
  cases skip <;> cases contradiction
  · exact progress_trans _ _ _ _ (require_children_progress rank classes.flatten 0 before)
      (progress_trans _ _ _ _ (schedule_progress source rank meet empty leafProgress read classes _)
        (propagate_progress source rank _))
  · exact erase_progress rank before
  · exact progress_refl _ _
  · exact progress_refl _ _

end MicroCFTA.EqualityLeafProjectionSchedule
