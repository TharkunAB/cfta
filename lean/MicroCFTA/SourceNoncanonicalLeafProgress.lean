import MicroCFTA.NoncanonicalLeafProgress
import MicroCFTA.EqualityLeafProjectionAdmittedSource

/-!
# Source guard normalization with arbitrary initial outer syntax

Initial guards can contain redundant And and Top constructors. Exact
source conjunction canonicalizes a Cartesian result. Constructor checks
can then remove literal Bottom or invalid positive equality rows.
-/
namespace MicroCFTA.SourceNoncanonicalLeafProgress
open SourceGuards FullSyntax GuardConjunction FiniteRowIntersection

/-- A raw source row uses the original finite outer atom inventory. -/
def Raw (initial : List (Guard Formula)) :=
  {guard : Guard Formula // ∀ atom ∈ atoms guard, atom ∈ SourceLeafRowProgress.basis initial}

/-- Normalize the guard without applying the edge constructor's rejection checks. -/
def normalizeRow (row : Raw initial) : SourceLeafRowProgress.Row initial :=
  ⟨normalize GuardStructuralOrder.le row.val,
    normalize_idempotent GuardStructuralOrder.le GuardStructuralOrder.le_trans
      GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm row.val,
    fun atom present => row.property atom
      ((canonical_mem _ _ _).mp (by simpa only [atoms_normalize] using present))⟩

/-- Canonical rows retain their exact guard in the source representation. -/
def embed (row : SourceLeafRowProgress.Row initial) : Raw initial := ⟨row.val, row.property.2⟩

/-- Canonical row normalization is a retraction. -/
theorem retraction (row : SourceLeafRowProgress.Row initial) : normalizeRow (embed row) = row :=
  Subtype.ext row.property.1

/-- Outer source conjunction depends on the flattened atom sets of both operands. -/
theorem merge_normalized (first second : Guard Formula) :
    merge GuardStructuralOrder.le (normalize GuardStructuralOrder.le first) (normalize GuardStructuralOrder.le second) =
      merge GuardStructuralOrder.le first second := by
  apply normalize_eq GuardStructuralOrder.le GuardStructuralOrder.le_trans
    GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm
  intro atom
  simp only [atoms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    atoms_normalize, canonical_mem]

/-- The actual source guard operation retains exactly the union of input atoms. -/
def rawJoin (first second : Raw initial) : Raw initial :=
  ⟨merge GuardStructuralOrder.le first.val second.val,
    fun atom member => ((merge_mem _ _ _ _).mp member).elim (first.property atom) (second.property atom)⟩

/-- The raw source operation is the canonical row product after normalization of its factors. -/
theorem rawJoin_exact (first second : Raw initial) :
    rawJoin first second = embed ((SourceLeafRowProgress.algebra initial).join (normalizeRow first) (normalizeRow second)) :=
  Subtype.ext (merge_normalized first.val second.val).symm

/-- Literal contradiction and actual source equality arity checking decide row admission. -/
def Admitted (row : SourceLeafRowProgress.Row initial) : Prop :=
  row.val ≠ .bottom ∧ EqualityLeafProjectionAdmittedSource.fitsLeaf
    (SourceCompactGuards.sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) row.val)) = true

/-- Copy the source nullary Cartesian branch, including its complete residual guard and rejection checks. -/
def product (first second : NoncanonicalLeafProgress.Node (Raw initial) symbols) :
    NoncanonicalLeafProgress.Node (Raw initial) symbols := fun symbol row =>
  ∃ left right, first symbol left ∧ second symbol right ∧ rawJoin left right = row ∧ row.val ≠ .bottom ∧
    EqualityLeafProjectionAdmittedSource.fitsLeaf
      (SourceCompactGuards.sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) row.val)) = true

/-- Every source Cartesian result is the filtered canonical product used by the progress proof. -/
theorem product_exact (first second : NoncanonicalLeafProgress.Node (Raw initial) symbols) :
    product first second = NoncanonicalLeafProgress.product (SourceLeafRowProgress.algebra initial)
      normalizeRow embed Admitted first second := by
  funext symbol row
  apply propext
  constructor
  · rintro ⟨left, right, firstPresent, secondPresent, rfl, survives, fits⟩
    let combined := (SourceLeafRowProgress.algebra initial).join (normalizeRow left) (normalizeRow right)
    have same : rawJoin left right = embed combined := rawJoin_exact left right
    refine ⟨combined, ⟨⟨normalizeRow left, normalizeRow right,
      ⟨left, firstPresent, rfl⟩, ⟨right, secondPresent, rfl⟩, rfl⟩, ?_⟩, same.symm⟩
    change (embed combined).val ≠ .bottom ∧ EqualityLeafProjectionAdmittedSource.fitsLeaf
      (SourceCompactGuards.sourceEqualities (SourceSymbolicIndex.Constraint.mk (some []) (embed combined).val)) = true
    rw [← same]
    exact ⟨survives, fits⟩
  · rintro ⟨combined, ⟨⟨a, b, ⟨left, firstPresent, rfl⟩, ⟨right, secondPresent, rfl⟩, rfl⟩, admitted⟩, rfl⟩
    exact ⟨left, right, firstPresent, secondPresent, rawJoin_exact left right, admitted⟩

/-- The source compares the complete node before it enters the Cartesian branch. -/
noncomputable def intersect (first second : NoncanonicalLeafProgress.Node (Raw initial) symbols) :
    NoncanonicalLeafProgress.Node (Raw initial) symbols := by
  classical
  exact if first = second then first else product first second

/-- Both source intersection branches agree with the normalization-phase model. -/
theorem intersect_exact (first second : NoncanonicalLeafProgress.Node (Raw initial) symbols) :
    intersect first second = NoncanonicalLeafProgress.intersect (SourceLeafRowProgress.algebra initial)
      normalizeRow embed Admitted first second := by
  classical
  simp only [intersect, NoncanonicalLeafProgress.intersect, product_exact]

/-- Derive the phase and finite canonical potential from the actual original guard atoms. -/
noncomputable def rank (node : NoncanonicalLeafProgress.Node (Raw initial) symbols) : Nat :=
  NoncanonicalLeafProgress.rank (SourceLeafRowProgress.algebra initial) (SourceLeafRowProgress.inventory initial)
    normalizeRow embed Admitted node

/-- Every changed source nullary intersection decreases a derived natural rank, even for raw initial guards. -/
theorem intersect_strict (first second : NoncanonicalLeafProgress.Node (Raw initial) symbols)
    (changed : intersect first second ≠ first) : rank (intersect first second) < rank first := by
  rw [intersect_exact] at changed ⊢
  exact NoncanonicalLeafProgress.intersect_strict (SourceLeafRowProgress.algebra initial)
    (SourceLeafRowProgress.inventory initial) (SourceLeafRowProgress.inventory_complete initial)
    normalizeRow embed retraction Admitted first second changed

/-- A self-intersection preserves the original guard representation without forced normalization. -/
theorem self (node : NoncanonicalLeafProgress.Node (Raw initial) symbols) : intersect node node = node := by
  classical
  simp [intersect]

/-- Source structural conjunction keeps operand order irrelevant for the complete raw row. -/
theorem rawJoin_comm (first second : Raw initial) : rawJoin first second = rawJoin second first :=
  Subtype.ext (merge_commutative GuardStructuralOrder.le GuardStructuralOrder.le_trans
    GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm first.val second.val)

/-- Source Cartesian filtering uses the same completed row in either operand order. -/
theorem product_comm (first second : NoncanonicalLeafProgress.Node (Raw initial) symbols) :
    product first second = product second first := by
  funext symbol row
  apply propext
  constructor <;> rintro ⟨left, right, foundLeft, foundRight, equal, admitted⟩
  · exact ⟨right, left, foundRight, foundLeft, (rawJoin_comm right left).trans equal, admitted⟩
  · exact ⟨right, left, foundRight, foundLeft, (rawJoin_comm right left).trans equal, admitted⟩

/-- The copied source whole-node operation is commutative, including raw self returns. -/
theorem intersect_comm (first second : NoncanonicalLeafProgress.Node (Raw initial) symbols) :
    intersect first second = intersect second first := by
  classical
  by_cases same : first = second
  · subst second; rfl
  · simp only [intersect, same, Ne.symm same, ↓reduceIte, product_comm first second]

/-- Projected edits obtain the local progress law without canonical initial-guard assumptions. -/
theorem leaf_progress (target before : NoncanonicalLeafProgress.Node (Raw initial) symbols) :
    EqualityLeafProjectionSyntax.Progress rank (intersect target before) before := by
  classical
  by_cases same : intersect target before = before
  · exact ⟨by simp only [same, Nat.le_refl], fun _ => same⟩
  · have strict := intersect_strict before target (by simpa only [intersect_comm before target] using same)
    rw [intersect_comm before target] at strict
    exact ⟨Nat.le_of_lt strict, fun equal => False.elim (Nat.ne_of_lt strict equal)⟩

/-- Retained occurrence-tree schedules inherit the bound for arbitrary original guard syntax. -/
theorem projected_terminates (initial : List (Guard Formula))
    (source : EqualityLeafProjectionSyntax.Source Tag (NoncanonicalLeafProgress.Node (Raw initial) symbols) Node)
    (laws : EqualityLeafProjectionSyntax.ConstructorLaws source intersect)
    (read : EqualityLeafProjectionSyntax.Path → List Node → NoncanonicalLeafProgress.Node (Raw initial) symbols)
    (skip contradiction : Bool) (classes : List (List EqualityLeafProjectionSyntax.Path))
    (before : List (EqualityLeafProjectionSyntax.Tree Tag (NoncanonicalLeafProgress.Node (Raw initial) symbols)))
    (valid : EqualityLeafProjectionSyntax.Endpoints classes.flatten before) :
    ∃ fuel result, EqualityLeafProjectionSchedule.sourceRun source intersect (fun _ _ => False)
        read skip contradiction classes fuel (EqualityLeafProjectionSyntax.lowerForest source before) = some result ∧
      EqualityLeafProjectionSchedule.sourcePass source intersect (fun _ _ => False) read skip contradiction classes result = result ∧
      fuel ≤ EqualityLeafProjectionSyntax.forestWeight rank before + 1 :=
  EqualityLeafProjectionSchedule.source_terminates source rank intersect (fun _ _ => False) laws
    leaf_progress read skip contradiction classes before valid

end MicroCFTA.SourceNoncanonicalLeafProgress
