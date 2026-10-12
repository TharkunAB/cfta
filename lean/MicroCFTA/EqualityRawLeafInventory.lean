import MicroCFTA.EqualityRawLeafAvailability

/-!
# Finite reachable raw leaf alternatives

The source retains initial guard syntax until a Cartesian intersection.
Later conjunctions are canonical. Thus the finite inventory consists of
the original raw guards and the generated canonical guards, with the actual
constructor admission check applied to both parts.
-/
namespace MicroCFTA.EqualityRawLeafInventory
open SourceGuards FullSyntax GuardConjunction
open SourceNoncanonicalLeafProgress (Raw)
open EqualityRawLeafConstruction (accepted)

/-- Each reachable residual is original raw syntax or a canonical source conjunction. -/
def Reachable (row : Raw initial) : Prop :=
  row.val ∈ initial ∨ normalize GuardStructuralOrder.le row.val = row.val

/-- Retain an initial guard with its exact source syntax and derived atom support. -/
def original (initial : List (Guard Formula)) (guard : Guard Formula) (member : guard ∈ initial) : Raw initial :=
  ⟨guard, fun _ present => List.mem_flatMap.mpr ⟨guard, member, present⟩⟩

/-- Enumerate initial syntax and every later canonical conjunction before constructor admission. -/
def candidates (initial : List (Guard Formula)) : List (Raw initial) :=
  initial.attach.map (fun guard => original initial guard.val guard.property) ++
    (SourceLeafRowProgress.inventory initial).map SourceNoncanonicalLeafProgress.embed

/-- The raw phase adds only the original finite number of guard occurrences. -/
theorem candidates_length (initial : List (Guard Formula)) :
    (candidates initial).length = initial.length + 2 ^ (SourceLeafRowProgress.basis initial).length := by
  simp only [candidates, List.length_append, List.length_map, List.length_attach, SourceLeafRowProgress.inventory_length]

/-- The derived candidate inventory contains every reachable raw residual. -/
theorem candidates_complete (row : Raw initial) (reachable : Reachable row) : row ∈ candidates initial := by
  rcases reachable with originalRow | canonical
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨⟨row.val, originalRow⟩, List.mem_attach _ _, Subtype.ext rfl⟩
  · apply List.mem_append_right
    let canonicalRow : SourceLeafRowProgress.Row initial := ⟨row.val, canonical, row.property⟩
    exact List.mem_map.mpr ⟨canonicalRow, SourceLeafRowProgress.inventory_complete initial canonicalRow, Subtype.ext rfl⟩

/-- Only source-admitted reachable alternatives occur in the finite leaf carrier. -/
def Row (initial : List (Guard Formula)) := {row : Raw initial // Reachable row ∧ accepted row.val = true}

/-- Apply the exact constructor check to the finite original-and-canonical candidates. -/
noncomputable def inventory (initial : List (Guard Formula)) : List (Row initial) := by
  classical
  exact (candidates initial).filterMap fun row =>
    if admitted : Reachable row ∧ accepted row.val = true then some ⟨row, admitted⟩ else none

/-- The physical row carrier has an explicit generated finite inventory. -/
theorem inventory_complete (row : Row initial) : row ∈ inventory initial := by
  unfold inventory
  apply List.mem_filterMap.mpr
  refine ⟨row.val, candidates_complete row.val row.property.1, ?_⟩
  rw [dite_eq_left row.property]
  exact congrArg some (Subtype.ext rfl)

/-- Source admission cannot enlarge the original-and-canonical inventory. -/
theorem inventory_bound (initial : List (Guard Formula)) :
    (inventory initial).length ≤ initial.length + 2 ^ (SourceLeafRowProgress.basis initial).length := by
  rw [← candidates_length initial]
  exact List.length_filterMap_le _ _

/-- A raw source Cartesian result is canonical, even when either initial operand is not. -/
theorem joined_reachable (first second : Raw initial) :
    Reachable (SourceNoncanonicalLeafProgress.rawJoin first second) := by
  right
  exact normalize_idempotent GuardStructuralOrder.le GuardStructuralOrder.le_trans
    GuardStructuralOrder.le_total GuardStructuralOrder.le_antisymm _

/-- Constructor symbols index independent row sets; physical identity compares the complete function. -/
abbrev Leaf (initial : List (Guard Formula)) (symbols : Nat) := Fin symbols → Row initial → Prop

/-- Interpret finite admitted alternatives in the raw normalization-phase carrier. -/
def interpret (leaf : Leaf initial symbols) : NoncanonicalLeafProgress.Node (Raw initial) symbols :=
  fun symbol raw => ∃ row, leaf symbol row ∧ row.val = raw

/-- The interpretation retains every finite row without adding an identity quotient. -/
theorem interpret_row (leaf : Leaf initial symbols) (symbol : Fin symbols) (row : Row initial) :
    interpret leaf symbol row.val ↔ leaf symbol row := by
  constructor
  · rintro ⟨other, present, same⟩
    exact (Subtype.ext same : other = row) ▸ present
  · exact fun present => ⟨row, present, rfl⟩

/-- Every interpreted raw row is reachable and passes the actual source edge check. -/
theorem interpret_valid (leaf : Leaf initial symbols) (symbol : Fin symbols) (raw : Raw initial)
    (member : interpret leaf symbol raw) : Reachable raw ∧ accepted raw.val = true := by
  obtain ⟨row, _, rfl⟩ := member
  exact row.property

/-- Equal raw interpretations determine the complete finite source predicates. -/
theorem interpret_injective (first second : Leaf initial symbols)
    (same : interpret first = interpret second) : first = second := by
  funext symbol row
  apply propext
  rw [← interpret_row first symbol row, ← interpret_row second symbol row, same]

/-- Restrict the exact source raw operation to the finite admitted carrier. -/
noncomputable def intersect (first second : Leaf initial symbols) : Leaf initial symbols :=
  fun symbol row => SourceNoncanonicalLeafProgress.intersect (interpret first) (interpret second) symbol row.val

/-- The source operation derives the finite-carrier invariant in both branches. -/
theorem intersect_valid (first second : Leaf initial symbols) (symbol : Fin symbols) (raw : Raw initial)
    (member : SourceNoncanonicalLeafProgress.intersect (interpret first) (interpret second) symbol raw) :
    Reachable raw ∧ accepted raw.val = true := by
  unfold SourceNoncanonicalLeafProgress.intersect at member
  split at member
  · exact interpret_valid first symbol raw member
  · obtain ⟨left, right, _, _, rfl, admitted⟩ := member
    exact ⟨joined_reachable left right, (EqualityRawLeafConstruction.accepted_iff _).mpr admitted⟩

/-- The finite carrier loses no source alternative and adds no canonicalization step. -/
theorem intersect_exact (first second : Leaf initial symbols) :
    interpret (intersect first second) = SourceNoncanonicalLeafProgress.intersect (interpret first) (interpret second) := by
  funext symbol raw
  apply propext
  constructor
  · rintro ⟨row, member, rfl⟩
    exact member
  · intro member
    exact ⟨⟨raw, intersect_valid first second symbol raw member⟩, member, rfl⟩

/-- Enumerate a selected finite predicate in a fixed source declaration order. -/
noncomputable def choices (leaf : Leaf initial symbols) : List (Fin symbols × Row initial) := by
  classical
  exact (List.ofFn id).flatMap fun symbol =>
    ((inventory initial).filter (fun row => decide (leaf symbol row))).map (symbol, ·)

/-- Finite choices represent exactly the selected leaf predicate. -/
theorem choices_member (leaf : Leaf initial symbols) (symbol : Fin symbols) (row : Row initial) :
    (symbol, row) ∈ choices leaf ↔ leaf symbol row := by
  classical
  simp only [choices, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨actual, _, original, ⟨_, member⟩, same⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact member
  · intro member
    exact ⟨symbol, by simp, row, ⟨inventory_complete row, member⟩, rfl⟩

/-- Supply the exact raw syntax to the physical constructor. -/
noncomputable def rawChoices (leaf : Leaf initial symbols) : List (Fin symbols × Raw initial) :=
  (choices leaf).map fun (symbol, row) => (symbol, row.val)

/-- The finite physical declarations decode to the raw progress interpretation. -/
theorem choices_exact (leaf : Leaf initial symbols) : EqualityRawLeafIdentity.denote (rawChoices leaf) = interpret leaf := by
  funext symbol raw
  apply propext
  constructor
  · rintro ⟨member, _⟩
    obtain ⟨⟨actual, row⟩, present, same⟩ := List.mem_map.mp member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact ⟨row, (choices_member leaf actual row).mp present, rfl⟩
  · rintro ⟨row, member, rfl⟩
    exact ⟨List.mem_map.mpr ⟨(symbol, row), (choices_member leaf symbol row).mpr member, rfl⟩, row.property.2⟩

/-- The finite raw leaf measure comes from the actual source normalization phase. -/
noncomputable def rank (leaf : Leaf initial symbols) : Nat := SourceNoncanonicalLeafProgress.rank (interpret leaf)

/-- The finite exact raw carrier supplies the projected worker's local progress law. -/
theorem leaf_progress (target before : Leaf initial symbols) :
    EqualityLeafProjectionSyntax.Progress rank (intersect target before) before := by
  have progress := SourceNoncanonicalLeafProgress.leaf_progress (interpret target) (interpret before)
  rw [← intersect_exact] at progress
  exact ⟨progress.1, fun same => interpret_injective _ _ (progress.2 same)⟩

end MicroCFTA.EqualityRawLeafInventory
