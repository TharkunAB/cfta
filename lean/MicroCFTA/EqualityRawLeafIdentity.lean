import MicroCFTA.EqualityRawLeafConstruction
import MicroCFTA.EqualityLeafProjectionCompile

/-!
# Physical identity for finite raw leaf declarations

Two completed leaf constructions can issue different rejected requests.
Their resulting nodes agree exactly when the accepted row sets agree.
The comparison uses their actual finite common cache.
-/
namespace MicroCFTA.EqualityRawLeafIdentity
open SourceGuards FullSyntax InternedConstructorTemplates InternedRecordCoherence
open InternedFreshProbeKeys InternedEdgeResidency EqualityLeafProjectionPhysical
open EqualityRawLeafConstruction
open EqualityLeafProjectionWorkers (sequence)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- A completed finite row sequence has exact resident readback in each later cache. -/
theorem snapshot_rows [DecidableEq Symbol] (rows : List (Symbol × Guard Formula))
    (before after : State Symbol ConstraintKey) (valid : Valid before) (coherent : Coherent after)
    (growth : Grows (run (sequence (requests rows)) before).2 after) :
    (∀ edge ∈ (run (sequence (requests rows)) before).1, EdgeResident after edge) ∧
      (run (sequence (requests rows)) before).1 = rows.map (fun row => (run (request row) after).1) := by
  have repeated := replay (sequence (requests rows)) before after valid growth
  have checked := completed_rows rows after coherent
  rw [repeated] at checked
  exact checked.2

/-- Surviving physical rows retain exactly the accepted original occurrence set. -/
theorem snapshot_members [DecidableEq Symbol] (rows : List (Symbol × Guard Formula))
    (before after : State Symbol ConstraintKey) (valid : Valid before) (coherent : Coherent after)
    (growth : Grows (run (sequence (requests rows)) before).2 after) (edge : EdgeValue Symbol ConstraintKey) :
    edge ∈ surviving (run (sequence (requests rows)) before).1 ↔
      ∃ row ∈ rows, accepted row.2 = true ∧ (run (request row) after).1 = edge := by
  rw [(snapshot_rows rows before after valid coherent growth).2]
  simp only [surviving, List.mem_filter, List.mem_map, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨row, present, rfl⟩, live⟩
    change dead (run (request row) after).1 = false at live
    rw [(request_fields row after coherent).2] at live
    exact ⟨row, present, by simpa using live, rfl⟩
  · rintro ⟨row, present, admitted, rfl⟩
    refine ⟨⟨row, present, rfl⟩, ?_⟩
    change dead (run (request row) after).1 = false
    rw [(request_fields row after coherent).2, admitted]
    rfl

/-- Equal accepted raw row sets give equal complete physical nodes in a common cache. -/
theorem same_records [DecidableEq Symbol] (first second : List (Symbol × Guard Formula))
    (leftState rightState after : State Symbol ConstraintKey)
    (leftValid : Valid leftState) (rightValid : Valid rightState) (coherent : Coherent after)
    (leftGrowth : Grows (run (build first) leftState).2 after)
    (rightGrowth : Grows (run (build second) rightState).2 after)
    (same : ∀ row, (row ∈ first ∧ accepted row.2 = true) ↔ (row ∈ second ∧ accepted row.2 = true)) :
    (run (build first) leftState).1 = (run (build second) rightState).1 := by
  have left := EqualityLeafProjectionCompile.bind_completed (sequence (requests first)) makeNode
    leftState after leftValid leftGrowth
  have right := EqualityLeafProjectionCompile.bind_completed (sequence (requests second)) makeNode
    rightState after rightValid rightGrowth
  have constructors := InternedNodeSetCongruence.makeNode_same_members after coherent
    (run (sequence (requests first)) leftState).1 (run (sequence (requests second)) rightState).1
    (snapshot_rows first leftState after leftValid coherent left.1).1
    (snapshot_rows second rightState after rightValid coherent right.1).1 (by
      intro edge
      rw [snapshot_members first leftState after leftValid coherent left.1,
        snapshot_members second rightState after rightValid coherent right.1]
      constructor
      · rintro ⟨row, member, admitted, equal⟩
        have other := (same row).mp ⟨member, admitted⟩
        exact ⟨row, other.1, other.2, equal⟩
      · rintro ⟨row, member, admitted, equal⟩
        have other := (same row).mpr ⟨member, admitted⟩
        exact ⟨row, other.1, other.2, equal⟩)
  have outcomes := left.2.2.symm.trans ((congrArg (fun work => run work after) constructors).trans right.2.2)
  exact (Prod.mk.inj outcomes).1

/-- The global physical identity shortcut tests exactly the full accepted raw row set. -/
theorem identity_iff (first second : List (Fin symbols × Guard Formula))
    (leftState rightState after : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState) (coherent : Coherent after)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState)
    (leftGrowth : Grows (run (build first) leftState).2 after)
    (rightGrowth : Grows (run (build second) rightState).2 after) :
    (run (build first) leftState).1.referenceOf = (run (build second) rightState).1.referenceOf ↔
      ∀ row, (row ∈ first ∧ accepted row.2 = true) ↔ (row ∈ second ∧ accepted row.2 = true) := by
  constructor
  · intro identities row
    have values := resident_reference_injective after coherent _ _
      (resident_grows _ after leftGrowth _ (build_resident first leftState leftCoherent))
      (resident_grows _ after rightGrowth _ (build_resident second rightState rightCoherent)) identities
    rw [← build_member first leftState leftCoherent leftLinked row,
      ← build_member second rightState rightCoherent rightLinked row, values]
  · intro same
    exact congrArg Value.referenceOf (same_records first second leftState rightState after
      leftCoherent.valid rightCoherent.valid coherent leftGrowth rightGrowth same)

/-- The raw progress carrier reads the exact admitted finite declaration set. -/
def denote (rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial)) :
    NoncanonicalLeafProgress.Node (SourceNoncanonicalLeafProgress.Raw initial) symbols :=
  fun symbol row => (symbol, row) ∈ rows ∧ accepted row.val = true

/-- Atom certificates add no identity distinction to physical source declarations. -/
theorem declarations_iff (first second : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial)) :
    (∀ row, (row ∈ declarations first ∧ accepted row.2 = true) ↔
      (row ∈ declarations second ∧ accepted row.2 = true)) ↔ denote first = denote second := by
  constructor
  · intro same
    funext symbol row
    apply propext
    constructor <;> rintro ⟨member, admitted⟩
    · obtain ⟨other, accepted⟩ := (same (symbol, row.val)).mp
        ⟨List.mem_map.mpr ⟨(symbol, row), member, rfl⟩, admitted⟩
      obtain ⟨⟨actual, original⟩, present, equal⟩ := List.mem_map.mp other
      obtain ⟨rfl, guards⟩ := Prod.mk.inj equal
      have rows : original = row := Subtype.ext guards
      exact ⟨rows ▸ present, accepted⟩
    · obtain ⟨other, accepted⟩ := (same (symbol, row.val)).mpr
        ⟨List.mem_map.mpr ⟨(symbol, row), member, rfl⟩, admitted⟩
      obtain ⟨⟨actual, original⟩, present, equal⟩ := List.mem_map.mp other
      obtain ⟨rfl, guards⟩ := Prod.mk.inj equal
      have rows : original = row := Subtype.ext guards
      exact ⟨rows ▸ present, accepted⟩
  · intro same row
    constructor <;> rintro ⟨member, admitted⟩
    · obtain ⟨⟨symbol, original⟩, present, rfl⟩ := List.mem_map.mp member
      have other : denote second symbol original := same ▸ (show denote first symbol original from ⟨present, admitted⟩)
      exact ⟨List.mem_map.mpr ⟨(symbol, original), other.1, rfl⟩, other.2⟩
    · obtain ⟨⟨symbol, original⟩, present, rfl⟩ := List.mem_map.mp member
      have other : denote first symbol original := same.symm ▸ (show denote second symbol original from ⟨present, admitted⟩)
      exact ⟨List.mem_map.mpr ⟨(symbol, original), other.1, rfl⟩, other.2⟩

/-- The physical whole-node shortcut agrees with equality of raw progress states. -/
theorem raw_identity_iff (first second : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (leftState rightState after : State (Fin symbols) ConstraintKey)
    (leftCoherent : Coherent leftState) (rightCoherent : Coherent rightState) (coherent : Coherent after)
    (leftLinked : Linked leftState) (rightLinked : Linked rightState)
    (leftGrowth : Grows (run (build (declarations first)) leftState).2 after)
    (rightGrowth : Grows (run (build (declarations second)) rightState).2 after) :
    (run (build (declarations first)) leftState).1.referenceOf =
      (run (build (declarations second)) rightState).1.referenceOf ↔ denote first = denote second :=
  (identity_iff _ _ leftState rightState after leftCoherent rightCoherent coherent leftLinked rightLinked
    leftGrowth rightGrowth).trans (declarations_iff first second)

end MicroCFTA.EqualityRawLeafIdentity
