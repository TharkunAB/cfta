import MicroCFTA.SourceSizedConjunctionPreparation

/-!
# Child-state sharing in actual conjunction rows

Every position in a joined equality group receives the same conjunction
key. Removing singleton groups and regrouping the retained classes preserve
this property. Actual preparation and decorated sorting retain it.

The grouped index can therefore read one child state for each group. These
laws derive the property from the computed rows. No caller supplies a child
layout or a completed conjunction worker.
-/
namespace MicroCFTA.SourceSizedConjunctionSharing
open SourceSizedDecided SourceSizedFiniteKeys SourceSizedConjunctionWorklist

variable {State Symbol Formula : Type}

/-- Every position in a current equality group reads the same child state. -/
def Shared (row : Row State Symbol (List (List Nat))) : Prop :=
  CompactGroups.GroupsEqual (fun index => row.children[index]?)
    (CompactGroups.childGroups row.children.length row.constraint)

section Rows
variable [DecidableEq State] [Ord State]

/-- Each original joined group reads its one assigned conjunction key. -/
theorem intersection_joined (first : Row State Symbol (List (List Nat)))
    (others : List (Row State Symbol (List (List Nat)))) :
    CompactGroups.GroupsEqual
      (fun index => (SourceSizedConjunctionRows.intersection first others).children[index]?)
      (CompactGroups.childGroups first.children.length
        ((first :: others).flatMap fun row => row.constraint)) := by
  intro group groupIn left leftIn right rightIn
  change (SourceSizedConjunctionPositions.children (first :: others) first.children.length)[left]? =
    (SourceSizedConjunctionPositions.children (first :: others) first.children.length)[right]?
  rw [SourceSizedConjunctionPositions.child_at _ _ group groupIn left leftIn,
    SourceSizedConjunctionPositions.child_at _ _ group groupIn right rightIn]

/-- Regrouping the actual retained classes preserves the assigned child-state sharing. -/
theorem intersection_shared (first : Row State Symbol (List (List Nat)))
    (others : List (Row State Symbol (List (List Nat)))) :
    Shared (SourceSizedConjunctionRows.intersection first others) := by
  let row := SourceSizedConjunctionRows.intersection first others
  have equalities : CompactGroups.GroupsEqual (fun index => row.children[index]?) row.constraint :=
    (SourceSizedEqualChildren.classesOf_exact _ _).mpr (intersection_joined first others)
  exact (CompactGroups.childGroups_exact _ _ _
    (SourceSizedConjunctionRows.intersection_bounded first others)).mpr equalities

variable [DecidableEq Symbol]

/-- Actual conjunction row enumeration emits only bounded equality positions. -/
theorem rows_bounded (lookup : State → List (Row State Symbol (List (List Nat))))
    (key : List State) (row : Row (List State) Symbol (List (List Nat)))
    (member : row ∈ SourceSizedConjunctionRows.rows lookup key) :
    CompactGroups.ValidClasses row.children.length row.constraint := by
  obtain ⟨first, others, _, rfl⟩ := (SourceSizedConjunctionRows.mem_rows lookup key row).mp member
  exact SourceSizedConjunctionRows.intersection_bounded first others

/-- Every row chosen by the actual tuple enumeration shares each grouped child state. -/
theorem rows_shared (lookup : State → List (Row State Symbol (List (List Nat))))
    (key : List State) (row : Row (List State) Symbol (List (List Nat)))
    (member : row ∈ SourceSizedConjunctionRows.rows lookup key) : Shared row := by
  obtain ⟨first, others, _, rfl⟩ := (SourceSizedConjunctionRows.mem_rows lookup key row).mp member
  exact intersection_shared first others

private theorem prepared_row (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned)
    (key : List State) (row : Row (List State) Symbol (List (List Nat)))
    (member : row ∈ lookup returned key) :
    ∃ owner, row ∈ SourceSizedConjunctionRows.rows (lookup classified) owner := by
  obtain ⟨entry, entryIn, selected⟩ := List.mem_flatMap.mp member
  have rowIn : row ∈ entry.2 := by
    split at selected
    · exact selected
    · cases selected
  exact ⟨entry.1, (prepare_ready classified root returned success).rowReadback entry entryIn ▸ rowIn⟩

/-- Successful exploration derives both grouped-index prerequisites for every returned row. -/
theorem prepared_facts (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned)
    (key : List State) (row : Row (List State) Symbol (List (List Nat)))
    (member : row ∈ lookup returned key) :
    CompactGroups.ValidClasses row.children.length row.constraint ∧ Shared row := by
  obtain ⟨owner, actual⟩ := prepared_row classified root returned success key row member
  exact ⟨rows_bounded _ owner row actual, rows_shared _ owner row actual⟩

end Rows

section Sorted
variable [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol] [Ord Symbol]

/-- The actual decorated sort preserves both grouped-index prerequisites. -/
theorem sorted_facts (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned)
    (key : List State) (row : Row (List State) Symbol (List (List Nat)))
    (member : row ∈ SourceSizedConjunctionSorted.sortedRows classified root returned success key) :
    CompactGroups.ValidClasses row.children.length row.constraint ∧ Shared row :=
  prepared_facts classified root returned success key row
    ((SourceSizedConjunctionSorted.sorted_permutation classified root returned success key).mem_iff.mp member)

/-- Exact final lookup retains the sharing and position bounds computed by exploration. -/
theorem sorted_table_facts (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned)
    (key : List State) (row : Row (List State) Symbol (List (List Nat)))
    (member : row ∈ lookup (SourceSizedConjunctionSorted.sortedTable classified root returned success) key) :
    CompactGroups.ValidClasses row.children.length row.constraint ∧ Shared row := by
  rw [SourceSizedConjunctionSorted.sortedTable_lookup] at member
  exact sorted_facts classified root returned success key row member

/-- The complete computed preparation supplies the grouped-index prerequisites without a layout premise. -/
theorem preparation_facts (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (row : Row (List State) Symbol (List (List Nat)))
    (member : row ∈ lookup output key) :
    CompactGroups.ValidClasses row.children.length row.constraint ∧ Shared row := by
  obtain ⟨classified, _, returned, ready, same⟩ :=
    SourceSizedConjunctionPreparation.success_origin original root output success
  rw [same] at member
  exact sorted_table_facts classified root returned ready key row member

end Sorted
end MicroCFTA.SourceSizedConjunctionSharing
