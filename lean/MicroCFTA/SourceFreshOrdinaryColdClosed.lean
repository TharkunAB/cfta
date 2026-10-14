import MicroCFTA.MergedFreshOrdinaryExposureLive
import MicroCFTA.SourceFreshOrdinaryColdKeys

/-!
# Derived child-key closure of actual cold tables

Replayed source rows contain no empty child. Resident rows contain only
closed children. Completed traversal declares every remaining child identity.
These facts derive finite child-key closure without a NoEmptyBelow premise.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdClosed
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows ResidentRows CoveredRows)
open SourceFreshOrdinaryColdSharedRows (ReplayedRows)
open SourcePreparedSharedRows (reference encode exposure)

/-- Actual final-cache row replay derives the source empty-child normalization property. -/
theorem rows_live [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state)
    (rows : Rows Symbol Guard) (replayed : ReplayedRows state rows)
    (identity : Nat) (edges : List (EdgeValue Symbol Guard)) (present : rows identity = some edges) :
    ∀ edge ∈ edges, edge.children.any (fun child => child.referenceOf == .empty) = false := by
  obtain ⟨value, fuel, available, _, closed, read⟩ := replayed identity edges present
  simpa only [read, MergedFreshOrdinaryExposureLive.Live] using
    MergedFreshOrdinaryExposureLive.nodeEdges_live fuel value state semantic covered available closed

/-- Actual row normalization and completed child declarations derive raw finite-key closure. -/
theorem table_closed [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state)
    (rows : Rows Symbol Guard) (replayed : ReplayedRows state rows) (resident : ResidentRows state rows)
    (children : CoveredRows rows rows) (keys : List Nat)
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (root : Value Symbol Guard) : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows keys root) := by
  intro key edge member child childIn
  cases rootRef : reference root with
  | none => simp [SourceColdSharedRows.table, rootRef, SourceInternedRows.lookup] at member
  | some rootIdentity =>
      simp only [SourceColdSharedRows.table, rootRef] at member ⊢
      cases key with
      | empty => rw [SourceInternedRows.table_empty] at member; cases member
      | interned identity =>
          rw [SourceInternedRows.table_lookup] at member
          by_cases declared : identity ∈ keys
          · rw [ite_eq_left declared] at member
            obtain ⟨edges, present⟩ := (domain identity).mpr declared
            simp only [SourceColdSharedRows.heap, present, Option.getD_some, List.map_map] at member
            obtain ⟨original, edgeIn, rfl⟩ := List.mem_map.mp member
            change child ∈ (original.children.map reference).map SourceInternedRows.stateOf at childIn
            rw [List.map_map] at childIn
            obtain ⟨physical, physicalIn, rfl⟩ := List.mem_map.mp childIn
            obtain ⟨_, _, _, _, _, closedEdges⟩ := resident identity edges present
            have physicalClosed := closedEdges original edgeIn physical physicalIn
            have live := rows_live state semantic covered rows replayed identity edges present original edgeIn
            have notEmpty : physical.referenceOf ≠ .empty := by
              intro same
              have yes : original.children.any (fun child => child.referenceOf == .empty) = true :=
                List.any_eq_true.mpr ⟨physical, physicalIn, by simp only [same, beq_self_eq_true]⟩
              rw [live] at yes
              cases yes
            have nonempty : ∃ next, reference physical = some next := by
              cases physical with
              | empty => exact False.elim (notEmpty rfl)
              | reference name => simp only [Value.free] at physicalClosed; cases physicalClosed
              | node entry edges depth free | union entry members depth free | mu entry body depth ordinary => exact ⟨entry.identity, rfl⟩
            obtain ⟨next, same⟩ := nonempty
            have nextIn := (domain next).mp (children identity edges present original edgeIn physical physicalIn next same)
            rw [SourceDenseRows.mem_keys]
            simpa only [Function.comp_def, same, SourceInternedRows.stateOf] using
              (SourceInternedRows.table_keys (SourceColdSharedRows.heap rows) keys (.interned next)).mpr ⟨next, nextIn, rfl⟩
          · rw [ite_eq_right declared] at member; cases member

end MicroCFTA.SourceFreshOrdinaryColdClosed
