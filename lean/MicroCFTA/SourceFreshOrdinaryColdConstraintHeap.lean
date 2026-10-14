import MicroCFTA.MergedFreshOrdinaryConstraintHeap
import MicroCFTA.SourceFreshOrdinaryColdTable
import MicroCFTA.SourceColdSharedRowsTable

/-!
# Constraint invariants at actual finite cold tables

Every repaired worklist read retains the checked edge-cache invariant.
Resident row edges then supply that invariant for each exact raw transition.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdSharedRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceColdSharedRows (Inputs ResidentRows)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open InternedFreshOrdinaryConstraintHeap (Heap)

/-- Actual shared traversal retains the source constraint invariant in its exact final cache. -/
theorem Trace.constraint_heap [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : SourceColdSharedRows.Rows Symbol Guard}
    {pending : List (Value Symbol Guard)} (trace : Trace state seen pending result final)
    (property : Guard → Prop) (semantic : SemanticHeap state) (covered : Covered [] state)
    (heap : Heap property state) (inputs : Inputs state pending) : Heap property final := by
  induction trace with
  | nil => exact heap
  | empty rest ih | known value identity edges same present rest ih =>
      exact ih semantic covered heap (fun value member => inputs value (List.mem_cons_of_mem _ member))
  | @read seen state after pending result final value identity fuel edges same absent done rest ih =>
      have own := inputs value List.mem_cons_self
      have tail : Inputs state pending := fun child member => inputs child (List.mem_cons_of_mem _ member)
      have checked := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value state semantic covered own.1 own.2
      have afterSemantic : SemanticHeap after := by simpa only [done, MergedSourceExposure.Result.state] using checked.semantic
      have afterCovered : Covered [] after := by simpa only [done, MergedSourceExposure.Result.state] using checked.covered
      have afterHeap : Heap property after := by
        simpa only [done, MergedSourceExposure.Result.state] using
          MergedFreshOrdinaryConstraintHeap.nodeEdges_heap property fuel value state semantic covered heap own.1 own.2
      have growth : Grows state after := by simpa only [done, MergedSourceExposure.Result.state] using checked.growth
      have history : Extends state.nodes.issued after.nodes.issued := by
        simpa only [done, MergedSourceExposure.Result.state] using checked.history
      have edgeResident := checked.edges edges after done
      have edgeClosed := checked.closed edges after done
      apply ih afterSemantic afterCovered afterHeap
      intro child member
      rcases List.mem_append.mp member with first | later
      · obtain ⟨edge, edgeIn, childIn⟩ := List.mem_flatMap.mp first
        exact ⟨afterSemantic.1.normal.facts.cached.edges edge.entry.key edge (edgeResident edge edgeIn) child childIn,
          edgeClosed edge edgeIn child childIn⟩
      · exact ⟨(tail child later).1.grows state after growth history, (tail child later).2⟩

/-- Every actual raw row carries a checked constraint from its resident canonical edge. -/
theorem table_constraints (property : Guard → Prop) (state : State Symbol Guard) (heap : Heap property state)
    (rows : SourceColdSharedRows.Rows Symbol Guard) (resident : ResidentRows state rows) (keys : List Nat)
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys) (root : Value Symbol Guard) :
    ∀ key edge, edge ∈ SourceInternedRows.lookup (SourceColdSharedRows.table rows keys root) key → property edge.constraint := by
  intro key edge member
  cases rootRef : SourcePreparedSharedRows.reference root with
  | none => simp [SourceColdSharedRows.table, rootRef, SourceInternedRows.lookup] at member
  | some rootIdentity =>
      simp only [SourceColdSharedRows.table, rootRef] at member
      cases key with
      | empty => rw [SourceInternedRows.table_empty] at member; cases member
      | interned identity =>
          rw [SourceInternedRows.table_lookup] at member
          by_cases declared : identity ∈ keys
          · rw [ite_eq_left declared] at member
            obtain ⟨edges, present⟩ := (domain identity).mpr declared
            simp only [SourceColdSharedRows.heap, present, Option.getD_some, List.map_map] at member
            obtain ⟨original, edgeIn, rfl⟩ := List.mem_map.mp member
            obtain ⟨_, _, _, _, residentEdges, _⟩ := resident identity edges present
            exact heap original.entry.key original (residentEdges original edgeIn)
          · rw [ite_eq_right declared] at member; cases member

end MicroCFTA.SourceFreshOrdinaryColdSharedRows
