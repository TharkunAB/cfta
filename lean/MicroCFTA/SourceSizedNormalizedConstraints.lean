import MicroCFTA.SourceSizedFiniteKeysNormalized
import MicroCFTA.SourceFreshOrdinaryColdConstraintHeap
import MicroCFTA.SourceFreshOrdinaryColdValidated

/-!
# Original constraints after actual normalized cold readback

Raw map normalization preserves complete lookup lists. The source edge
invariant therefore reaches every normalized cold transition through actual
construction and traversal. No rowwise annotation certificate is supplied.
-/
namespace MicroCFTA.SourceSizedFiniteKeys

/-- Map normalization preserves the complete raw alternative list, including every annotation. -/
theorem normalized_lookup [DecidableEq State] [Ord State]
    (table : Table State Symbol Payload) (state : State) : lookup (normalized table) state = lookup table state := by
  unfold normalized lookup
  simp only [List.flatMap_map]
  rw [SourceFromTerms.select_unique _ ((List.mergeSort_perm _ _).nodup_iff.mpr (DistinctRank.distinct_nodup _))]
  by_cases present : state ∈ table.map Prod.fst
  · simp [DistinctRank.mem_distinct, present]
  · simp only [List.mem_mergeSort, DistinctRank.mem_distinct, present, ite_false]
    symm
    apply List.flatMap_eq_nil_iff.mpr
    intro entry member
    have different : entry.1 ≠ state := fun same => present (List.mem_map.mpr ⟨entry, member, same⟩)
    simp [different]

end MicroCFTA.SourceSizedFiniteKeys

namespace MicroCFTA.SourceFreshOrdinaryColdSharedRows
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows Inputs ResidentRows sizedTable table)

/-- Actual traversal derives the original edge invariant on every normalized raw query row. -/
theorem Trace.normalized_constraints [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final)
    (semantic : SemanticHeap state) (covered : Covered [] state)
    (available : Available state value) (closed : value.free = [])
    (property : Guard → Prop) (heap : InternedFreshOrdinaryConstraintHeap.Heap property state)
    (keys : List Nat) (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys) :
    ∀ key row, row ∈ SourceSizedFiniteKeys.lookup (SourceSizedFiniteKeys.normalized (sizedTable (table rows keys value))) key →
      property row.constraint := by
  have inputs : Inputs state [value] := by
    intro child member
    simpa only [List.mem_singleton.mp member] using And.intro available closed
  have noRows : ResidentRows state (fun _ => none) := by intro identity edges absent; cases absent
  obtain ⟨_, _, _, _, _, resident⟩ := trace.correct semantic covered inputs noRows
  have finalHeap := trace.constraint_heap property semantic covered heap inputs
  have invariant := table_constraints property final finalHeap rows resident keys domain value
  intro key row member
  rw [SourceSizedFiniteKeys.normalized_lookup, SourceColdSharedRows.sized_lookup] at member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact invariant key original present

end MicroCFTA.SourceFreshOrdinaryColdSharedRows
