import MicroCFTA.EqualityOrdinaryReadback
import MicroCFTA.InternedNestedFacts

/-!
# Ordinary reconstruction in any cache retaining the same complete value

The source normal form determines its exact canonical outgoing rows.
Their node key already stores the same complete value in the target cache.
The target request therefore returns without allocation or cache growth.
-/
namespace MicroCFTA.MergedNormalReadback
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency InternedNestedFacts
open EqualityOrdinaryReadback EqualityLeafProjectionPhysical

/-- Complete source residency transfers exact ordinary reconstruction without a cache-growth premise. -/
theorem normal_resident [DecidableEq (EdgeKey Symbol Guard)]
    (before after : State Symbol Guard) (beforeCoherent : Coherent before) (beforeLinked : Linked before)
    (afterCoherent : Coherent after) (value : Value Symbol Guard)
    (beforeResident : Resident before value) (afterResident : Resident after value)
    (normal : Normal before value) : Normal after value := by
  cases value with
  | empty => exact empty_normal after
  | reference | union | mu =>
      simp only [Normal, nodeEdges, makeNode, canonicalEdges, surviving,
        EnumerationBuilderCaches.canonicalIds, List.filter_nil, List.map_nil, List.eraseDups_nil,
        List.mergeSort_nil, List.filterMap_nil, run, Prod.mk.injEq, reduceCtorEq, false_and] at normal
  | node entry edges depth free =>
      have resident := resident_edges before beforeLinked (.node entry edges depth free) beforeResident
      have rows := makeNode_edges edges before beforeCoherent beforeLinked resident
      have normalized : canonicalEdges (surviving edges) = edges := by
        rw [show run (makeNode edges) before = (.node entry edges depth free, before) from normal] at rows
        exact rows.symm
      have stored : after.nodeRecords entry.key = some (.node entry edges depth free) := afterResident entry rfl
      obtain ⟨actual, present, fields⟩ := afterCoherent.nodes entry.key _ stored
      have same : entry = actual := fields.1
      have key : entry.key = .node (edges.map (fun edge => edge.entry.identity)) := fields.2.1
      have table : after.nodes.table entry.key = some entry := by simpa only [← same] using present
      cases edges with
      | nil =>
          simp only [Normal, nodeEdges, makeNode, canonicalEdges, surviving,
            EnumerationBuilderCaches.canonicalIds, List.filter_nil, List.map_nil, List.eraseDups_nil,
            List.mergeSort_nil, List.filterMap_nil, run, Prod.mk.injEq, reduceCtorEq, false_and] at normal
      | cons first rest =>
          simp only [Normal, nodeEdges, makeNode, normalized, run, nodeStep, ← key,
            Cache.intern, table, keepFirst, stored, Option.getD_some]

/-- Original availability and target coherence derive reconstruction of the same immutable value. -/
theorem normal_transfer [DecidableEq (EdgeKey Symbol Guard)]
    (before after : State Symbol Guard) (facts : Facts before) (afterCoherent : Coherent after)
    (value : Value Symbol Guard) (beforeAvailable : Available before value) (afterAvailable : Available after value)
    (normal : Normal before value) : Normal after value :=
  normal_resident before after facts.coherent facts.linked afterCoherent value
    beforeAvailable.resident afterAvailable.resident normal

end MicroCFTA.MergedNormalReadback
