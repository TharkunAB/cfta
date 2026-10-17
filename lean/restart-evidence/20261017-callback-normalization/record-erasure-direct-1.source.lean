import MicroCFTA.SourceCurrentNativeRootErasure
import MicroCFTA.SourceCurrentRequiredUnionNormal

/-!
# Root erasure for an actual returned source record

A normalized available record replays its singleton union request without
effects. Root erasure therefore uses that record's actual returned heap.
-/
namespace MicroCFTA.SourceCurrentNativeRecordErasure
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedStoredMuOrigins
open InternedRootAlternativeLists InternedNormalizedUnionReplay
open SourceCurrentNativeCallbackErasure (eraseSelf)
open SourceCurrentRequiredUnionNormal (UnionNormal)
open InternedBinderProtocol (Reference)

/-- A normalized available source record replays its singleton union without effects. -/
theorem singleton [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (unions : UnionNormal state)
    (available : Available state value) : run (makeUnion [value]) state = (value, state) := by
  cases value with
  | empty | reference | node | mu => simp [makeUnion, unionMembers, distinctNodes, run]
  | union entry members depth free =>
      have stored := available.resident entry rfl
      have shape := InternedNonemptyRecords.resident_nonempty state normal.proper _ available.resident
      have nonordinary := unions entry.key _ stored
      obtain ⟨actual, installed, fields⟩ := normal.facts.coherent.nodes entry.key _ stored
      simp only [NodeFields] at fields
      have key := fields.2.1
      have dedup := distinct_of_nodup members shape.2
      cases members with
      | nil => simp at shape
      | cons first rest =>
          cases rest with
          | nil => simp at shape
          | cons second tail =>
              simp only [makeUnion, List.flatMap_cons, List.flatMap_nil, List.append_nil, unionMembers, dedup]
              change ordinaryEdges (first :: second :: tail) = none at nonordinary
              rw [nonordinary]
              simp only [run, nodeStep, ← key, Cache.intern, installed]
              simp only [keepFirst, stored, Option.getD_some]

/-- Root filtering and bare-self erasure execute the stripped canonical request at the actual heap. -/
theorem request [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (normal : Normal state) (unions : UnionNormal state) (available : Available state value) :
    let filtered := run (withoutSelfReference name value) state
    (eraseSelf name filtered.1, filtered.2) =
      run (makeUnion (remove name (distinctNodes (unionMembers value)))) state := by
  have replay := singleton value state normal unions available
  have result := SourceCurrentNativeRootErasure.union_request name [value] state normal
    (by intro selected member; simpa only [List.mem_singleton] using member ▸ available)
  simpa only [replay, List.flatMap_cons, List.flatMap_nil, List.append_nil] using result

end MicroCFTA.SourceCurrentNativeRecordErasure
