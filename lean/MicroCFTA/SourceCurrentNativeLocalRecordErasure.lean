import MicroCFTA.SourceCurrentNativeRecordErasure
import MicroCFTA.InternedUnionFilterFusion

/-!
# Root erasure from the selected record alone

Only the selected union payload must reject ordinary merging. The state
can contain other union records without that additional invariant.
-/
namespace MicroCFTA.SourceCurrentNativeLocalRecordErasure
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedStoredMuOrigins
open InternedRootAlternativeLists InternedNormalizedUnionReplay
open SourceCurrentNativeCallbackErasure (eraseSelf)
open SourceCurrentRequiredUnionNormal (ValueNormal)
open InternedBinderProtocol (Reference)

/-- A bare root reference prevents the selected union payload from ordinary merging. -/
theorem root_reference (value : Value Symbol Guard) (name : Reference)
    (present : Value.reference name ∈ unionMembers value) : ValueNormal value := by
  cases value with
  | empty | reference | node | mu => trivial
  | union entry members depth free =>
      exact InternedUnionFilterFusion.ordinary_none name members present

/-- A normalized available source record replays its singleton union without effects. -/
theorem singleton [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (unions : ValueNormal value)
    (available : Available state value) : run (makeUnion [value]) state = (value, state) := by
  cases value with
  | empty | reference | node | mu => simp [makeUnion, unionMembers, distinctNodes, run]
  | union entry members depth free =>
      have stored := available.resident entry rfl
      have shape := InternedNonemptyRecords.resident_nonempty state normal.proper _ available.resident
      change 2 ≤ members.length ∧ (members.map Value.referenceOf).Nodup at shape
      have nonordinary := unions
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
    (normal : Normal state) (unions : ValueNormal value) (available : Available state value) :
    let filtered := run (withoutSelfReference name value) state
    (eraseSelf name filtered.1, filtered.2) =
      run (makeUnion (remove name (distinctNodes (unionMembers value)))) state := by
  have replay := singleton value state normal unions available
  have result := SourceCurrentNativeRootErasure.union_request name [value] state normal
    (by intro selected member; rcases List.mem_singleton.mp member with rfl; exact available)
  simpa only [replay, List.flatMap_cons, List.flatMap_nil, List.append_nil] using result

/-- Equal stripped root alternatives identify actual erased callback records in a common history. -/
theorem same [DecidableEq (EdgeKey Symbol Guard)] (firstName secondName : Reference)
    (first second : Value Symbol Guard) (left right common : State Symbol Guard)
    (ln : Normal left) (rn : Normal right) (lu : ValueNormal first) (ru : ValueNormal second)
    (li : Available left first) (ri : Available right second)
    (stripped : remove firstName (unionMembers first) = remove secondName (unionMembers second))
    (lg : Grows (run (withoutSelfReference firstName first) left).2 common)
    (rg : Grows (run (withoutSelfReference secondName second) right).2 common) :
    eraseSelf firstName (run (withoutSelfReference firstName first) left).1 =
      eraseSelf secondName (run (withoutSelfReference secondName second) right).1 := by
  have leftReplay := singleton first left ln lu li
  have rightReplay := singleton second right rn ru ri
  have result := SourceCurrentNativeRootErasure.union_same firstName secondName [first] [second]
    left right common ln rn
    (by intro selected member; rcases List.mem_singleton.mp member with rfl; exact li)
    (by intro selected member; rcases List.mem_singleton.mp member with rfl; exact ri)
    (by simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using stripped)
    (by simpa only [leftReplay] using lg) (by simpa only [rightReplay] using rg)
  simpa only [leftReplay, rightReplay] using result

end MicroCFTA.SourceCurrentNativeLocalRecordErasure
