import MicroCFTA.EqualityIndex

/-!
# Canonical identity of the source equality partition

The source array worker and the reference completion use different schedules.
This module relates their complete connected partitions, including path names
and canonical class order.
-/
namespace MicroCFTA.EqualityIndex
open EqualityNormalize

/-- One representative bucket in the source map readback. -/
def bucket (entries : List (Nat × Nat)) (root : Nat) : List Nat :=
  (entries.filter fun entry => entry.1 == root).map Prod.snd

/-- Every bucket entry comes from exactly its recorded root/member pair. -/
theorem bucket_exact (entries : List (Nat × Nat)) (root index : Nat) :
    index ∈ bucket entries root ↔ (root, index) ∈ entries := by
  simp only [bucket, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨key, value⟩, ⟨member, same⟩, equal⟩
    dsimp only at same equal
    subst key; subst value; exact member
  · intro member; exact ⟨(root, index), ⟨member, rfl⟩, rfl⟩

/-- Each output index group is one bucket of a root that actually occurs. -/
theorem group_named (entries : List (Nat × Nat)) (group : List Nat) (member : group ∈ EqualityArray.groups entries) :
    ∃ root ∈ entries.map Prod.fst, group = bucket entries root := by
  obtain ⟨root, present, same⟩ := List.mem_map.mp member
  exact ⟨root, by simpa using present, same.symm⟩

/-- Original path connectivity becomes the exact indexed class connectivity. -/
theorem encode_connected (classes : Constraints) (left right : Path) (connected : Connected classes left right) :
    EqualityArray.Connected (encoded classes) (encode classes left) (encode classes right) := by
  induction connected with
  | edge paths present leftMember rightMember =>
      exact .related (paths.map (encode classes)) (List.mem_map.mpr ⟨paths, present, rfl⟩) _ _
        (List.mem_map.mpr ⟨_, leftMember, rfl⟩) (List.mem_map.mpr ⟨_, rightMember, rfl⟩)
  | trans _ _ first second => exact .trans first second

/-- Indexed connectivity cannot introduce a connection between unrelated paths. -/
theorem decode_connected (classes : Constraints) (left right : Nat)
    (connected : EqualityArray.Connected (encoded classes) left right)
    (leftBound : left < (members classes).length) (rightBound : right < (members classes).length) :
    Connected classes (decode classes left) (decode classes right) := by
  induction connected with
  | refl index =>
      obtain ⟨paths, present, member⟩ := List.mem_flatten.mp (decode_member classes index leftBound)
      exact .edge paths present member member
  | related indices present left right leftMember rightMember =>
      obtain ⟨paths, pathsMember, rfl⟩ := List.mem_map.mp present
      obtain ⟨first, firstMember, rfl⟩ := List.mem_map.mp leftMember
      obtain ⟨second, secondMember, rfl⟩ := List.mem_map.mp rightMember
      rw [decode_encode classes first (List.mem_flatten.mpr ⟨paths, pathsMember, firstMember⟩),
        decode_encode classes second (List.mem_flatten.mpr ⟨paths, pathsMember, secondMember⟩)]
      exact .edge paths pathsMember firstMember secondMember
  | symm _ ih => exact connected_symm classes _ _ (ih rightBound leftBound)
  | @trans left middle right first second ih ihtail =>
      have middleBound : middle < (members classes).length := by
        rcases EqualityArray.connected_members (encoded classes) left middle first with same | present
        · simpa [← same] using leftBound
        · exact encoded_bounded classes middle present.2
      exact .trans (ih leftBound middleBound) (ihtail middleBound rightBound)

/-- The source's decoded groups have exactly the reference class connectivity. -/
theorem decoded_partition (classes : Constraints) (mergeFuel readFuel : Nat)
    (forest after : UnionFind.Forest) (entries : List (Nat × Nat))
    (merged : EqualityArray.mergePairs mergeFuel ((encoded classes).flatMap EqualityArray.classPairs)
      (UnionFind.withInitialValues (encoded classes).flatten) = some forest)
    (readback : EqualityArray.readAll readFuel (List.range (members classes).length) forest = some (entries, after))
    (left right : Path) :
    (∃ paths ∈ decodedGroups classes entries, left ∈ paths ∧ right ∈ paths) ↔ Connected classes left right := by
  have valid := (EqualityArray.mergePairs_correct (Value := Nat) _ _ (UnionFind.initial_total _) mergeFuel forest merged).1
  have grouped := EqualityArray.grouped_partition (List.range (members classes).length) forest valid readFuel entries after readback
  constructor
  · rintro ⟨paths, present, first, second⟩
    obtain ⟨indices, indicesMember, rfl⟩ := List.mem_map.mp present
    obtain ⟨leftIndex, leftMember, rfl⟩ := List.mem_map.mp first
    obtain ⟨rightIndex, rightMember, rfl⟩ := List.mem_map.mp second
    obtain ⟨leftDomain, rightDomain, related⟩ := (grouped leftIndex rightIndex).mp ⟨indices, indicesMember, leftMember, rightMember⟩
    exact decode_connected classes leftIndex rightIndex
      ((EqualityArray.complete_connected (encoded classes) mergeFuel forest merged leftIndex rightIndex).mp related)
      (List.mem_range.mp leftDomain)
      (List.mem_range.mp rightDomain)
  · intro connected
    have original := connected_member classes left right connected
    have leftPresent : left ∈ classes.flatten := by
      obtain ⟨paths, present, member⟩ := (mem_members left classes).mp original.1
      exact List.mem_flatten.mpr ⟨paths, present, member⟩
    have rightPresent : right ∈ classes.flatten := by
      obtain ⟨paths, present, member⟩ := (mem_members right classes).mp original.2
      exact List.mem_flatten.mpr ⟨paths, present, member⟩
    have related := (EqualityArray.complete_connected (encoded classes) mergeFuel forest merged
      (encode classes left) (encode classes right)).mpr (encode_connected classes left right connected)
    obtain ⟨indices, present, first, second⟩ := (grouped (encode classes left) (encode classes right)).mpr
      ⟨List.mem_range.mpr (encode_bounded classes left leftPresent),
        List.mem_range.mpr (encode_bounded classes right rightPresent), related⟩
    exact ⟨indices.map (decode classes), List.mem_map.mpr ⟨indices, present, rfl⟩,
      List.mem_map.mpr ⟨_, first, decode_encode classes left leftPresent⟩,
      List.mem_map.mpr ⟨_, second, decode_encode classes right rightPresent⟩⟩

/-- Distinct root buckets remain disjoint after decoding their allocated indexes. -/
theorem decoded_disjoint (classes : Constraints) (forest after : UnionFind.Forest)
    (valid : UnionFind.Total forest) (fuel : Nat) (entries : List (Nat × Nat))
    (readback : EqualityArray.readAll fuel (List.range (members classes).length) forest = some (entries, after)) :
    (decodedGroups classes entries).Pairwise (fun left right => overlap left right = false) := by
  have listed := (EqualityArray.readAll_correct _ forest valid fuel entries after readback).2.2
  simp only [decodedGroups, EqualityArray.groups, List.map_map, Function.comp_def]
  apply List.pairwise_map.mpr
  apply (EqualityTrie.eraseDups_nodup (entries.map Prod.fst)).imp
  intro leftRoot rightRoot different
  apply Bool.eq_false_iff.mpr
  intro overlapping
  obtain ⟨path, leftMember, rightMember⟩ := (overlap_correct _ _).mp overlapping
  obtain ⟨⟨leftKey, leftIndex⟩, leftMember, leftPath⟩ := List.mem_map.mp leftMember
  obtain ⟨⟨rightKey, rightIndex⟩, rightMember, rightPath⟩ := List.mem_map.mp rightMember
  simp only [List.mem_filter, beq_iff_eq] at leftMember rightMember
  dsimp only at leftMember rightMember leftPath rightPath
  obtain ⟨leftPresent, rfl⟩ := leftMember
  obtain ⟨rightPresent, rfl⟩ := rightMember
  obtain ⟨leftDomain, leftSize, first⟩ := (listed leftKey leftIndex).mp leftPresent
  obtain ⟨rightDomain, rightSize, second⟩ := (listed rightKey rightIndex).mp rightPresent
  have same := decode_injective classes leftIndex rightIndex
    (List.mem_range.mp leftDomain)
    (List.mem_range.mp rightDomain) (leftPath.trans rightPath.symm)
  subst rightIndex
  exact different (UnionFind.reaches_unique first second).1

/-- Every decoded group contains an actual original readback member. -/
theorem decoded_nonempty (classes : Constraints) (entries : List (Nat × Nat)) (paths : Class)
    (present : paths ∈ decodedGroups classes entries) : ∃ path, path ∈ paths := by
  obtain ⟨indices, indicesMember, rfl⟩ := List.mem_map.mp present
  obtain ⟨root, rootMember, same⟩ := group_named entries indices indicesMember
  subst indices
  obtain ⟨⟨key, index⟩, entryMember, same⟩ := List.mem_map.mp rootMember
  dsimp only at same
  subst key
  exact ⟨decode classes index, List.mem_map.mpr ⟨index, (bucket_exact entries root index).mpr entryMember, rfl⟩⟩

/-- Completion of nontrivial input classes has no trivial output component. -/
theorem decoded_active (classes : Constraints) (active : Active classes) (mergeFuel readFuel : Nat)
    (forest after : UnionFind.Forest) (entries : List (Nat × Nat))
    (merged : EqualityArray.mergePairs mergeFuel ((encoded classes).flatMap EqualityArray.classPairs)
      (UnionFind.withInitialValues (encoded classes).flatten) = some forest)
    (readback : EqualityArray.readAll readFuel (List.range (members classes).length) forest = some (entries, after)) :
    Active (decodedGroups classes entries) := by
  have valid := (EqualityArray.mergePairs_correct (Value := Nat) _ _ (UnionFind.initial_total _) mergeFuel forest merged).1
  have disjoint := decoded_disjoint classes forest after valid readFuel entries readback
  have partition := decoded_partition classes mergeFuel readFuel forest after entries merged readback
  intro paths present
  obtain ⟨pivot, pivotMember⟩ := decoded_nonempty classes entries paths present
  have connected := (partition pivot pivot).mp ⟨paths, present, pivotMember, pivotMember⟩
  obtain ⟨original, originalMember, originalPivot⟩ := (mem_members pivot classes).mp (connected_member classes pivot pivot connected).1
  have included : ∀ path ∈ original, path ∈ paths := by
    intro path member
    obtain ⟨other, otherMember, pivotOther, pathOther⟩ := (partition pivot path).mpr
      (.edge original originalMember originalPivot member)
    have same := components_equal _ disjoint paths other present otherMember pivot pivotMember pivotOther
    simpa only [same] using pathOther
  exact nontrivial_mono original paths included (active original originalMember)

/-- Canonical path and class sorting preserve the exact pair partition. -/
theorem canonical_partition_pairs (classes : Constraints) (left right : Path) :
    (∃ paths ∈ canonicalize classes, left ∈ paths ∧ right ∈ paths) ↔
      ∃ paths ∈ classes, left ∈ paths ∧ right ∈ paths := by
  simp only [canonicalize, List.mem_mergeSort]
  constructor
  · rintro ⟨paths, present, first, second⟩
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
    exact ⟨original, member, (mem_canonicalClass left original).mp first, (mem_canonicalClass right original).mp second⟩
  · rintro ⟨paths, present, first, second⟩
    exact ⟨canonicalClass paths, List.mem_map.mpr ⟨paths, present, rfl⟩,
      (mem_canonicalClass left paths).mpr first, (mem_canonicalClass right paths).mpr second⟩

/-- The actual array completion and the reference completion return the same canonical classes. -/
theorem source_complete_eq (classes : Constraints) (active : Active classes) (mergeFuel readFuel : Nat)
    (forest after : UnionFind.Forest) (entries : List (Nat × Nat))
    (merged : EqualityArray.mergePairs mergeFuel ((encoded classes).flatMap EqualityArray.classPairs)
      (UnionFind.withInitialValues (encoded classes).flatten) = some forest)
    (readback : EqualityArray.readAll readFuel (List.range (members classes).length) forest = some (entries, after)) :
    complete classes = canonicalize (decodedGroups classes entries) := by
  have valid := (EqualityArray.mergePairs_correct (Value := Nat) _ _ (UnionFind.initial_total _) mergeFuel forest merged).1
  apply complete_matches_partition classes _ active
  · exact canonicalize_active _ (decoded_active classes active mergeFuel readFuel forest after entries merged readback)
  · exact canonicalize_disjoint _ (decoded_disjoint classes forest after valid readFuel entries readback)
  · exact canonicalize_ordered _
  · exact canonicalize_members _
  · intro left right
    exact (canonical_partition_pairs _ left right).trans
      (decoded_partition classes mergeFuel readFuel forest after entries merged readback left right)

/-- Complete source equality merging with the concrete array representation. -/
def completeArray (fuel : Nat) (classes : Constraints) : Option Constraints := do
  let parents ← EqualityArray.mergeArrays fuel ((encoded classes).flatMap EqualityArray.classPairs) id
  let (entries, _) ← EqualityArray.readArrays fuel (List.range (members classes).length) parents
  pure (canonicalize (decodedGroups classes entries))

/-- Actual array completion eventually returns exactly the proved reference completion. -/
theorem completeArray_eventual (classes : Constraints) (active : Active classes) :
    ∃ bound, ∀ fuel, bound ≤ fuel → completeArray fuel classes = some (complete classes) := by
  obtain ⟨mergeFuel, forest, merged⟩ := EqualityArray.mergePairs_terminates
    ((encoded classes).flatMap EqualityArray.classPairs)
    (UnionFind.withInitialValues (encoded classes).flatten) (UnionFind.initial_total _)
  have valid := (EqualityArray.mergePairs_correct (Value := Nat) _ _ (UnionFind.initial_total _) mergeFuel forest merged).1
  obtain ⟨readFuel, entries, after, readback⟩ := EqualityArray.readAll_terminates
    (List.range (members classes).length) forest valid
  have completeSame := source_complete_eq classes active mergeFuel readFuel forest after entries merged readback
  refine ⟨max mergeFuel readFuel, ?_⟩
  intro fuel enough
  have mergeExtended := EqualityArray.mergePairs_more _ _ mergeFuel fuel (by omega) forest merged
  have readExtended := EqualityArray.readAll_more _ forest readFuel fuel (by omega) entries after readback
  have arrayMerged : EqualityArray.mergeArrays fuel ((encoded classes).flatMap EqualityArray.classPairs) id =
      some (ArrayUnionFind.erase forest) := by
    simpa only [ArrayUnionFind.initial_array] using
      EqualityArray.mergeArrays_refines _ _ (UnionFind.initial_total _) fuel forest mergeExtended
  have arrayRead := EqualityArray.readArrays_refines _ forest valid fuel entries after readExtended
  simp [completeArray, arrayMerged, arrayRead, Bind.bind, Option.bind, completeSame]

end MicroCFTA.EqualityIndex
