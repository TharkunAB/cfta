import MicroCFTA.ArrayBounds

/-!
# Finite path-index allocation for equality completion

The source sorts all distinct paths and assigns consecutive indexes. This
module proves that allocation, inverse lookup, and encoded class inputs are
complete and in range. Missing paths do not occur in a class lookup.
-/
namespace MicroCFTA.EqualityIndex
open EqualityNormalize

/-- Ascending distinct member paths used by the source index map. -/
def members (classes : Constraints) : List Path := canonicalClass classes.flatten

/-- The functional value of a source member-map lookup. -/
def encode (classes : Constraints) (path : Path) : Nat := (members classes).idxOf path

/-- Inverse path lookup; the default is unreachable at allocated indexes. -/
def decode (classes : Constraints) (index : Nat) : Path := ((members classes)[index]?).getD []

/-- Every original path, and only an original path, gets an index-map entry. -/
theorem member_exact (classes : Constraints) (path : Path) : path ∈ members classes ↔ path ∈ classes.flatten :=
  mem_canonicalClass path classes.flatten

/-- The source member map has no duplicate keys. -/
theorem members_distinct (classes : Constraints) : (members classes).Nodup := canonicalClass_nodup _

/-- Every lookup made by the source class loop is inside the allocated array. -/
theorem encode_bounded (classes : Constraints) (path : Path) (present : path ∈ classes.flatten) :
    encode classes path < (members classes).length :=
  List.idxOf_lt_length_of_mem ((member_exact classes path).mpr present)

/-- Encoding and inverse path lookup preserve every original path. -/
theorem decode_encode (classes : Constraints) (path : Path) (present : path ∈ classes.flatten) :
    decode classes (encode classes path) = path := by
  simp only [decode, List.getElem?_eq_getElem (encode_bounded classes path present), Option.getD_some]
  exact List.getElem_idxOf (encode_bounded classes path present)

/-- Every allocated index decodes to an original input path. -/
theorem decode_member (classes : Constraints) (index : Nat) (within : index < (members classes).length) :
    decode classes index ∈ classes.flatten := by
  apply (member_exact classes _).mp
  simp only [decode, List.getElem?_eq_getElem within, Option.getD_some]
  exact List.getElem_mem within

/-- Inverse lookup has no holes in the allocated interval. -/
theorem encode_decode (classes : Constraints) (index : Nat) (within : index < (members classes).length) :
    encode classes (decode classes index) = index := by
  simp only [encode, decode, List.getElem?_eq_getElem within, Option.getD_some]
  exact (members_distinct classes).idxOf_getElem index within

/-- Distinct original paths cannot share a source array index. -/
theorem encode_injective (classes : Constraints) (left right : Path)
    (leftMember : left ∈ classes.flatten) (rightMember : right ∈ classes.flatten)
    (same : encode classes left = encode classes right) : left = right := by
  rw [← decode_encode classes left leftMember, ← decode_encode classes right rightMember, same]

/-- Distinct allocated indexes cannot decode to one path. -/
theorem decode_injective (classes : Constraints) (left right : Nat)
    (leftBound : left < (members classes).length) (rightBound : right < (members classes).length)
    (same : decode classes left = decode classes right) : left = right := by
  rw [← encode_decode classes left leftBound, ← encode_decode classes right rightBound, same]

/-- The source class loop translates each path through the same complete map. -/
def encoded (classes : Constraints) : List (List Nat) := classes.map (List.map (encode classes))

/-- Class translation preserves every path and its class order under inverse lookup. -/
theorem encoded_roundtrip (classes : Constraints) :
    (encoded classes).map (List.map (decode classes)) = classes := by
  simp only [encoded, List.map_map, Function.comp_def]
  conv => rhs; rw [← List.map_id classes]
  apply List.map_congr_left
  intro paths present
  change paths.map (fun path => decode classes (encode classes path)) = paths
  conv => rhs; rw [← List.map_id paths]
  apply List.map_congr_left
  intro path member
  exact decode_encode classes path (List.mem_flatten.mpr ⟨paths, present, member⟩)

/-- Each encoded member supplied to union or readback is a valid array index. -/
theorem encoded_bounded (classes : Constraints) (index : Nat) (present : index ∈ (encoded classes).flatten) :
    index < (members classes).length := by
  obtain ⟨indices, indicesMember, indexMember⟩ := List.mem_flatten.mp present
  obtain ⟨paths, pathsMember, rfl⟩ := List.mem_map.mp indicesMember
  obtain ⟨path, pathMember, rfl⟩ := List.mem_map.mp indexMember
  exact encode_bounded classes path (List.mem_flatten.mpr ⟨paths, pathsMember, pathMember⟩)

/-- Every allocated index occurs in an encoded original class. -/
theorem encoded_covers (classes : Constraints) (index : Nat) (within : index < (members classes).length) :
    index ∈ (encoded classes).flatten := by
  obtain ⟨paths, pathsMember, pathMember⟩ := List.mem_flatten.mp (decode_member classes index within)
  apply List.mem_flatten.mpr
  refine ⟨paths.map (encode classes), List.mem_map.mpr ⟨paths, pathsMember, rfl⟩, ?_⟩
  exact List.mem_map.mpr ⟨decode classes index, pathMember, encode_decode classes index within⟩

/-- The complete source path assignment gives the exact interval of allocated indexes. -/
theorem encoded_domain (classes : Constraints) (index : Nat) :
    index ∈ (encoded classes).flatten ↔ index < (members classes).length :=
  ⟨encoded_bounded classes index, encoded_covers classes index⟩

/-- Entries supplied to `Map.fromDistinctAscList` have their exact consecutive indexes. -/
theorem indexed_exact (classes : Constraints) (path : Path) (index : Nat) :
    (path, index) ∈ (members classes).zipIdx ↔ path ∈ classes.flatten ∧ index = encode classes path := by
  rw [List.mk_mem_zipIdx_iff_getElem?]
  constructor
  · intro found
    have within := (List.getElem?_eq_some_iff.mp found).1
    have decoded : decode classes index = path := by simp [decode, found]
    exact ⟨decoded ▸ decode_member classes index within, by rw [← decoded, encode_decode classes index within]⟩
  · rintro ⟨present, rfl⟩
    simp only [List.getElem?_eq_getElem (encode_bounded classes path present)]
    exact congrArg some (List.getElem_idxOf (encode_bounded classes path present))

/-- Decoding the encoded input equations preserves every arbitrary path assignment. -/
theorem input_equations (classes : Constraints) (assignment : Path → Value) :
    (∀ indices ∈ encoded classes, ∀ left ∈ indices, ∀ right ∈ indices,
      assignment (decode classes left) = assignment (decode classes right)) ↔
      ∀ paths ∈ classes, ∀ left ∈ paths, ∀ right ∈ paths, assignment left = assignment right := by
  simp only [encoded, List.forall_mem_map]
  constructor
  · intro equations paths present left leftMember right rightMember
    simpa only [decode_encode classes left (List.mem_flatten.mpr ⟨paths, present, leftMember⟩),
      decode_encode classes right (List.mem_flatten.mpr ⟨paths, present, rightMember⟩)] using
        equations paths present left leftMember right rightMember
  · intro equations paths present left leftMember right rightMember
    simpa only [decode_encode classes left (List.mem_flatten.mpr ⟨paths, present, leftMember⟩),
      decode_encode classes right (List.mem_flatten.mpr ⟨paths, present, rightMember⟩)] using
        equations paths present left leftMember right rightMember

/-- Reconstruct path sets from source representative buckets. -/
def decodedGroups (classes : Constraints) (entries : List (Nat × Nat)) : Constraints :=
  (EqualityArray.groups entries).map (List.map (decode classes))

/-- The complete indexed array loop retains exactly every original path assignment equation. -/
theorem source_equations_exact (classes : Constraints) (mergeFuel readFuel : Nat)
    (forest after : UnionFind.Forest) (entries : List (Nat × Nat))
    (merged : EqualityArray.mergePairs mergeFuel ((encoded classes).flatMap EqualityArray.classPairs)
      (UnionFind.withInitialValues (encoded classes).flatten) = some forest)
    (readback : EqualityArray.readAll readFuel (List.range (members classes).length) forest = some (entries, after))
    (assignment : Path → Value) :
    (∀ paths ∈ decodedGroups classes entries, ∀ left ∈ paths, ∀ right ∈ paths, assignment left = assignment right) ↔
      ∀ paths ∈ classes, ∀ left ∈ paths, ∀ right ∈ paths, assignment left = assignment right := by
  simp only [decodedGroups, List.forall_mem_map]
  exact (EqualityArray.complete_groups_domain_exact (encoded classes) (List.range (members classes).length)
    (fun index => List.mem_range.trans (encoded_domain classes index).symm) mergeFuel readFuel forest after entries merged readback
    (fun index => assignment (decode classes index))).trans (input_equations classes assignment)

/-- Indexed array completion preserves existing-subterm equalities in both directions. -/
theorem source_path_semantics (classes : Constraints) (active : Active classes) (mergeFuel readFuel : Nat)
    (forest after : UnionFind.Forest) (entries : List (Nat × Nat))
    (merged : EqualityArray.mergePairs mergeFuel ((encoded classes).flatMap EqualityArray.classPairs)
      (UnionFind.withInitialValues (encoded classes).flatten) = some forest)
    (readback : EqualityArray.readAll readFuel (List.range (members classes).length) forest = some (entries, after))
    (term : Language.Term Symbol) :
    Satisfies term (decodedGroups classes entries) ↔ Satisfies term classes := by
  have valid := (EqualityArray.mergePairs_correct (Value := Nat) _ _ (UnionFind.initial_total _) mergeFuel forest merged).1
  have grouped := EqualityArray.grouped_partition (List.range (members classes).length) forest valid readFuel entries after readback
  constructor
  · intro result paths pathsMember left leftMember right rightMember different
    have indexedClass : paths.map (encode classes) ∈ encoded classes := List.mem_map.mpr ⟨paths, pathsMember, rfl⟩
    have leftIndex : encode classes left ∈ paths.map (encode classes) := List.mem_map.mpr ⟨left, leftMember, rfl⟩
    have rightIndex : encode classes right ∈ paths.map (encode classes) := List.mem_map.mpr ⟨right, rightMember, rfl⟩
    have related := (EqualityArray.complete_connected (encoded classes) mergeFuel forest merged
      (encode classes left) (encode classes right)).mpr
      (.related _ indexedClass _ _ leftIndex rightIndex)
    have leftPresent := List.mem_flatten.mpr ⟨_, indexedClass, leftIndex⟩
    have rightPresent := List.mem_flatten.mpr ⟨_, indexedClass, rightIndex⟩
    obtain ⟨indices, present, first, second⟩ := (grouped (encode classes left) (encode classes right)).mpr
      ⟨List.mem_range.mpr (encoded_bounded classes _ leftPresent),
        List.mem_range.mpr (encoded_bounded classes _ rightPresent), related⟩
    have leftRound := decode_encode classes left (List.mem_flatten.mpr ⟨paths, pathsMember, leftMember⟩)
    have rightRound := decode_encode classes right (List.mem_flatten.mpr ⟨paths, pathsMember, rightMember⟩)
    have firstPath : left ∈ indices.map (decode classes) := List.mem_map.mpr ⟨_, first, leftRound⟩
    have secondPath : right ∈ indices.map (decode classes) := List.mem_map.mpr ⟨_, second, rightRound⟩
    exact result _ (List.mem_map.mpr ⟨indices, present, rfl⟩) left firstPath right secondPath different
  · intro original
    have inputEquations : ∀ paths ∈ classes, ∀ left ∈ paths, ∀ right ∈ paths,
        term.atPath left = term.atPath right := by
      intro paths present left leftMember right rightMember
      obtain ⟨value, first, second⟩ := class_pair_equal term paths (active paths present) (original paths present)
        left right leftMember rightMember
      exact first.trans second.symm
    have outputEquations := (source_equations_exact classes mergeFuel readFuel forest after entries merged readback term.atPath).mpr inputEquations
    intro paths present left leftMember right rightMember _different
    obtain ⟨indices, indicesMember, same⟩ := List.mem_map.mp present
    subst paths
    obtain ⟨index, indexMember, same⟩ := List.mem_map.mp leftMember
    subst left
    have originalIndex : index ∈ (encoded classes).flatten := by
      have both := (grouped index index).mp ⟨indices, indicesMember, indexMember, indexMember⟩
      exact encoded_covers classes index (List.mem_range.mp both.1)
    have originalPath := decode_member classes index (encoded_bounded classes index originalIndex)
    obtain ⟨originalPaths, originalMember, pathMember⟩ := List.mem_flatten.mp originalPath
    obtain ⟨value, found⟩ := class_member_exists term originalPaths (active originalPaths originalMember)
      (original originalPaths originalMember) (decode classes index) pathMember
    have firstMember : decode classes index ∈ indices.map (decode classes) := List.mem_map.mpr ⟨index, indexMember, rfl⟩
    have equality := outputEquations (indices.map (decode classes)) (List.mem_map.mpr ⟨indices, indicesMember, rfl⟩)
      _ firstMember right rightMember
    exact ⟨value, found, equality.symm.trans found⟩

/-- Source set construction and final sorting preserve the exact completed equality semantics. -/
theorem source_canonical_semantics (classes : Constraints) (active : Active classes) (mergeFuel readFuel : Nat)
    (forest after : UnionFind.Forest) (entries : List (Nat × Nat))
    (merged : EqualityArray.mergePairs mergeFuel ((encoded classes).flatMap EqualityArray.classPairs)
      (UnionFind.withInitialValues (encoded classes).flatten) = some forest)
    (readback : EqualityArray.readAll readFuel (List.range (members classes).length) forest = some (entries, after))
    (term : Language.Term Symbol) :
    Satisfies term (canonicalize (decodedGroups classes entries)) ↔ Satisfies term classes :=
  (canonicalize_correct term _).trans
    (source_path_semantics classes active mergeFuel readFuel forest after entries merged readback term)

end MicroCFTA.EqualityIndex
