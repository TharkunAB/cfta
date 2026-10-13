import MicroCFTA.CanonicalClasses

/-!
# Dense numbering of finite row-map keys

The source numbers Map.keys in ascending order by zipping them with natural
numbers. The finite key carrier contains only keys in that map. Numbering
and indexed key lookup are inverse because the key list has no duplicates.
-/

namespace MicroCFTA.SourceDenseRows

/-- The finite state domain of the row map. -/
abbrev Member (keys : List State) := {state : State // state ∈ keys}

/-- Source Map.keys is sorted set readback of the row-key inventory. -/
def keys [DecidableEq State] [Ord State] (table : List (State × Value)) : List State :=
  CanonicalClasses.sortedSet (table.map Prod.fst)

/-- Map key readback contains every stored key and nothing else. -/
theorem mem_keys [DecidableEq State] [Ord State] (table : List (State × Value)) (state : State) :
    state ∈ keys table ↔ state ∈ table.map Prod.fst := CanonicalClasses.mem_sortedSet _ _

/-- The source finite map gives a duplicate-free numbering domain. -/
theorem keys_nodup [DecidableEq State] [Ord State] (table : List (State × Value)) : (keys table).Nodup :=
  CanonicalClasses.sortedSet_nodup _

/-- Read the natural index assigned by zip Map.keys [0..]. -/
def number [DecidableEq State] (keys : List State) (state : Member keys) : Fin keys.length :=
  ⟨keys.idxOf state.val, List.idxOf_lt_length_iff.mpr state.property⟩

/-- Read the original key at one valid dense index. -/
def unnumber (keys : List State) (index : Fin keys.length) : Member keys :=
  ⟨keys[index.val], List.getElem_mem index.isLt⟩

/-- Indexed readback recovers the key supplied to the numbering map. -/
theorem unnumber_number [DecidableEq State] (keys : List State) (state : Member keys) :
    unnumber keys (number keys state) = state := by
  apply Subtype.ext
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr state.property)

/-- Every dense index is assigned once and is recovered by key lookup. -/
theorem number_unnumber [DecidableEq State] (keys : List State) (unique : keys.Nodup) (index : Fin keys.length) :
    number keys (unnumber keys index) = index := by
  apply Fin.ext
  exact unique.idxOf_getElem index.val index.isLt

/-- Dense numbering never identifies two map keys. -/
theorem number_injective [DecidableEq State] (keys : List State) (first second : Member keys)
    (same : number keys first = number keys second) : first = second := by
  have recovered := congrArg (unnumber keys) same
  simpa only [unnumber_number] using recovered

/-- The concrete numbering table preserves the original ascending key order. -/
def numbering (keys : List State) : List (State × Nat) := keys.zipIdx

/-- The emitted dense keys are exactly 0 through the map cardinality minus one. -/
theorem numbering_domain (keys : List State) : (numbering keys).map Prod.snd = List.range keys.length := by
  simp [numbering, List.range_eq_range']

/-- Dense map construction receives strictly ascending distinct integer keys. -/
theorem numbering_ascending (keys : List State) :
    (numbering keys).Pairwise (fun first second => first.2 < second.2) := by
  apply List.pairwise_map.mp
  rw [numbering_domain]
  exact List.pairwise_lt_range

/-- Extensional lookup in the actual zip-built numbering map. -/
def lookupNumber [DecidableEq State] (keys : List State) (state : State) : Option Nat :=
  ((numbering keys).find? (fun (value, _) => value == state)).map (fun entry => entry.2)

/-- Every source map lookup succeeds with the constructed number. -/
theorem lookupNumber_exact [DecidableEq State] (keys : List State) (unique : keys.Nodup) (state : Member keys) :
    lookupNumber keys state.val = some (number keys state).val := by
  unfold lookupNumber numbering
  rw [← List.findIdx?_eq_fst_find?_zipIdx (xs := keys) (p := fun value => value == state.val)]
  apply List.idxOf?_eq_some_iff.mpr
  refine ⟨(number keys state).isLt, List.getElem_idxOf _, ?_⟩
  intro index before same
  have position := unique.idxOf_getElem index (Nat.lt_trans before (number keys state).isLt)
  rw [same] at position
  change (number keys state).val = index at position
  omega

/-- Number-map lookup fails exactly outside the stored source key domain. -/
theorem lookupNumber_absent [DecidableEq State] (keys : List State) (state : State) :
    lookupNumber keys state = none ↔ state ∉ keys := by
  unfold lookupNumber numbering
  rw [← List.findIdx?_eq_fst_find?_zipIdx (xs := keys) (p := fun value => value == state)]
  exact List.idxOf?_eq_none_iff

/-- A numbering table row is exactly an indexed source key. -/
theorem numbering_member (keys : List State) (state : State) (index : Nat) :
    (state, index) ∈ numbering keys ↔ keys[index]? = some state :=
  List.mem_zipIdx_iff_getElem?

/-- The actual zipped map contains the derived number of every source key. -/
theorem numbering_number [DecidableEq State] (keys : List State) (state : Member keys) :
    (state.val, (number keys state).val) ∈ numbering keys := by
  apply (numbering_member keys _ _).mpr
  simp [number, List.idxOf_lt_length_iff.mpr state.property]

/-- No valid number is missing from the concrete source table. -/
theorem numbering_complete (keys : List State) (index : Nat) :
    (∃ state, (state, index) ∈ numbering keys) ↔ index < keys.length := by
  constructor
  · rintro ⟨state, member⟩
    exact (List.getElem?_eq_some_iff.mp ((numbering_member keys state index).mp member)).1
  · intro inside
    exact ⟨keys[index], (numbering_member keys _ index).mpr (List.getElem?_eq_getElem inside)⟩

/-- Every source key has exactly its derived dense number in the zipped table. -/
theorem numbering_unique [DecidableEq State] (keys : List State) (unique : keys.Nodup)
    (state : Member keys) (index : Nat) (member : (state.val, index) ∈ numbering keys) :
    index = (number keys state).val := by
  obtain ⟨inside, found⟩ := List.getElem?_eq_some_iff.mp ((numbering_member keys state.val index).mp member)
  have position := unique.idxOf_getElem index inside
  simpa only [found, number] using position.symm

/-- Every finite state is present in the attached source key enumeration. -/
theorem member_complete (keys : List State) (state : Member keys) : state ∈ keys.attach := by simp

/-- Attaching key-membership proofs retains the source map's uniqueness. -/
theorem member_nodup (keys : List State) (unique : keys.Nodup) : keys.attach.Nodup := by
  have mapped : (keys.attach.map Subtype.val).Nodup := by simpa using unique
  exact (List.pairwise_map.mp mapped).imp (fun different same => different (congrArg Subtype.val same))

end MicroCFTA.SourceDenseRows
