import MicroCFTA.SizedRank

/-!
# Shared and sized finite plans

This extension permits shared and sized nodes inside maps, choices, and
applications. A sized node is built from all classes up to a finite bound.
Its class order and cardinalities are derived from that construction.
Empty classes can remain in the table because their counts are zero.

Shared nodes delegate to their inner plan. Keys do not affect pure rank or
value semantics. Runtime cache storage is a separate implementation concern.
Finite lists represent source callbacks and sized-class callbacks. Infinite
lazy size indexes and optimized machine-rank dispatch remain outside this
finite model.
-/

namespace MicroCFTA.PlanVariants

open SizedRank

/-- Finite plans extended with shared nodes and bounded size-class nodes. -/
inductive Plan : Type → Type 1 where
  | finite (plan : Decoder.Plan α) : Plan α
  | shared (key : Nat) (inner : Plan α) : Plan α
  | sized (classes : Nat → List α) (bound : Nat) : Plan α
  | map (transform : α → β) (inner : Plan α) : Plan β
  | choice (left right : Plan α) : Plan α
  | ap (functions : Plan (α → β)) (arguments : Plan α) : Plan β

/-- Remove shared wrappers and expose sized classes in their ordinary rank order. -/
def erase : Plan α → Decoder.Plan α
  | .finite plan => plan
  | .shared _ inner => erase inner
  | .sized classes bound => .source ((List.range (bound + 1)).flatMap classes)
  | .map transform inner => .map transform (erase inner)
  | .choice left right => .choice (erase left) (erase right)
  | .ap functions arguments => .ap (erase functions) (erase arguments)

/-- Derive the ordinary rank count from the finite plan constructors. -/
def count (plan : Plan α) : Nat := Decoder.count (erase plan)

/-- Class counts follow ascending sizes and are computed from their finite lists. -/
def sizedCounts (classes : Nat → List α) (bound : Nat) : Sparse.Series Nat :=
  (List.range (bound + 1)).map (fun size => (size, (classes size).length))

/-- The offset of one sized class is the length of all preceding classes. -/
def sizedOffset (classes : Nat → List α) (size : Nat) : Nat :=
  ((List.range size).map (fun size => (classes size).length)).sum

/-- List ordinary run ranks in a bounded class, including zero-count classes. -/
def sizedRanks (classes : Nat → List α) (bound size : Nat) : List Nat :=
  if size ≤ bound then (List.range (classes size).length).map (sizedOffset classes size + ·) else []

/-- Derive the ordinary replay ranks of every size class compositionally. -/
def classRanks : Plan α → Nat → List Nat
  | .finite plan, size => SizedRank.planClassRanks plan size
  | .shared _ inner, size => classRanks inner size
  | .sized classes bound, size => sizedRanks classes bound size
  | .map _ inner, size => classRanks inner size
  | .choice left right, size => classRanks left size ++ (classRanks right size).map (count left + ·)
  | .ap functions arguments, size =>
      (List.range (size + 1)).flatMap fun split =>
        Decoder.applyValues ((classRanks functions split).map
          (fun function argument => Probability.pairRank (count arguments) function argument))
          (classRanks arguments (size - split))

/-- The complete `planPosition` recursion includes shared and bounded sized nodes. -/
def position : Plan α → Nat → Option Position
  | .finite plan, rank => SizedRank.planPosition plan rank
  | .shared _ inner, rank => position inner rank
  | .sized classes bound, rank => sizeClassOf (sizedCounts classes bound) rank
  | .map _ inner, rank => position inner rank
  | .choice left right, rank =>
      if rank < count left then position left rank
      else (position right (rank - count left)).map fun part =>
        ⟨part.size, (classRanks left part.size).length + part.rank⟩
  | .ap functions arguments, rank =>
      if rank < count functions * count arguments then do
        let first ← position functions (rank / count arguments)
        let second ← position arguments (rank % count arguments)
        pure (productPosition (fun size => (classRanks functions size).length)
          (fun size => (classRanks arguments size).length) first second)
      else none

/-- The sized constructor always builds a strictly ordered table. -/
theorem sizedCounts_ordered (classes : Nat → List α) (bound : Nat) :
    Sparse.Ordered (sizedCounts classes bound) :=
  List.pairwise_map.mpr (RecursiveSize.range_ordered (bound + 1))

/-- The count table has exactly the cardinality of the flattened sized constructor. -/
theorem sizedCounts_total (classes : Nat → List α) (bound : Nat) :
    ((sizedCounts classes bound).map Prod.snd).sum = count (.sized classes bound) := by
  simp only [sizedCounts, List.map_map, Function.comp_def, count, erase, Decoder.count,
    List.length_flatMap]

/-- Every sized-node position identifies a listed class and a valid rank within it. -/
theorem sized_position_valid (classes : Nat → List α) (bound rank : Nat) (part : Position)
    (found : sizeClassOf (sizedCounts classes bound) rank = some part) :
    part.size ≤ bound ∧ part.rank < (classes part.size).length := by
  obtain ⟨sizeCount, member, valid⟩ := sizeClassOf_valid _ _ _ found
  obtain ⟨size, sizeMember, same⟩ := List.mem_map.mp member
  have sizeSame : size = part.size := congrArg Prod.fst same
  have countSame : (classes size).length = sizeCount := congrArg Prod.snd same
  have within := List.mem_range.mp sizeMember
  constructor
  · omega
  · simpa only [← sizeSame, countSame] using valid

/-- Selecting a sized node's computed position recovers its ordinary rank. -/
theorem sized_position_replay (classes : Nat → List α) (bound rank : Nat) (part : Position)
    (found : sizeClassOf (sizedCounts classes bound) rank = some part) :
    (sizedRanks classes bound part.size)[part.rank]? = some rank := by
  obtain ⟨within, valid⟩ := sized_position_valid classes bound rank part found
  have ranked := sizeMajorRank_sizeClassOf (sizedCounts classes bound)
    (sizedCounts_ordered classes bound) rank part found
  have offset := countBelow_range (fun size => (classes size).length) (bound + 1) part.size (by omega)
  change countBelow (sizedCounts classes bound) part.size = sizedOffset classes part.size at offset
  unfold sizeMajorRank at ranked
  rw [offset] at ranked
  simp only [sizedRanks, ite_eq_left within, List.getElem?_map, List.getElem?_range valid, Option.map_some, ranked]

/-- A bounded sized node has a position exactly for every valid ordinary rank. -/
theorem sized_position_exists_iff (classes : Nat → List α) (bound rank : Nat) :
    (∃ part, sizeClassOf (sizedCounts classes bound) rank = some part) ↔
      rank < count (.sized classes bound) := by
  rw [sizeClassOf_exists_iff, sizedCounts_total]

/-- Every valid ordinary rank has a position, including through nested shared and sized nodes. -/
theorem position_complete (plan : Plan α) (rank : Nat) (valid : rank < count plan) :
    ∃ part, position plan rank = some part := by
  induction plan generalizing rank with
  | finite plan => exact SizedRank.planPosition_complete plan rank valid
  | shared key inner ih => exact ih rank valid
  | sized classes bound => exact (sized_position_exists_iff classes bound rank).mpr valid
  | map transform inner ih => exact ih rank valid
  | choice left right ihl ihr =>
      by_cases inLeft : rank < count left
      · obtain ⟨part, found⟩ := ihl rank inLeft
        exact ⟨part, by simp [position, inLeft, found]⟩
      · have inRight : rank - count left < count right := by
          change rank < count left + count right at valid
          omega
        obtain ⟨part, found⟩ := ihr _ inRight
        exact ⟨⟨part.size, (classRanks left part.size).length + part.rank⟩,
          by simp [position, inLeft, found]⟩
  | ap functions arguments ihf ihx =>
      obtain ⟨leftValid, rightValid⟩ := Probability.split_lt
        (leftCount := count functions) (rightCount := count arguments) valid
      obtain ⟨first, foundFirst⟩ := ihf _ leftValid
      obtain ⟨second, foundSecond⟩ := ihx _ rightValid
      dsimp only [Probability.splitRank] at foundFirst foundSecond
      refine ⟨productPosition (fun size => (classRanks functions size).length)
        (fun size => (classRanks arguments size).length) first second, ?_⟩
      simp [position, show rank < count functions * count arguments from valid, foundFirst, foundSecond]

/-- Invalid ordinary ranks have no position in any extended finite plan. -/
theorem position_none (plan : Plan α) (rank : Nat) (invalid : count plan ≤ rank) :
    position plan rank = none := by
  induction plan generalizing rank with
  | finite plan => exact SizedRank.planPosition_none plan rank invalid
  | shared key inner ih => exact ih rank invalid
  | sized classes bound =>
      cases found : position (.sized classes bound) rank with
      | none => rfl
      | some part =>
          have valid := (sized_position_exists_iff classes bound rank).mp ⟨part, found⟩
          omega
  | map transform inner ih => exact ih rank invalid
  | choice left right ihl ihr =>
      change count left + count right ≤ rank at invalid
      have inRight : count right ≤ rank - count left := by omega
      simp [position, show ¬rank < count left by omega, ihr _ inRight]
  | ap functions arguments ihf ihx =>
      simp [position, show ¬rank < count functions * count arguments from Nat.not_lt.mpr invalid]

/-- Position lookup succeeds exactly on the ordinary rank interval. -/
theorem position_exists_iff (plan : Plan α) (rank : Nat) :
    (∃ part, position plan rank = some part) ↔ rank < count plan := by
  constructor
  · rintro ⟨part, found⟩
    by_cases valid : rank < count plan
    · exact valid
    · rw [position_none plan rank (by omega)] at found
      cases found
  · exact position_complete plan rank

/-- Selecting a computed class position returns the original ordinary rank. -/
theorem position_replay (plan : Plan α) (rank : Nat) (part : Position)
    (found : position plan rank = some part) :
    (classRanks plan part.size)[part.rank]? = some rank := by
  induction plan generalizing rank part with
  | finite plan => exact SizedRank.planPosition_replay plan rank part found
  | shared key inner ih => exact ih rank part found
  | sized classes bound => exact sized_position_replay classes bound rank part found
  | map transform inner ih => exact ih rank part found
  | choice left right ihl ihr =>
      simp only [position] at found
      split at found
      next inLeft =>
        have replay := ihl rank part found
        have valid := (List.getElem?_eq_some_iff.mp replay).1
        rw [classRanks, List.getElem?_append_left valid]
        exact replay
      next inRight =>
        cases rightFound : position right (rank - count left) with
        | none => simp [rightFound] at found
        | some inner =>
            have same : (⟨inner.size, (classRanks left inner.size).length + inner.rank⟩ : Position) = part :=
              by simpa [rightFound] using found
            subst part
            have replay := ihr _ inner rightFound
            simp only [classRanks]
            rw [List.getElem?_append_right (by omega)]
            simp only [Nat.add_sub_cancel_left, List.getElem?_map, replay, Option.map_some]
            congr 1
            omega
  | ap functions arguments ihf ihx =>
      simp only [position] at found
      split at found
      next valid =>
        cases firstFound : position functions (rank / count arguments) with
        | none => simp [firstFound] at found
        | some first =>
            cases secondFound : position arguments (rank % count arguments) with
            | none => simp [firstFound, secondFound] at found
            | some second =>
                have same : productPosition (fun size => (classRanks functions size).length)
                    (fun size => (classRanks arguments size).length) first second = part := by
                  simpa [firstFound, secondFound] using found
                subst part
                have firstReplay := ihf _ first firstFound
                have secondReplay := ihx _ second secondFound
                have firstValid := (List.getElem?_eq_some_iff.mp firstReplay).1
                have secondValid := (List.getElem?_eq_some_iff.mp secondReplay).1
                have replay := productPosition_replay
                  (fun size => (classRanks functions size).map
                    (fun function argument => Probability.pairRank (count arguments) function argument))
                  (classRanks arguments) first second (by simpa using firstValid) secondValid
                simp only [List.length_map] at replay
                rw [classRanks, productPosition_size, replay]
                simp only [List.getElem?_map, firstReplay, secondReplay, Option.map_some, Option.bind_some]
                exact congrArg some (Probability.pair_split (count arguments) rank)
      next invalid => cases found

/-- A class selector returns the original ordinary rank together with its decoded value. -/
def selectClass (plan : Plan α) (part : Position) : Option (Nat × α) := do
  let rank ← (classRanks plan part.size)[part.rank]?
  let value ← Decoder.decode (erase plan) rank
  pure (rank, value)

/-- Ordinary decoding and size-class selection return the same rank and value. -/
theorem selectClass_position (plan : Plan α) (rank : Nat) (part : Position) (value : α)
    (found : position plan rank = some part) (decoded : Decoder.decode (erase plan) rank = some value) :
    selectClass plan part = some (rank, value) := by
  simp [selectClass, position_replay plan rank part found, decoded]

/-- Every ordinary run appears at a computed size-class position with its original rank. -/
theorem position_selection_complete (plan : Plan α) (rank : Nat) (valid : rank < count plan) :
    ∃ part value, position plan rank = some part ∧ selectClass plan part = some (rank, value) := by
  obtain ⟨part, found⟩ := position_complete plan rank valid
  obtain ⟨value, decoded⟩ := Decoder.decode_exists (erase plan) rank valid
  exact ⟨part, value, found, selectClass_position plan rank part value found decoded⟩

/-- Shared keys preserve counts, class positions, original ranks, and decoded values. -/
theorem shared_transparent (key : Nat) (inner : Plan α) (rank : Nat) (part : Position) :
    count (.shared key inner) = count inner ∧
      position (.shared key inner) rank = position inner rank ∧
      selectClass (.shared key inner) part = selectClass inner part := by
  exact ⟨rfl, rfl, rfl⟩

/-- A sized class position is the usual size-major offset into the flattened source. -/
theorem sized_selectClass (classes : Nat → List α) (bound : Nat) (part : Position)
    (within : part.size ≤ bound) (valid : part.rank < (classes part.size).length) :
    selectClass (.sized classes bound) part =
      (classes part.size)[part.rank]?.map (fun value => (sizedOffset classes part.size + part.rank, value)) := by
  unfold selectClass
  simp only [classRanks, sizedRanks, ite_eq_left within, List.getElem?_map,
    List.getElem?_range valid, Option.map_some, erase, Decoder.decode]
  change ((List.range (bound + 1)).flatMap classes)[sizedOffset classes part.size + part.rank]?.bind
    (fun value => some (sizedOffset classes part.size + part.rank, value)) = _
  unfold sizedOffset
  rw [RecursiveSize.get_class_offset classes bound part.size part.rank within valid]
  cases (classes part.size)[part.rank]? <;> rfl

/-- Removing zero-count classes preserves every global-rank lookup. -/
theorem sizeClassOf_drop_zero (counts : Sparse.Series Nat) (rank : Nat) :
    sizeClassOf (counts.filter (fun entry => decide (0 < entry.2))) rank = sizeClassOf counts rank := by
  induction counts generalizing rank with
  | nil => rfl
  | cons entry counts ih =>
      rcases entry with ⟨size, count⟩
      by_cases positive : 0 < count
      · simp only [List.filter_cons, positive, decide_true, ite_true, sizeClassOf]
        split <;> simp_all
      · have zero : count = 0 := by omega
        subst count
        simpa [sizeClassOf] using ih rank

/-- The nonempty class table produced by `sizeClasses` has the same position lookup. -/
theorem position_sized_nonempty (classes : Nat → List α) (bound rank : Nat) :
    position (.sized classes bound) rank =
      sizeClassOf ((sizedCounts classes bound).filter (fun entry => decide (0 < entry.2))) rank :=
  (sizeClassOf_drop_zero (sizedCounts classes bound) rank).symm

/-- Omitting empty sized-class callbacks leaves the ordinary value list unchanged. -/
theorem flatten_drop_empty (classes : List (Nat × List α)) :
    ((classes.filter (fun entry => !entry.2.isEmpty)).flatMap Prod.snd) = classes.flatMap Prod.snd := by
  induction classes with
  | nil => rfl
  | cons entry classes ih =>
      rcases entry with ⟨size, values⟩
      cases values <;> simp [ih]

/-- A valid sized-class position returns from its global offset unchanged. -/
theorem position_sized_offset (classes : Nat → List α) (bound : Nat) (part : Position)
    (within : part.size ≤ bound) (valid : part.rank < (classes part.size).length) :
    position (.sized classes bound) (sizedOffset classes part.size + part.rank) = some part := by
  have listed : Valid (sizedCounts classes bound) part := by
    refine ⟨(classes part.size).length, ?_, valid⟩
    exact List.mem_map.mpr ⟨part.size, List.mem_range.mpr (by omega), rfl⟩
  have result := sizeClassOf_sizeMajorRank (sizedCounts classes bound)
    (sizedCounts_ordered classes bound) part listed
  have offset := countBelow_range (fun size => (classes size).length) (bound + 1) part.size (by omega)
  change countBelow (sizedCounts classes bound) part.size = sizedOffset classes part.size at offset
  simpa only [position, sizeMajorRank, offset] using result

/-- Replaying any sized-class member and ranking its original rank preserves its position. -/
theorem sized_rank_roundTrip (classes : Nat → List α) (bound : Nat) (part : Position)
    (within : part.size ≤ bound) (valid : part.rank < (classes part.size).length) :
    ∃ value, selectClass (.sized classes bound) part =
      some (sizedOffset classes part.size + part.rank, value) ∧
      position (.sized classes bound) (sizedOffset classes part.size + part.rank) = some part := by
  refine ⟨(classes part.size)[part.rank], ?_, position_sized_offset classes bound part within valid⟩
  rw [sized_selectClass classes bound part within valid, List.getElem?_eq_getElem valid]
  rfl

end MicroCFTA.PlanVariants


