import MicroCFTA.PlanVariants

/-!
# Complete finite plan-position constructor dispatch

Values are erased because planPosition reads only counts and sizes. Pure
has size zero. Pay increments the selected size without changing its rank.
Positive Scale multiplies each size and preserves both rank orders.
Sized leaf rows use the existing complete bounded table model. Ordered
choices are right-associated; each step adds the earlier class count.
-/
namespace MicroCFTA.SourcePlanPositions
open SizedRank
attribute [local instance] lexOrd

/-- The source plan structure read by finite rank-to-size conversion. -/
inductive Plan where
  | select (count : Nat)
  | selectOnDemand (count : Nat)
  | pure
  | pay (inner : Plan)
  | scale (factor : Nat) (positive : 0 < factor) (inner : Plan)
  | shared (inner : Plan)
  | map (inner : Plan)
  | choice (left right : Plan)
  | ap (left right : Plan)
  | sized (classes : Nat → List Unit) (bound : Nat)

/-- Counts are derived from the same child plans used by position conversion. -/
def count : Plan → Nat
  | .select total | .selectOnDemand total => total
  | .pure => 1
  | .pay inner | .scale _ _ inner | .shared inner | .map inner => count inner
  | .choice left right => count left + count right
  | .ap left right => count left * count right
  | .sized classes bound => PlanVariants.count (.sized classes bound)

/-- Independent class lists retain original finite member ranks. -/
def classRanks : Plan → Nat → List Nat
  | .select total, size | .selectOnDemand total, size => if size = 1 then List.range total else []
  | .pure, size => if size = 0 then [0] else []
  | .pay _, 0 => []
  | .pay inner, size + 1 => classRanks inner size
  | .scale factor _ inner, size =>
      if size % factor = 0 then classRanks inner (size / factor) else []
  | .shared inner, size | .map inner, size => classRanks inner size
  | .choice left right, size => classRanks left size ++ (classRanks right size).map (count left + ·)
  | .ap left right, size =>
      (List.range (size + 1)).flatMap fun split =>
        Decoder.applyValues ((classRanks left split).map
          (fun first second => Probability.pairRank (count right) first second))
          (classRanks right (size - split))
  | .sized classes bound, size => PlanVariants.classRanks (.sized classes bound) size

/-- Execute each source position branch with the same counts and product offsets. -/
def position : Plan → Nat → Option Position
  | .select total, rank | .selectOnDemand total, rank => if rank < total then some ⟨1, rank⟩ else none
  | .pure, rank => if rank < 1 then some ⟨0, rank⟩ else none
  | .pay inner, rank => (position inner rank).map (fun part => ⟨part.size + 1, part.rank⟩)
  | .scale factor _ inner, rank => (position inner rank).map (fun part => ⟨factor * part.size, part.rank⟩)
  | .shared inner, rank | .map inner, rank => position inner rank
  | .choice left right, rank =>
      if rank < count left then position left rank
      else (position right (rank - count left)).map
        (fun part => ⟨part.size, (classRanks left part.size).length + part.rank⟩)
  | .ap left right, rank =>
      if rank < count left * count right then do
        let first ← position left (rank / count right)
        let second ← position right (rank % count right)
        pure (productPosition (fun size => (classRanks left size).length)
          (fun size => (classRanks right size).length) first second)
      else none
  | .sized classes bound, rank => PlanVariants.position (.sized classes bound) rank

/-- Every valid finite rank reaches one source size-class position. -/
theorem position_complete (plan : Plan) (rank : Nat) (valid : rank < count plan) :
    ∃ part, position plan rank = some part := by
  induction plan generalizing rank with
  | select total | selectOnDemand total => exact ⟨⟨1, rank⟩, by simpa [position, count] using valid⟩
  | pure => exact ⟨⟨0, rank⟩, by simpa [position, count] using valid⟩
  | pay inner ih =>
      obtain ⟨part, found⟩ := ih rank valid
      exact ⟨⟨part.size + 1, part.rank⟩, by simp [position, found]⟩
  | scale factor positive inner ih =>
      obtain ⟨part, found⟩ := ih rank valid
      exact ⟨⟨factor * part.size, part.rank⟩, by simp [position, found]⟩
  | shared inner ih | map inner ih => exact ih rank valid
  | choice left right ihl ihr =>
      by_cases first : rank < count left
      · obtain ⟨part, found⟩ := ihl rank first
        exact ⟨part, by simp [position, first, found]⟩
      · obtain ⟨part, found⟩ := ihr (rank - count left) (by simp only [count] at valid; omega)
        exact ⟨⟨part.size, (classRanks left part.size).length + part.rank⟩, by simp [position, first, found]⟩
  | ap left right ihl ihr =>
      have split := Probability.split_lt valid
      obtain ⟨first, firstFound⟩ := ihl (rank / count right) split.1
      obtain ⟨second, secondFound⟩ := ihr (rank % count right) split.2
      refine ⟨productPosition (fun size => (classRanks left size).length)
        (fun size => (classRanks right size).length) first second, ?_⟩
      simp [position, firstFound, secondFound, show rank < count left * count right from valid]
  | sized classes bound => exact PlanVariants.position_complete (.sized classes bound) rank valid

/-- Invalid ranks fail before they can create a class position. -/
theorem position_none (plan : Plan) (rank : Nat) (invalid : count plan ≤ rank) :
    position plan rank = none := by
  induction plan generalizing rank with
  | select total | selectOnDemand total =>
      simp only [count] at invalid
      simp only [position, ite_eq_right (Nat.not_lt.mpr invalid)]
  | pure =>
      simp only [count] at invalid
      simp only [position, ite_eq_right (Nat.not_lt.mpr invalid)]
  | pay inner ih => simp [position, ih rank invalid]
  | scale factor positive inner ih => simp [position, ih rank invalid]
  | shared inner ih | map inner ih => exact ih rank invalid
  | choice left right ihl ihr =>
      have first : ¬rank < count left := by simp only [count] at invalid; omega
      simp [position, first, ihr (rank - count left) (by simp only [count] at invalid; omega)]
  | ap left right ihl ihr =>
      simp only [count] at invalid
      simp only [position, ite_eq_right (Nat.not_lt.mpr invalid)]
  | sized classes bound => exact PlanVariants.position_none (.sized classes bound) rank invalid

/-- The source's outer cardinality guard is equivalent to the modeled branch checks. -/
theorem position_exists_iff (plan : Plan) (rank : Nat) :
    (∃ part, position plan rank = some part) ↔ rank < count plan := by
  constructor
  · rintro ⟨part, found⟩
    by_cases valid : rank < count plan
    · exact valid
    · rw [position_none plan rank (by omega)] at found
      contradiction
  · exact position_complete plan rank

/-- Every produced position selects precisely its original member rank. -/
theorem position_replay (plan : Plan) (rank : Nat) (part : Position)
    (found : position plan rank = some part) :
    (classRanks plan part.size)[part.rank]? = some rank := by
  induction plan generalizing rank part with
  | select total | selectOnDemand total =>
      simp only [position] at found
      split at found
      · have same : part = ⟨1, rank⟩ := Option.some.inj found.symm
        subst part
        simp [classRanks, *]
      · contradiction
  | pure =>
      simp only [position] at found
      split at found
      · have same : part = ⟨0, rank⟩ := Option.some.inj found.symm
        subst part
        have zero : rank = 0 := by omega
        simp [classRanks, zero]
      · contradiction
  | pay inner ih =>
      cases previous : position inner rank with
      | none => simp [position, previous] at found
      | some old =>
          have same : part = ⟨old.size + 1, old.rank⟩ := by simpa [position, previous] using found.symm
          subst part
          exact ih rank old previous
  | scale factor positive inner ih =>
      cases previous : position inner rank with
      | none => simp [position, previous] at found
      | some old =>
          have same : part = ⟨factor * old.size, old.rank⟩ := by
            simpa [position, previous] using found.symm
          subst part
          simpa [classRanks, Nat.mul_div_cancel_left old.size positive] using ih rank old previous
  | shared inner ih | map inner ih => exact ih rank part found
  | choice left right ihl ihr =>
      simp only [position] at found
      split at found
      next inLeft =>
        have replay := ihl rank part found
        have valid := (List.getElem?_eq_some_iff.mp replay).1
        rw [classRanks, List.getElem?_append_left valid]
        exact replay
      next inRight =>
        cases previous : position right (rank - count left) with
        | none => simp [previous] at found
        | some old =>
            have same : part = ⟨old.size, (classRanks left old.size).length + old.rank⟩ :=
              by simpa [previous] using found.symm
            subst part
            have replay := ihr _ old previous
            simp only [classRanks]
            rw [List.getElem?_append_right (by omega)]
            simp only [Nat.add_sub_cancel_left, List.getElem?_map, replay, Option.map_some]
            congr 1
            omega
  | ap left right ihl ihr =>
      simp only [position] at found
      split at found
      next valid =>
        cases firstFound : position left (rank / count right) with
        | none => simp [firstFound] at found
        | some first => cases secondFound : position right (rank % count right) with
          | none => simp [firstFound, secondFound] at found
          | some second =>
              have same : part = productPosition (fun size => (classRanks left size).length)
                  (fun size => (classRanks right size).length) first second := by
                simpa [firstFound, secondFound] using found.symm
              subst part
              have firstReplay := ihl _ first firstFound
              have secondReplay := ihr _ second secondFound
              have firstValid := (List.getElem?_eq_some_iff.mp firstReplay).1
              have secondValid := (List.getElem?_eq_some_iff.mp secondReplay).1
              have replay := productPosition_replay
                (fun size => (classRanks left size).map
                  (fun first second => Probability.pairRank (count right) first second))
                (classRanks right) first second (by simpa using firstValid) secondValid
              simp only [List.length_map] at replay
              rw [classRanks, productPosition_size, replay]
              simp only [List.getElem?_map, firstReplay, secondReplay, Option.map_some, Option.bind_some]
              exact congrArg some (Probability.pair_split (count right) rank)
      next invalid => contradiction
  | sized classes bound => exact PlanVariants.position_replay (.sized classes bound) rank part found

/-- Two original ranks cannot collapse to the same size-class position. -/
theorem position_injective (plan : Plan) (first second : Nat) (part : Position)
    (left : position plan first = some part) (right : position plan second = some part) : first = second :=
  Option.some.inj ((position_replay plan first part left).symm.trans (position_replay plan second part right))

/-- Every rank stored anywhere in the source size index is a valid ordinary rank. -/
theorem class_rank_bound (plan : Plan) (size rank : Nat) (member : rank ∈ classRanks plan size) :
    rank < count plan := by
  induction plan generalizing size rank with
  | select total | selectOnDemand total =>
      simp only [classRanks] at member
      split at member
      · exact List.mem_range.mp member
      · simp at member
  | pure =>
      simp only [classRanks] at member
      split at member
      · have zero : rank = 0 := by simpa using member
        simp [zero, count]
      · simp at member
  | pay inner ih =>
      cases size with
      | zero => simp [classRanks] at member
      | succ size => exact ih size rank member
  | scale factor positive inner ih =>
      simp only [classRanks] at member
      split at member
      · exact ih (size / factor) rank member
      · simp at member
  | shared inner ih | map inner ih => exact ih size rank member
  | choice left right ihl ihr =>
      rcases List.mem_append.mp member with first | second
      · have bound := ihl size rank first
        simp only [count]
        omega
      · obtain ⟨original, present, same⟩ := List.mem_map.mp second
        have bound := ihr size original present
        simp only [count]
        omega
  | ap left right ihl ihr =>
      obtain ⟨split, _, present⟩ := List.mem_flatMap.mp member
      simp only [Decoder.applyValues, List.mem_flatMap, List.mem_map] at present
      obtain ⟨function, ⟨first, firstMember, firstSame⟩, second, secondMember, same⟩ := present
      subst function
      subst rank
      exact Probability.pairRank_lt (ihl split first firstMember) (ihr (size - split) second secondMember)
  | sized classes bound =>
      change rank ∈ PlanVariants.sizedRanks classes bound size at member
      simp only [PlanVariants.sizedRanks] at member
      split at member
      next within =>
        obtain ⟨localRank, present, same⟩ := List.mem_map.mp member
        have found := PlanVariants.position_sized_offset classes bound ⟨size, localRank⟩ within (List.mem_range.mp present)
        exact (PlanVariants.position_exists_iff (.sized classes bound) rank).mp
          ⟨⟨size, localRank⟩, by simpa [same] using found⟩
      next outside => simp at member

/-- Convert callback rows exactly as staticTerms does, before sorting. -/
def convert (plan : Plan) (candidates : List (Nat × Bool)) : List (Position × Bool) :=
  candidates.filterMap fun (rank, checked) => (position plan rank).map (fun part => (part, checked))

/-- Conversion preserves each valid callback rank and its checked-symbol flag. -/
theorem converted_member (plan : Plan) (candidates : List (Nat × Bool)) (part : Position) (checked : Bool) :
    (part, checked) ∈ convert plan candidates ↔
      ∃ rank, (rank, checked) ∈ candidates ∧ position plan rank = some part := by
  simp only [convert, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨rank, flag⟩, member, position, found, same⟩
    obtain ⟨samePosition, sameFlag⟩ := Prod.mk.inj same
    change flag = checked at sameFlag
    subst position
    subst flag
    exact ⟨rank, member, found⟩
  · rintro ⟨rank, member, found⟩
    exact ⟨(rank, checked), member, part, found, rfl⟩

/-- Conversion retains every valid original candidate without assuming any callback law. -/
theorem convert_complete (plan : Plan) (candidates : List (Nat × Bool)) (rank : Nat) (checked : Bool)
    (member : (rank, checked) ∈ candidates) (valid : rank < count plan) :
    ∃ part, (part, checked) ∈ convert plan candidates ∧ (classRanks plan part.size)[part.rank]? = some rank := by
  obtain ⟨part, found⟩ := position_complete plan rank valid
  exact ⟨part, (converted_member plan candidates part checked).mpr ⟨rank, member, found⟩,
    position_replay plan rank part found⟩

/-- The source sorts by size, class rank, and then checked-symbol flag. -/
def sorted (plan : Plan) (candidates : List (Nat × Bool)) : List (Position × Bool) :=
  (convert plan candidates).mergeSort (fun left right =>
    compare (left.1.size, left.1.rank, if left.2 then (1 : Nat) else 0)
      (right.1.size, right.1.rank, if right.2 then (1 : Nat) else 0) != .gt)

/-- Sorting changes no converted position or its flag. -/
theorem sorted_member (plan : Plan) (candidates : List (Nat × Bool)) (part : Position) (checked : Bool) :
    (part, checked) ∈ sorted plan candidates ↔
      ∃ rank, (rank, checked) ∈ candidates ∧ position plan rank = some part := by
  simpa [sorted] using converted_member plan candidates part checked

/-- Every sorted candidate has a valid source rank and a valid class position. -/
theorem sorted_valid (plan : Plan) (candidates : List (Nat × Bool)) (part : Position) (checked : Bool)
    (member : (part, checked) ∈ sorted plan candidates) :
    ∃ rank, rank < count plan ∧ (rank, checked) ∈ candidates ∧
      (classRanks plan part.size)[part.rank]? = some rank ∧ part.rank < (classRanks plan part.size).length := by
  obtain ⟨rank, original, found⟩ := (sorted_member plan candidates part checked).mp member
  have replay := position_replay plan rank part found
  exact ⟨rank, (position_exists_iff plan rank).mp ⟨part, found⟩, original, replay,
    (List.getElem?_eq_some_iff.mp replay).1⟩

/-- The converted term index selects through its original ordinary member rank. -/
def selectClass (plan : Plan) (select : Nat → Option Value) (part : Position) : Option Value :=
  ((classRanks plan part.size)[part.rank]?).bind select

/-- Every valid size-index entry can safely invoke the original outcome selector. -/
theorem every_class_selection_total (plan : Plan) (select : Nat → Option Value)
    (total : ∀ rank, rank < count plan → ∃ value, select rank = some value)
    (part : Position) (valid : part.rank < (classRanks plan part.size).length) :
    ∃ value, selectClass plan select part = some value := by
  let rank := (classRanks plan part.size)[part.rank]
  obtain ⟨value, selected⟩ := total rank (class_rank_bound plan part.size rank (List.getElem_mem valid))
  exact ⟨value, by simp [selectClass, List.getElem?_eq_getElem valid, selected, rank]⟩

/-- No source outcome error can arise at a converted valid rank when original selection is total. -/
theorem class_selection_total (plan : Plan) (select : Nat → Option Value)
    (total : ∀ rank, rank < count plan → ∃ value, select rank = some value)
    (rank : Nat) (part : Position) (found : position plan rank = some part) :
    ∃ value, selectClass plan select part = some value := by
  obtain ⟨value, selected⟩ := total rank ((position_exists_iff plan rank).mp ⟨part, found⟩)
  exact ⟨value, by simp [selectClass, position_replay plan rank part found, selected]⟩

/-- staticTerms preserves each emitted checked-symbol certificate. -/
theorem sorted_checked (plan : Plan) (select : Nat → Option Value) (project : Value → Observation)
    (query : Observation) (candidates : List (Nat × Bool))
    (checked : ∀ rank, (rank, true) ∈ candidates →
      ∃ value, select rank = some value ∧ project value = query)
    (part : Position) (member : (part, true) ∈ sorted plan candidates) :
    ∃ value, selectClass plan select part = some value ∧ project value = query := by
  obtain ⟨rank, original, found⟩ := (sorted_member plan candidates part true).mp member
  obtain ⟨value, selected, matched⟩ := checked rank original
  exact ⟨value, by simp [selectClass, position_replay plan rank part found, selected], matched⟩

/-- Any original certified member also appears in the converted sorted callback. -/
theorem sorted_complete (plan : Plan) (select : Nat → Option Value)
    (candidates : List (Nat × Bool)) (rank : Nat) (value : Value)
    (valid : rank < count plan) (member : (rank, true) ∈ candidates) (selected : select rank = some value) :
    ∃ part, (part, true) ∈ sorted plan candidates ∧ selectClass plan select part = some value := by
  obtain ⟨part, found⟩ := position_complete plan rank valid
  exact ⟨part, (sorted_member plan candidates part true).mpr ⟨rank, member, found⟩,
    by simp [selectClass, position_replay plan rank part found, selected]⟩

example : position (.pure) 0 = some ⟨0, 0⟩ := rfl
example : position (.pay (.choice .pure (.select 2))) 2 = some ⟨2, 1⟩ := by decide
example : position (.ap (.pay .pure) (.choice .pure (.pay .pure))) 1 = some ⟨2, 0⟩ := by cbv

end MicroCFTA.SourcePlanPositions
