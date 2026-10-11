import MicroCFTA.PlanVariants

/-!
# Structural shrinking

This model retains the rank and size structure of every finite Haskell plan
constructor. Values and maps do not affect that structure. A choice list is
represented by right-associated binary choices. Counts and product radices
are derived from children. Sized members occur in nondecreasing size order.
Shared size caches are represented by their inner plan.
-/

namespace MicroCFTA.Shrink

/-- The finite rank structure read by the Haskell shrinker. -/
inductive Plan where
  | select (count : Nat)
  | selectOnDemand (count : Nat)
  | pure
  | pay (inner : Plan)
  | shared (inner : Plan)
  | map (inner : Plan)
  | choice (left right : Plan)
  | ap (left right : Plan)
  | sized (sizes : List Nat) (ordered : sizes.Pairwise (· ≤ ·))

/-- Count members without inspecting their values. -/
def count : Plan → Nat
  | .select n | .selectOnDemand n => n
  | .pure => 1
  | .pay p | .shared p | .map p => count p
  | .choice p q => count p + count q
  | .ap p q => count p * count q
  | .sized sizes _ => sizes.length

/-- Read one member's size. Only ranks below `count` specify members. -/
def memberSize : Plan → Nat → Nat
  | .select _, _ | .selectOnDemand _, _ => 1
  | .pure, _ => 0
  | .pay p, rank => 1 + memberSize p rank
  | .shared p, rank | .map p, rank => memberSize p rank
  | .choice p q, rank =>
      if rank < count p then memberSize p rank else memberSize q (rank - count p)
  | .ap p q, rank => memberSize p (rank / count q) + memberSize q (rank % count q)
  | .sized sizes _, rank => sizes[rank]?.getD 0

/-- Select the first member of minimum size through the plan structure. -/
def smallest : Plan → Option Nat
  | .select n | .selectOnDemand n => if n = 0 then none else some 0
  | .pure => some 0
  | .pay p | .shared p | .map p => smallest p
  | .choice p q =>
      match smallest p, smallest q with
      | none, right => right.map (count p + ·)
      | left, none => left
      | some left, some right =>
          if memberSize p left ≤ memberSize q right then some left else some (count p + right)
  | .ap p q => do
      let left ← smallest p
      let right ← smallest q
      pure (Probability.pairRank (count q) left right)
  | .sized sizes _ => if sizes = [] then none else some 0

/-- A rank of minimum size, with the least rank when sizes are equal. -/
def Minimum (plan : Plan) (rank : Nat) : Prop :=
  rank < count plan ∧ ∀ other, other < count plan →
    memberSize plan rank ≤ memberSize plan other ∧
      (memberSize plan rank = memberSize plan other → rank ≤ other)

/-- The size of a valid sized-plan member is its listed size. -/
theorem sized_size (sizes : List Nat) (ordered : sizes.Pairwise (· ≤ ·))
    (rank : Nat) (valid : rank < sizes.length) :
    memberSize (.sized sizes ordered) rank = sizes[rank] := by
  simp [memberSize, List.getElem?_eq_getElem valid]

/-- A sorted sized plan has its smallest member at rank zero. -/
theorem sized_minimum (sizes : List Nat) (ordered : sizes.Pairwise (· ≤ ·))
    (nonempty : sizes ≠ []) : Minimum (.sized sizes ordered) 0 := by
  have positive : 0 < sizes.length := List.length_pos_iff.mpr nonempty
  refine ⟨positive, fun other valid => ⟨?_, fun _ => Nat.zero_le _⟩⟩
  rw [sized_size sizes ordered 0 positive, sized_size sizes ordered other valid]
  by_cases zero : other = 0
  · subst other; exact Nat.le_refl _
  · exact List.pairwise_iff_getElem.mp ordered 0 other positive valid (by omega)

/-- The structural minimum is valid, minimum-sized, and least on ties. -/
theorem smallest_correct (plan : Plan) :
    match smallest plan with
    | none => count plan = 0
    | some rank => Minimum plan rank := by
  induction plan with
  | select n | selectOnDemand n =>
      by_cases empty : n = 0
      · simp [smallest, count, empty]
      · simp [smallest, empty, Minimum, count, memberSize]
        omega
  | pure => simp [smallest, Minimum, count, memberSize]
  | pay inner ih =>
      simp only [smallest]
      cases selected : smallest inner with
      | none => simpa [selected, count] using ih
      | some rank =>
          have best : Minimum inner rank := by simpa [selected] using ih
          exact ⟨best.1, fun other valid => by
            obtain ⟨size, tie⟩ := best.2 other valid
            constructor
            · simpa [memberSize] using Nat.add_le_add_left size 1
            · simpa [memberSize] using tie⟩
  | shared inner ih | map inner ih => exact ih
  | sized sizes ordered =>
      by_cases empty : sizes = []
      · simp [smallest, empty, count]
      · simpa [smallest, empty] using sized_minimum sizes ordered empty
  | choice left right ihl ihr =>
      cases hl : smallest left with
      | none =>
          have empty : count left = 0 := by simpa [hl] using ihl
          cases hr : smallest right with
          | none => simpa [smallest, hl, hr, count, empty] using ihr
          | some rank =>
              have best : Minimum right rank := by simpa [hr] using ihr
              simpa [smallest, hl, hr, empty, Minimum, count, memberSize] using best
      | some first =>
          have bestLeft : Minimum left first := by simpa [hl] using ihl
          cases hr : smallest right with
          | none =>
              have empty : count right = 0 := by simpa [hr] using ihr
              simp only [smallest, hl, hr]
              refine ⟨by simpa [count, empty] using bestLeft.1, fun other valid => ?_⟩
              have inLeft : other < count left := by simpa [count, empty] using valid
              simpa [memberSize, bestLeft.1, inLeft] using bestLeft.2 other inLeft
          | some second =>
              have bestRight : Minimum right second := by simpa [hr] using ihr
              have firstValid := bestLeft.1
              have secondValid := bestRight.1
              simp only [smallest, hl, hr]
              by_cases order : memberSize left first ≤ memberSize right second
              · simp only [order, ite_true]
                refine ⟨by simp only [count]; omega, fun other valid => ?_⟩
                by_cases inLeft : other < count left
                · simpa [memberSize, bestLeft.1, inLeft] using bestLeft.2 other inLeft
                · have inRight : other - count left < count right := by simp only [count] at valid; omega
                  have bound := (bestRight.2 _ inRight).1
                  simp only [memberSize, bestLeft.1, inLeft, ite_true, ite_false]
                  exact ⟨Nat.le_trans order bound, fun _ => by omega⟩
              · simp only [order, ite_false]
                have selectedRight : ¬ count left + second < count left := by omega
                refine ⟨by simp only [count]; omega, fun other valid => ?_⟩
                by_cases inLeft : other < count left
                · have bound := (bestLeft.2 other inLeft).1
                  simp only [memberSize, selectedRight, inLeft, ite_true, ite_false,
                    Nat.add_sub_cancel_left]
                  exact ⟨by omega, fun same => by omega⟩
                · have inRight : other - count left < count right := by simp only [count] at valid; omega
                  obtain ⟨bound, tie⟩ := bestRight.2 _ inRight
                  simp only [memberSize, selectedRight, inLeft, ite_false, Nat.add_sub_cancel_left]
                  exact ⟨bound, fun same => by have h := tie same; omega⟩
  | ap left right ihl ihr =>
      cases hl : smallest left with
      | none =>
          have empty : count left = 0 := by simpa [hl] using ihl
          simp [smallest, hl, count, empty]
      | some first =>
          have bestLeft : Minimum left first := by simpa [hl] using ihl
          cases hr : smallest right with
          | none =>
              have empty : count right = 0 := by simpa [hr] using ihr
              simp [smallest, hl, hr, count, empty]
          | some second =>
              have bestRight : Minimum right second := by simpa [hr] using ihr
              simp only [smallest, hl, hr, pure, Pure.pure]
              refine ⟨Probability.pairRank_lt bestLeft.1 bestRight.1, fun other valid => ?_⟩
              have split := Probability.split_lt valid
              have leftBound := bestLeft.2 (other / count right) split.1
              have rightBound := bestRight.2 (other % count right) split.2
              have pair := Probability.split_pair (left := first) bestRight.1
              have divEq := congrArg Prod.fst pair
              have modEq := congrArg Prod.snd pair
              simp only [Probability.splitRank] at divEq modEq
              simp only [memberSize, divEq, modEq]
              refine ⟨Nat.add_le_add leftBound.1 rightBound.1, fun same => ?_⟩
              have leftTie := leftBound.2 (by omega)
              have rightTie := rightBound.2 (by omega)
              have mul := Nat.mul_le_mul_right (count right) leftTie
              have restore := Probability.pair_split (count right) other
              simp only [Probability.pairRank, Probability.splitRank] at restore
              unfold Probability.pairRank
              omega

/-- Repeatedly halve a positive shrink distance. -/
def halves (distance : Nat) : List Nat :=
  if zero : distance = 0 then [] else distance :: halves (distance / 2)
termination_by distance
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- Every halved distance is positive and no greater than the starting distance. -/
theorem halves_bounds (distance step : Nat) (member : step ∈ halves distance) :
    0 < step ∧ step ≤ distance := by
  induction distance using Nat.strongRecOn with
  | ind distance ih =>
      rw [halves] at member
      split at member
      · simp at member
      next nonzero =>
        rcases List.mem_cons.mp member with same | rest
        · subst step; omega
        · have smaller : distance / 2 < distance := Nat.div_lt_self (by omega) (by decide)
          have bounds := ih _ smaller rest
          exact ⟨bounds.1, Nat.le_trans bounds.2 (Nat.div_le_self _ _)⟩

/-- Integral shrink candidates retain the source order: zero, then smaller distances. -/
def towardZero (rank : Nat) : List Nat := (halves rank).map (rank - ·)

/-- Every integral shrink candidate has a strictly smaller rank. -/
theorem towardZero_lt (rank candidate : Nat) (member : candidate ∈ towardZero rank) :
    candidate < rank := by
  obtain ⟨step, present, rfl⟩ := List.mem_map.mp member
  have bounds := halves_bounds rank step present
  omega

/-- Generate structural candidates with the same choice and product operations. -/
def shrink : Plan → Nat → List Nat
  | .select _, rank | .selectOnDemand _, rank => towardZero rank
  | .pure, _ => []
  | .pay inner, rank | .shared inner, rank | .map inner, rank => shrink inner rank
  | .sized _ _, rank => towardZero rank
  | .choice left right, rank =>
      if rank < count left then shrink left rank
      else
        (match smallest left with
          | none => []
          | some first =>
              if memberSize left first ≤ memberSize right (rank - count left) then [first] else []) ++
        (shrink right (rank - count left)).map (count left + ·)
  | .ap left right, rank =>
      (shrink left (rank / count right)).map
        (fun first => Probability.pairRank (count right) first (rank % count right)) ++
      (shrink right (rank % count right)).map
        (fun second => Probability.pairRank (count right) (rank / count right) second)

/-- Product replay has the sum of its component sizes. -/
theorem size_ap_pair (left right : Plan) (first second : Nat)
    (valid : second < count right) :
    memberSize (.ap left right) (Probability.pairRank (count right) first second) =
      memberSize left first + memberSize right second := by
  have split := Probability.split_pair (left := first) valid
  have hf := congrArg Prod.fst split
  have hs := congrArg Prod.snd split
  simp only [Probability.splitRank] at hf hs
  simp only [memberSize, hf, hs]

/-- Structural candidates have smaller ranks and do not increase member size. -/
theorem shrink_safe (plan : Plan) (rank candidate : Nat)
    (valid : rank < count plan) (member : candidate ∈ shrink plan rank) :
    candidate < rank ∧ memberSize plan candidate ≤ memberSize plan rank := by
  induction plan generalizing rank candidate with
  | select n | selectOnDemand n =>
      exact ⟨towardZero_lt _ _ member, Nat.le_refl _⟩
  | pure => simp [shrink] at member
  | pay inner ih =>
      obtain ⟨smaller, size⟩ := ih rank candidate valid member
      exact ⟨smaller, Nat.add_le_add_left size 1⟩
  | shared inner ih | map inner ih => exact ih rank candidate valid member
  | sized sizes ordered =>
      have smaller := towardZero_lt rank candidate member
      have inside : candidate < sizes.length := Nat.lt_trans smaller valid
      refine ⟨smaller, ?_⟩
      rw [sized_size sizes ordered candidate inside, sized_size sizes ordered rank valid]
      exact List.pairwise_iff_getElem.mp ordered candidate rank inside valid smaller
  | choice left right ihl ihr =>
      by_cases inLeft : rank < count left
      · have childMember : candidate ∈ shrink left rank := by simpa [shrink, inLeft] using member
        obtain ⟨smaller, size⟩ := ihl rank candidate inLeft childMember
        have candidateLeft := Nat.lt_trans smaller inLeft
        exact ⟨smaller, by simpa [memberSize, inLeft, candidateLeft] using size⟩
      · have inRight : rank - count left < count right := by simp only [count] at valid; omega
        simp only [shrink, inLeft, ite_false, List.mem_append] at member
        rcases member with earlier | childMember
        · cases selected : smallest left with
          | none => simp [selected] at earlier
          | some first =>
              simp only [selected] at earlier
              split at earlier
              next size =>
                have same : candidate = first := by simpa using earlier
                subst candidate
                have best : Minimum left first := by simpa [selected] using smallest_correct left
                have firstValid := best.1
                exact ⟨by omega, by simpa [memberSize, inLeft, firstValid] using size⟩
              next => simp at earlier
        · obtain ⟨childRank, present, rfl⟩ := List.mem_map.mp childMember
          obtain ⟨smaller, size⟩ := ihr (rank - count left) childRank inRight present
          have candidateRight : ¬ count left + childRank < count left := by omega
          refine ⟨by omega, ?_⟩
          simpa [memberSize, inLeft, candidateRight] using size
  | ap left right ihl ihr =>
      have split := Probability.split_lt valid
      have leftValid : rank / count right < count left := split.1
      have rightValid : rank % count right < count right := split.2
      have positive : 0 < count right := by omega
      have restore := Probability.pair_split (count right) rank
      simp only [Probability.pairRank, Probability.splitRank] at restore
      simp only [shrink, List.mem_append] at member
      rcases member with first | second
      · obtain ⟨first, present, rfl⟩ := List.mem_map.mp first
        obtain ⟨smaller, size⟩ := ihl _ _ leftValid present
        have mul := Nat.mul_lt_mul_of_pos_right smaller positive
        refine ⟨by unfold Probability.pairRank; omega, ?_⟩
        rw [size_ap_pair _ _ _ _ rightValid]
        exact Nat.add_le_add_right size _
      · obtain ⟨second, present, rfl⟩ := List.mem_map.mp second
        obtain ⟨smaller, size⟩ := ihr _ _ rightValid present
        refine ⟨by unfold Probability.pairRank; omega, ?_⟩
        rw [size_ap_pair _ _ _ _ (Nat.lt_trans smaller rightValid)]
        exact Nat.add_le_add_left size _

/-- A shrink candidate stays inside the finite rank interval. -/
theorem shrink_valid (plan : Plan) (rank candidate : Nat)
    (valid : rank < count plan) (member : candidate ∈ shrink plan rank) :
    candidate < count plan := Nat.lt_trans (shrink_safe plan rank candidate valid member).1 valid

/-- No sequence can take a structural shrink step forever. -/
theorem no_infinite_shrink_chain (plan : Plan) (ranks : Nat → Nat)
    (initial : ranks 0 < count plan)
    (steps : ∀ step, ranks (step + 1) ∈ shrink plan (ranks step)) : False := by
  have valid : ∀ step, ranks step < count plan := by
    intro step
    induction step with
    | zero => exact initial
    | succ step ih => exact shrink_valid plan _ _ ih (steps step)
  have bound : ∀ step, ranks step + step ≤ ranks 0 := by
    intro step
    induction step with
    | zero => omega
    | succ step ih =>
        have smaller := (shrink_safe plan _ _ (valid step) (steps step)).1
        omega
  have impossible := bound (ranks 0 + 1)
  omega

/-- Ordinary decoder semantics with each value replaced by its member size. -/
def sizeDecoder : Plan → Decoder.Plan Nat
  | .select n | .selectOnDemand n => .source (List.replicate n 1)
  | .pure => .source [0]
  | .pay p => .map (1 + ·) (sizeDecoder p)
  | .shared p | .map p => sizeDecoder p
  | .choice p q => .choice (sizeDecoder p) (sizeDecoder q)
  | .ap p q => .ap (.map Nat.add (sizeDecoder p)) (sizeDecoder q)
  | .sized sizes _ => .source sizes

/-- The size decoder has exactly the plan's rank count. -/
theorem sizeDecoder_count (plan : Plan) : Decoder.count (sizeDecoder plan) = count plan := by
  induction plan <;> simp_all [sizeDecoder, Decoder.count, count]

/-- Every valid rank decodes to the size read by the structural shrinker. -/
theorem sizeDecoder_correct (plan : Plan) (rank : Nat) (valid : rank < count plan) :
    Decoder.decode (sizeDecoder plan) rank = some (memberSize plan rank) := by
  induction plan generalizing rank with
  | select n | selectOnDemand n =>
      simp [sizeDecoder, Decoder.decode, memberSize, show rank < n from valid]
  | pure =>
      have zero : rank = 0 := by simp only [count] at valid; omega
      simp [sizeDecoder, Decoder.decode, memberSize, zero]
  | pay inner ih => simp [sizeDecoder, Decoder.decode, memberSize, ih rank valid]
  | shared inner ih | map inner ih => exact ih rank valid
  | choice left right ihl ihr =>
      by_cases inLeft : rank < count left
      · simp [sizeDecoder, Decoder.decode, sizeDecoder_count, memberSize, inLeft, ihl rank inLeft]
      · have inRight : rank - count left < count right := by simp only [count] at valid; omega
        simp [sizeDecoder, Decoder.decode, sizeDecoder_count, memberSize, inLeft, ihr _ inRight]
  | ap left right ihl ihr =>
      have split := Probability.split_lt valid
      dsimp only [Probability.splitRank] at split
      simp [sizeDecoder, Decoder.decode, Decoder.count, sizeDecoder_count, memberSize,
        show rank < count left * count right from valid, ihl _ split.1, ihr _ split.2]
  | sized sizes ordered =>
      simpa [sizeDecoder, Decoder.decode, sized_size sizes ordered rank valid]
        using List.getElem?_eq_getElem valid

/-- Replay ranks in each size class, with the source's ordered product splits. -/
def classRanks : Plan → Nat → List Nat
  | .select n, size | .selectOnDemand n, size => if size = 1 then List.range n else []
  | .pure, size => if size = 0 then [0] else []
  | .pay p, size => if size = 0 then [] else classRanks p (size - 1)
  | .shared p, size | .map p, size => classRanks p size
  | .choice p q, size => classRanks p size ++ (classRanks q size).map (count p + ·)
  | .ap p q, size =>
      (List.range (size + 1)).flatMap fun split =>
        (classRanks p split).flatMap fun left =>
          (classRanks q (size - split)).map (Probability.pairRank (count q) left)
  | .sized sizes _, size =>
      (List.range sizes.length).filter (fun rank => decide (sizes[rank]?.getD 0 = size))

/-- Class construction contains exactly the valid ranks of the stated size. -/
theorem mem_classRanks (plan : Plan) (size rank : Nat) :
    rank ∈ classRanks plan size ↔ rank < count plan ∧ memberSize plan rank = size := by
  induction plan generalizing size rank with
  | select n | selectOnDemand n =>
      by_cases same : size = 1 <;> simp [classRanks, count, memberSize, same, eq_comm]
  | pure =>
      by_cases same : size = 0
      · simp [classRanks, count, memberSize, same]
      · simp [classRanks, count, memberSize, same, eq_comm]
  | pay inner ih =>
      by_cases zero : size = 0
      · simp [classRanks, count, memberSize, zero]
      · simp only [classRanks, zero, ite_false, ih, count, memberSize]
        constructor <;> rintro ⟨valid, same⟩ <;> exact ⟨valid, by omega⟩
  | shared inner ih | map inner ih => exact ih size rank
  | sized sizes ordered => simp [classRanks, count, memberSize]
  | choice left right ihl ihr =>
      simp only [classRanks, List.mem_append, List.mem_map, ihl, ihr, count]
      constructor
      · rintro (⟨valid, sizeEq⟩ | ⟨other, ⟨valid, sizeEq⟩, rfl⟩)
        · exact ⟨by omega, by simpa [memberSize, valid] using sizeEq⟩
        · exact ⟨by omega, by simp [memberSize, show ¬count left + other < count left by omega, sizeEq]⟩
      · rintro ⟨valid, sizeEq⟩
        by_cases inLeft : rank < count left
        · exact Or.inl ⟨inLeft, by simpa [memberSize, inLeft] using sizeEq⟩
        · exact Or.inr ⟨rank - count left,
            ⟨by omega, by simpa [memberSize, inLeft] using sizeEq⟩, by omega⟩
  | ap left right ihl ihr =>
      simp only [classRanks, List.mem_flatMap, List.mem_range, List.mem_map, ihl, ihr, count]
      constructor
      · rintro ⟨split, splitValid, first, ⟨firstValid, firstSize⟩,
          second, ⟨secondValid, secondSize⟩, rfl⟩
        exact ⟨Probability.pairRank_lt firstValid secondValid, by
          rw [size_ap_pair _ _ _ _ secondValid, firstSize, secondSize]; omega⟩
      · rintro ⟨valid, sizeEq⟩
        have split := Probability.split_lt valid
        have sizes : memberSize left (rank / count right) + memberSize right (rank % count right) = size := sizeEq
        refine ⟨memberSize left (rank / count right), by omega,
          rank / count right, ⟨split.1, rfl⟩,
          rank % count right, ⟨split.2, by omega⟩, ?_⟩
        exact Probability.pair_split _ _

/-- Each size class contains each of its replay ranks only once. -/
theorem classRanks_nodup (plan : Plan) (size : Nat) : (classRanks plan size).Nodup := by
  induction plan generalizing size with
  | select n | selectOnDemand n =>
      by_cases same : size = 1 <;> simp [classRanks, same, List.nodup_range]
  | pure => by_cases same : size = 0 <;> simp [classRanks, same]
  | pay inner ih =>
      by_cases zero : size = 0 <;> simp [classRanks, zero, ih]
  | shared inner ih | map inner ih => exact ih size
  | sized sizes ordered => exact List.Pairwise.filter _ List.nodup_range
  | choice left right ihl ihr =>
      apply List.nodup_append.mpr
      refine ⟨ihl size, List.pairwise_map.mpr ((ihr size).imp ?_), ?_⟩
      · intro a b different same
        exact different (Nat.add_left_cancel same)
      · intro a ha b hb same
        obtain ⟨other, ho, rfl⟩ := List.mem_map.mp hb
        have bound := ((mem_classRanks left size a).mp ha).1
        omega
  | ap left right ihl ihr =>
      apply List.pairwise_flatMap.mpr
      constructor
      · intro split present
        apply List.pairwise_flatMap.mpr
        constructor
        · intro first firstMember
          apply List.pairwise_map.mpr
          apply List.Pairwise.imp_of_mem _ (ihr (size - split))
          intro a b ha hb different same
          have boundsA := ((mem_classRanks right _ a).mp ha).1
          have boundsB := ((mem_classRanks right _ b).mp hb).1
          exact different (Probability.pairRank_injective boundsA boundsB same).2
        · apply List.Pairwise.imp_of_mem _ (ihl split)
          intro first second hf hs different a ha b hb same
          obtain ⟨ra, hra, rfl⟩ := List.mem_map.mp ha
          obtain ⟨rb, hrb, rfl⟩ := List.mem_map.mp hb
          have boundsA := ((mem_classRanks right _ ra).mp hra).1
          have boundsB := ((mem_classRanks right _ rb).mp hrb).1
          exact different (Probability.pairRank_injective boundsA boundsB same).1
      · apply List.Pairwise.imp_of_mem _ (RecursiveSize.range_ordered (size + 1))
        intro firstSplit secondSplit hf hs different a ha b hb same
        obtain ⟨la, hla, ra, hra, rfl⟩ := (by simpa only [List.mem_flatMap, List.mem_map] using ha :
          ∃ la, la ∈ classRanks left firstSplit ∧ ∃ ra, ra ∈ classRanks right (size - firstSplit) ∧
            Probability.pairRank (count right) la ra = a)
        obtain ⟨lb, hlb, rb, hrb, rfl⟩ := (by simpa only [List.mem_flatMap, List.mem_map] using hb :
          ∃ lb, lb ∈ classRanks left secondSplit ∧ ∃ rb, rb ∈ classRanks right (size - secondSplit) ∧
            Probability.pairRank (count right) lb rb = b)
        have boundsA := ((mem_classRanks right _ ra).mp hra).1
        have boundsB := ((mem_classRanks right _ rb).mp hrb).1
        have leftEq := (Probability.pairRank_injective boundsA boundsB same).1
        have sizeA := ((mem_classRanks left _ la).mp hla).2
        have sizeB := ((mem_classRanks left _ lb).mp hlb).2
        subst lb
        omega

/-- Stream every size class strictly below the current member's size. -/
def smallerMembers (plan : Plan) (rank : Nat) : List Nat :=
  (List.range (memberSize plan rank)).flatMap (classRanks plan)

/-- The complete smaller-size stream neither drops nor adds a rank. -/
theorem mem_smallerMembers (plan : Plan) (rank candidate : Nat) :
    candidate ∈ smallerMembers plan rank ↔
      candidate < count plan ∧ memberSize plan candidate < memberSize plan rank := by
  simp only [smallerMembers, List.mem_flatMap, List.mem_range, mem_classRanks]
  constructor
  · rintro ⟨size, smaller, valid, same⟩
    exact ⟨valid, by omega⟩
  · rintro ⟨valid, smaller⟩
    exact ⟨memberSize plan candidate, smaller, valid, rfl⟩

/-- The smaller-size stream contains no repeated replay rank. -/
theorem smallerMembers_nodup (plan : Plan) (rank : Nat) :
    (smallerMembers plan rank).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun size _ => classRanks_nodup plan size, ?_⟩
  apply List.Pairwise.imp _ (RecursiveSize.range_ordered (memberSize plan rank))
  intro first second smaller a ha b hb same
  subst b
  have firstSize := ((mem_classRanks plan first a).mp ha).2
  have secondSize := ((mem_classRanks plan second a).mp hb).2
  omega

/-- Members of the smaller-size stream occur in nondecreasing size order. -/
theorem smallerMembers_ordered (plan : Plan) (rank : Nat) :
    (smallerMembers plan rank).Pairwise
      (fun first second => memberSize plan first ≤ memberSize plan second) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro size _
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj _
    have first := ((mem_classRanks plan size _).mp (List.getElem_mem hi)).2
    have second := ((mem_classRanks plan size _).mp (List.getElem_mem hj)).2
    omega
  · apply List.Pairwise.imp _ (RecursiveSize.range_ordered (memberSize plan rank))
    intro first second smaller a ha b hb
    have firstSize := ((mem_classRanks plan first a).mp ha).2
    have secondSize := ((mem_classRanks plan second b).mp hb).2
    omega

/-- Every smaller-size stream entry decodes to a strictly smaller member. -/
theorem smallerMembers_decode (plan : Plan) (rank candidate : Nat)
    (present : candidate ∈ smallerMembers plan rank) :
    Decoder.decode (sizeDecoder plan) candidate = some (memberSize plan candidate) ∧
      memberSize plan candidate < memberSize plan rank := by
  obtain ⟨valid, smaller⟩ := (mem_smallerMembers plan rank candidate).mp present
  exact ⟨sizeDecoder_correct plan candidate valid, smaller⟩

/-- Exhausting the complete smaller-size stream proves minimum failing size. -/
theorem exhausted_smaller_search (plan : Plan) (rank : Nat) (passes : Nat → Prop)
    (checked : ∀ candidate, candidate ∈ smallerMembers plan rank → passes candidate) :
    ∀ candidate, candidate < count plan →
      memberSize plan candidate < memberSize plan rank → passes candidate := by
  intro candidate valid smaller
  exact checked candidate ((mem_smallerMembers plan rank candidate).mpr ⟨valid, smaller⟩)

end MicroCFTA.Shrink
