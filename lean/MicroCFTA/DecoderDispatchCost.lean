import MicroCFTA.DecoderDispatch

/-!
# Comparison cost of compiled offset dispatch

The source splits the offset table at half its entry count. Each compiled
split performs one rank comparison. This bound follows the actual compiler;
it does not assume that the resulting tree is balanced.
-/
namespace MicroCFTA.DecoderDispatchCost
open DecoderDispatch

/-- The maximum number of split comparisons on a root-to-leaf route. -/
def depth : Tree Payload → Nat
  | .leaf _ => 0
  | .split _ low high => max (depth low) (depth high) + 1

/-- Execute the same branch selection and count its rank comparisons. -/
def measured : Tree Payload → Nat → Entry Payload × Nat
  | .leaf entry, _ => (entry, 0)
  | .split pivot low high, rank =>
      let result := if rank < pivot then measured low rank else measured high rank
      (result.1, result.2 + 1)

/-- Adding the comparison counter does not change the selected entry. -/
theorem measured_result (tree : Tree Payload) (rank : Nat) : (measured tree rank).1 = select tree rank := by
  induction tree with
  | leaf entry => rfl
  | split pivot low high ihl ihr =>
      by_cases left : rank < pivot <;> simp [measured, select, left, ihl, ihr]

/-- Every lookup performs at most the maximum route depth comparisons. -/
theorem measured_le_depth (tree : Tree Payload) (rank : Nat) : (measured tree rank).2 ≤ depth tree := by
  induction tree with
  | leaf entry => simp [measured, depth]
  | split pivot low high ihl ihr =>
      by_cases left : rank < pivot
      · simp only [measured, left, ↓reduceIte, depth]
        exact Nat.succ_le_succ (Nat.le_trans ihl (Nat.le_max_left _ _))
      · simp only [measured, left, ↓reduceIte, depth]
        exact Nat.succ_le_succ (Nat.le_trans ihr (Nat.le_max_right _ _))

/-- Both actual table halves fit the preceding power-of-two entry bound. -/
theorem half_lengths (rows : List Item) (bits : Nat) (bound : rows.length ≤ 2 ^ (bits + 1)) :
    (rows.take (rows.length / 2)).length ≤ 2 ^ bits ∧
      (rows.drop (rows.length / 2)).length ≤ 2 ^ bits := by
  have upper : rows.length ≤ 2 ^ bits * 2 := by simpa [Nat.pow_succ] using bound
  simp only [List.length_take, List.length_drop]
  omega

/-- Actual successful compilation gives logarithmic tree depth for every table order. -/
theorem build_depth (fuel : Nat) (rows : List (Entry Payload)) (tree : Tree Payload)
    (success : build fuel rows = some tree) (bits : Nat) (bound : rows.length ≤ 2 ^ bits) :
    depth tree ≤ bits := by
  induction fuel generalizing rows tree bits with
  | zero => simp [build] at success
  | succ fuel ih => cases rows with
    | nil => simp [build] at success
    | cons first rest => cases rest with
      | nil =>
          have same : tree = .leaf first := by simpa [build] using success.symm
          subst tree
          simp [depth]
      | cons second rest =>
          let rows := first :: second :: rest
          let cut := rows.length / 2
          change rows.length ≤ 2 ^ bits at bound
          cases bits with
          | zero => simp [rows] at bound
          | succ bits =>
              have halves := half_lengths rows bits bound
              change ((build fuel (rows.take cut)).bind fun low =>
                (build fuel (rows.drop cut)).bind fun high =>
                  (rows.drop cut).head?.bind fun pivot => some (Tree.split pivot.1 low high)) = some tree at success
              cases lowFound : build fuel (rows.take cut) with
              | none => simp [lowFound] at success
              | some low => cases highFound : build fuel (rows.drop cut) with
                | none => simp [lowFound, highFound] at success
                | some high => cases firstFound : (rows.drop cut).head? with
                  | none => simp [lowFound, highFound, firstFound] at success
                  | some pivot =>
                      have same : tree = .split pivot.1 low high := by
                        simpa only [lowFound, highFound, firstFound,
                          Option.bind_some, Option.some.injEq] using success.symm
                      subst tree
                      exact Nat.succ_le_succ (Nat.max_le.mpr
                        ⟨ih _ low lowFound bits halves.1, ih _ high highFound bits halves.2⟩)

/-- A compiled table with at most 2^bits entries needs at most bits comparisons. -/
theorem compiled_comparisons (fuel : Nat) (rows : List (Entry Payload)) (tree : Tree Payload)
    (success : build fuel rows = some tree) (bits : Nat) (bound : rows.length ≤ 2 ^ bits) (rank : Nat) :
    (measured tree rank).2 ≤ bits :=
  Nat.le_trans (measured_le_depth tree rank) (build_depth fuel rows tree success bits bound)

/-- The least nonnegative power-of-two exponent that covers an entry count. -/
def ceilLog2 (count : Nat) : Nat := if count ≤ 1 then 0 else (count - 1).log2 + 1

/-- The computed exponent covers the complete table. -/
theorem ceilLog2_covers (count : Nat) : count ≤ 2 ^ ceilLog2 count := by
  by_cases small : count ≤ 1
  · simp [ceilLog2, small]
  · have strict := Nat.lt_log2_self (n := count - 1)
    simp only [ceilLog2, small, ↓reduceIte]
    omega

/-- No smaller power-of-two exponent covers the entry count. -/
theorem ceilLog2_le (count bits : Nat) (bound : count ≤ 2 ^ bits) : ceilLog2 count ≤ bits := by
  by_cases small : count ≤ 1
  · simp [ceilLog2, small]
  · have nonzero : count - 1 ≠ 0 := by omega
    have strict : count - 1 < 2 ^ bits := by omega
    have logarithm := (Nat.log2_lt nonzero).mpr strict
    simp only [ceilLog2, small, ↓reduceIte]
    omega

/-- Successful compilation has the explicit ceiling-logarithm depth bound. -/
theorem build_depth_logarithmic (fuel : Nat) (rows : List (Entry Payload)) (tree : Tree Payload)
    (success : build fuel rows = some tree) : depth tree ≤ ceilLog2 rows.length :=
  build_depth fuel rows tree success _ (ceilLog2_covers rows.length)

/-- Every compiled lookup has the explicit ceiling-logarithm comparison bound. -/
theorem compiled_logarithmic (fuel : Nat) (rows : List (Entry Payload)) (tree : Tree Payload)
    (success : build fuel rows = some tree) (rank : Nat) :
    (measured tree rank).2 ≤ ceilLog2 rows.length :=
  compiled_comparisons fuel rows tree success _ (ceilLog2_covers rows.length) rank

/-- Any binary decision tree of this depth has room for at most this many entries. -/
theorem leaves_le_power (tree : Tree Payload) : (leaves tree).length ≤ 2 ^ depth tree := by
  induction tree with
  | leaf entry => simp [leaves, depth]
  | split pivot low high ihl ihr =>
      have leftPower := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_left (depth low) (depth high))
      have rightPower := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_right (depth low) (depth high))
      have leftBound := Nat.le_trans ihl leftPower
      have rightBound := Nat.le_trans ihr rightPower
      simp only [leaves, List.length_append, depth, Nat.pow_succ]
      omega

/-- The compiled ordered table attains the minimum possible maximum comparison depth. -/
theorem build_depth_exact (fuel : Nat) (rows : List (Entry Payload)) (tree : Tree Payload)
    (success : build fuel rows = some tree) (sorted : rows.Pairwise (fun a b => a.1 < b.1)) :
    depth tree = ceilLog2 rows.length := by
  apply Nat.le_antisymm (build_depth_logarithmic fuel rows tree success)
  have same := (build_spec fuel rows tree success sorted).1
  exact ceilLog2_le rows.length (depth tree) (by simpa [same] using leaves_le_power tree)

/-- The source compiler yields the correct selected offset within the proved lookup cost. -/
theorem compiled_exact_with_cost (rows : List (Entry Payload))
    (sorted : rows.Pairwise (fun a b => a.1 < b.1)) (rank : Nat)
    (eligible : reference rows rank ≠ none) :
    ∃ tree, build rows.length rows = some tree ∧
      some (measured tree rank).1 = reference rows rank ∧
      (measured tree rank).2 ≤ ceilLog2 rows.length := by
  obtain ⟨tree, built, correct⟩ := compiled_exact rows sorted rank eligible
  exact ⟨tree, built, by simpa [measured_result] using correct,
    compiled_logarithmic rows.length rows tree built rank⟩

/-- Only positive-cardinality source branches occupy the dispatch table. -/
def positiveCount (parts : List (Nat × Payload)) : Nat :=
  (parts.filter fun part => decide (0 < part.1)).length

/-- The actual cumulative-offset builder emits exactly one entry per positive branch. -/
theorem offsets_length (parts : List (Nat × Payload)) (offset : Nat) :
    (offsetParts offset parts).length = positiveCount parts := by
  induction parts generalizing offset with
  | nil => simp [offsetParts, positiveCount]
  | cons part rest ih =>
      rcases part with ⟨count, payload⟩
      by_cases positive : 0 < count <;> simp [offsetParts, positiveCount, positive, ih]

/-- Concrete source alternatives compile to the exact branch and local rank within logarithmic cost. -/
theorem source_dispatch_with_cost (parts : List (Nat × Payload)) (rank : Nat) (valid : rank < total parts) :
    ∃ tree, build (offsetParts 0 parts).length (offsetParts 0 parts) = some tree ∧
      some ((measured tree rank).1.2, rank - (measured tree rank).1.1) = locate parts rank ∧
      (measured tree rank).2 ≤ ceilLog2 (positiveCount parts) := by
  obtain ⟨tree, built, correct⟩ := source_dispatch_exact parts rank valid
  refine ⟨tree, built, ?_, ?_⟩
  · simpa only [measured_result] using correct
  · simpa only [offsets_length] using compiled_logarithmic _ (offsetParts 0 parts) tree built rank

/-- The actual source table has the minimum possible maximum dispatch depth. -/
theorem source_dispatch_depth (parts : List (Nat × Payload)) (rank : Nat) (valid : rank < total parts) :
    ∃ tree, build (offsetParts 0 parts).length (offsetParts 0 parts) = some tree ∧
      depth tree = ceilLog2 (positiveCount parts) := by
  obtain ⟨tree, built, _⟩ := source_dispatch_exact parts rank valid
  refine ⟨tree, built, ?_⟩
  simpa only [offsets_length] using build_depth_exact _ (offsetParts 0 parts) tree built (offsets_sorted parts 0)

/-- A source choice with at most 2^bits positive alternatives needs at most bits comparisons. -/
theorem source_dispatch_bits (parts : List (Nat × Payload)) (rank : Nat) (valid : rank < total parts)
    (bits : Nat) (bound : positiveCount parts ≤ 2 ^ bits) :
    ∃ tree, build (offsetParts 0 parts).length (offsetParts 0 parts) = some tree ∧
      some ((measured tree rank).1.2, rank - (measured tree rank).1.1) = locate parts rank ∧
      (measured tree rank).2 ≤ bits := by
  obtain ⟨tree, built, correct, cost⟩ := source_dispatch_with_cost parts rank valid
  exact ⟨tree, built, correct, Nat.le_trans cost (ceilLog2_le _ bits bound)⟩

end MicroCFTA.DecoderDispatchCost
