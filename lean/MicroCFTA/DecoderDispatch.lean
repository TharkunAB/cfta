import MicroCFTA.Decoder

/-!
# Compiled offset-table dispatch

The source compiles an ordered offset map into a binary decision tree. Each
split uses half the entries and the first offset in the upper half. Leaves
rebase the rank before calling the selected branch decoder.
-/
namespace MicroCFTA.DecoderDispatch

/-- A branch begins at its cumulative offset. The payload is its decoder. -/
abbrev Entry (Payload : Type) := Nat × Payload

/-- The compiled source closure structure. -/
inductive Tree (Payload : Type) where
  | leaf (entry : Entry Payload)
  | split (pivot : Nat) (low high : Tree Payload)

/-- Preserve table order when reading the compiled branches. -/
def leaves : Tree Payload → List (Entry Payload)
  | .leaf entry => [entry]
  | .split _ low high => leaves low ++ leaves high

/-- Select one compiled branch without rebuilding any table. -/
def select : Tree Payload → Nat → Entry Payload
  | .leaf entry, _ => entry
  | .split pivot low high, rank => if rank < pivot then select low rank else select high rank

/-- The source leaf passes the offset-subtracted rank to its branch decoder. -/
def decode (tree : Tree (Nat → Value)) (rank : Nat) : Value :=
  let entry := select tree rank
  entry.2 (rank - entry.1)

/-- Compile both halves once. Empty tables and insufficient execution fuel fail. -/
def build : Nat → List (Entry Payload) → Option (Tree Payload)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [entry] => some (.leaf entry)
  | fuel + 1, rows@(_ :: _ :: _) => do
      let cut := rows.length / 2
      let low ← build fuel (rows.take cut)
      let high ← build fuel (rows.drop cut)
      let first ← (rows.drop cut).head?
      pure (.split first.1 low high)

/-- The independent specification selects the last eligible table offset. -/
def reference (rows : List (Entry Payload)) (rank : Nat) : Option (Entry Payload) :=
  (rows.filter (fun entry => decide (entry.1 ≤ rank))).getLast?

/-- The invariant needed by a compiled pivot, derived below from sorted offsets. -/
def Ordered : Tree Payload → Prop
  | .leaf _ => True
  | .split pivot low high =>
      Ordered low ∧ Ordered high ∧
      (∀ entry ∈ leaves low, entry.1 < pivot) ∧
      (∀ entry ∈ leaves high, pivot ≤ entry.1) ∧
      ∃ entry ∈ leaves high, entry.1 = pivot

private theorem reference_append (low high : List (Entry Payload)) (rank : Nat) :
    reference (low ++ high) rank = (reference high rank).or (reference low rank) := by
  simp [reference, List.filter_append]

private theorem reference_none (rows : List (Entry Payload)) (rank : Nat) :
    reference rows rank = none ↔ ∀ entry ∈ rows, rank < entry.1 := by
  simp [reference]

/-- A compiled ordered tree returns exactly the last eligible offset whenever one exists. -/
theorem select_exact (tree : Tree Payload) (ordered : Ordered tree) (rank : Nat)
    (eligible : reference (leaves tree) rank ≠ none) :
    some (select tree rank) = reference (leaves tree) rank := by
  induction tree with
  | leaf entry =>
      by_cases fits : entry.1 ≤ rank
      · simp [select, leaves, reference, fits]
      · simp [leaves, reference, fits] at eligible
  | split pivot low high ihl ihr =>
      obtain ⟨ol, oh, below, above, first, member, atPivot⟩ := ordered
      by_cases left : rank < pivot
      · have empty : reference (leaves high) rank = none :=
          (reference_none _ _).mpr (fun entry member => by have := above entry member; omega)
        have valid : reference (leaves low) rank ≠ none := by
          simpa only [leaves, reference_append, empty, Option.none_or] using eligible
        simp only [select, left, ↓reduceIte, leaves, reference_append, empty, Option.none_or]
        exact ihl ol valid
      · have valid : reference (leaves high) rank ≠ none := by
          intro absent
          have impossible := (reference_none _ _).mp absent first member
          omega
        have chosen := ihr oh valid
        simp only [select, left, ↓reduceIte, leaves, reference_append, ← chosen, Option.some_or]

/-- Successful compilation preserves every table entry, its order, and its pivot invariant. -/
theorem build_spec (fuel : Nat) (rows : List (Entry Payload)) (tree : Tree Payload)
    (success : build fuel rows = some tree) (sorted : rows.Pairwise (fun a b => a.1 < b.1)) :
    leaves tree = rows ∧ Ordered tree := by
  induction fuel generalizing rows tree with
  | zero => simp [build] at success
  | succ fuel ih => cases rows with
    | nil => simp [build] at success
    | cons first rest => cases rest with
      | nil =>
          have same : tree = .leaf first := by simpa [build] using success.symm
          subst tree
          simp [leaves, Ordered]
      | cons second rest =>
          let rows := first :: second :: rest
          let cut := rows.length / 2
          change rows.Pairwise (fun a b => a.1 < b.1) at sorted
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
                  obtain ⟨lowRows, lowOrder⟩ := ih _ low lowFound sorted.take
                  obtain ⟨highRows, highOrder⟩ := ih _ high highFound sorted.drop
                  have joined : rows.take cut ++ rows.drop cut = rows := List.take_append_drop ..
                  have cross := (List.pairwise_append.mp (joined.symm ▸ sorted)).2.2
                  have pivotMember := List.mem_of_head? firstFound
                  obtain ⟨tail, highEq⟩ := List.head?_eq_some_iff.mp firstFound
                  have tailOrder := List.pairwise_cons.mp (highEq ▸ sorted.drop)
                  constructor
                  · simpa only [leaves, lowRows, highRows] using joined
                  · refine ⟨lowOrder, highOrder, ?_, ?_, ?_⟩
                    · simpa only [lowRows] using fun entry member => cross entry member pivot pivotMember
                    · rw [highRows, highEq]
                      intro entry member
                      rcases List.mem_cons.mp member with rfl | member
                      · exact Nat.le_refl _
                      · exact Nat.le_of_lt (tailOrder.1 entry member)
                    · exact ⟨pivot, highRows ▸ pivotMember, rfl⟩

/-- Every nonempty table compiles with a finite bound derived from its own length. -/
theorem build_total (rows : List (Entry Payload)) (nonempty : rows ≠ []) (fuel : Nat)
    (enough : rows.length ≤ fuel) : ∃ tree, build fuel rows = some tree := by
  induction fuel generalizing rows with
  | zero => have := List.length_pos_iff.mpr nonempty; omega
  | succ fuel ih => cases rows with
    | nil => contradiction
    | cons first rest => cases rest with
      | nil => exact ⟨.leaf first, by simp [build]⟩
      | cons second rest =>
          let rows := first :: second :: rest
          let cut := rows.length / 2
          change rows.length ≤ fuel + 1 at enough
          have length : 2 ≤ rows.length := by simp [rows]
          have cutPos : 0 < cut := by dsimp [cut]; omega
          have cutLt : cut < rows.length := Nat.div_lt_self (by omega) (by decide)
          have lowLength : (rows.take cut).length = cut := by simp [Nat.min_eq_left (Nat.le_of_lt cutLt)]
          have highLength : (rows.drop cut).length = rows.length - cut := by simp
          obtain ⟨low, lowFound⟩ := ih (rows.take cut) (by intro empty; simp [empty] at lowLength; omega) (by rw [lowLength]; omega)
          obtain ⟨high, highFound⟩ := ih (rows.drop cut) (by intro empty; simp [empty] at highLength; omega) (by rw [highLength]; omega)
          cases firstFound : (rows.drop cut).head? with
          | none => have absent := List.head?_eq_none_iff.mp firstFound; simp [absent] at highLength; omega
          | some pivot =>
              exact ⟨.split pivot.1 low high, by
                change ((build fuel (rows.take cut)).bind fun low =>
                  (build fuel (rows.drop cut)).bind fun high =>
                    (rows.drop cut).head?.bind fun pivot => some (Tree.split pivot.1 low high)) = _
                simp only [lowFound, highFound, firstFound, Option.bind_some]⟩

/-- Balanced table compilation and selection implement ordered offset lookup. -/
theorem compiled_exact (rows : List (Entry Payload)) (sorted : rows.Pairwise (fun a b => a.1 < b.1))
    (rank : Nat) (eligible : reference rows rank ≠ none) :
    ∃ tree, build rows.length rows = some tree ∧ some (select tree rank) = reference rows rank := by
  have nonempty : rows ≠ [] := by intro empty; simp [empty, reference] at eligible
  obtain ⟨tree, built⟩ := build_total rows nonempty rows.length (Nat.le_refl _)
  obtain ⟨same, ordered⟩ := build_spec _ rows tree built sorted
  exact ⟨tree, built, by simpa only [same] using select_exact tree ordered rank (by simpa only [same] using eligible)⟩

/-- Source cumulative offsets omit zero-count branches. -/
def offsetParts (offset : Nat) : List (Nat × Payload) → List (Entry Payload)
  | [] => []
  | (count, payload) :: rest =>
      if 0 < count then (offset, payload) :: offsetParts (offset + count) rest
      else offsetParts offset rest

/-- The source's mathematical total does not enumerate any branch values. -/
def total (parts : List (Nat × Payload)) : Nat := (parts.map Prod.fst).sum

/-- Independent linear specification of the branch and its rebased rank. -/
def locate : List (Nat × Payload) → Nat → Option (Payload × Nat)
  | [], _ => none
  | (count, payload) :: rest, rank =>
      if rank < count then some (payload, rank) else locate rest (rank - count)

/-- Every valid rank selects a branch even when zero-count branches occur. -/
theorem locate_total (parts : List (Nat × Payload)) (rank : Nat) (valid : rank < total parts) :
    locate parts rank ≠ none := by
  induction parts generalizing rank with
  | nil => simp [total] at valid
  | cons part rest ih =>
      rcases part with ⟨count, payload⟩
      by_cases here : rank < count
      · simp [locate, here]
      · simp only [locate, here, ↓reduceIte]
        apply ih
        change rank < count + total rest at valid
        omega

/-- Every emitted offset is at least the incoming cumulative offset. -/
theorem offsets_lower (parts : List (Nat × Payload)) (offset : Nat)
    (entry : Entry Payload) (member : entry ∈ offsetParts offset parts) : offset ≤ entry.1 := by
  induction parts generalizing offset with
  | nil => simp [offsetParts] at member
  | cons part rest ih =>
      rcases part with ⟨count, payload⟩
      by_cases positive : 0 < count
      · simp only [offsetParts, positive, ↓reduceIte, List.mem_cons] at member
        rcases member with rfl | member
        · exact Nat.le_refl _
        · have := ih (offset + count) member; omega
      · exact ih offset (by simpa [offsetParts, positive] using member)

/-- The actual offset builder supplies the strict map ordering required by dispatch. -/
theorem offsets_sorted (parts : List (Nat × Payload)) (offset : Nat) :
    (offsetParts offset parts).Pairwise (fun a b => a.1 < b.1) := by
  induction parts generalizing offset with
  | nil => simp [offsetParts]
  | cons part rest ih =>
      rcases part with ⟨count, payload⟩
      by_cases positive : 0 < count
      · simp only [offsetParts, positive, ↓reduceIte, List.pairwise_cons]
        refine ⟨?_, ih _⟩
        intro entry member
        have := offsets_lower rest (offset + count) entry member
        omega
      · simpa [offsetParts, positive] using ih offset

private theorem reference_cons (entry : Entry Payload) (rows : List (Entry Payload)) (rank : Nat) :
    reference (entry :: rows) rank =
      (reference rows rank).or (if entry.1 ≤ rank then some entry else none) := by
  simp [reference]

/-- Cumulative offset lookup has exactly the source branch and local rank. -/
theorem offsets_exact (parts : List (Nat × Payload)) (offset rank : Nat) (valid : rank < total parts) :
    (reference (offsetParts offset parts) (offset + rank)).map (fun entry => (entry.2, offset + rank - entry.1)) =
      locate parts rank := by
  induction parts generalizing offset rank with
  | nil => simp [total] at valid
  | cons part rest ih =>
      rcases part with ⟨count, payload⟩
      have totalEq : total ((count, payload) :: rest) = count + total rest := by simp [total]
      rw [totalEq] at valid
      by_cases positive : 0 < count
      · simp only [offsetParts, positive, ↓reduceIte, reference_cons]
        have first : offset ≤ offset + rank := by omega
        simp only [first, ↓reduceIte]
        by_cases here : rank < count
        · have empty : reference (offsetParts (offset + count) rest) (offset + rank) = none := by
            apply (reference_none _ _).mpr
            intro entry member
            have := offsets_lower rest (offset + count) entry member
            omega
          simp [empty, locate, here]
        · have restValid : rank - count < total rest := by omega
          have restEq := ih (offset + count) (rank - count) restValid
          have indexEq : offset + count + (rank - count) = offset + rank := by omega
          rw [indexEq] at restEq
          cases found : reference (offsetParts (offset + count) rest) (offset + rank) with
          | none =>
              have impossible := locate_total rest (rank - count) restValid
              simp only [found, Option.map_none] at restEq
              exact False.elim (impossible restEq.symm)
          | some entry =>
              simpa only [found, Option.some_or, locate, here, ↓reduceIte] using restEq
      · have zero : count = 0 := by omega
        subst count
        simpa [offsetParts, locate] using ih offset rank (by simpa using valid)

/-- A valid source rank always reaches a table entry, including after empty branches are removed. -/
theorem offsets_eligible (parts : List (Nat × Payload)) (rank : Nat) (valid : rank < total parts) :
    reference (offsetParts 0 parts) rank ≠ none := by
  intro missing
  have exact := offsets_exact parts 0 rank valid
  simp only [Nat.zero_add, missing, Option.map_none] at exact
  exact locate_total parts rank valid exact.symm

/-- The source builder and compiled tree preserve every valid rank and its branch-local index. -/
theorem source_dispatch_exact (parts : List (Nat × Payload)) (rank : Nat) (valid : rank < total parts) :
    ∃ tree, build (offsetParts 0 parts).length (offsetParts 0 parts) = some tree ∧
      some ((select tree rank).2, rank - (select tree rank).1) = locate parts rank := by
  obtain ⟨tree, built, selected⟩ := compiled_exact _ (offsets_sorted parts 0) rank (offsets_eligible parts rank valid)
  refine ⟨tree, built, ?_⟩
  have exact := offsets_exact parts 0 rank valid
  simpa only [Nat.zero_add, ← selected, Option.map_some] using exact

/-- Every returned local rank lies inside the declared selected branch. -/
theorem locate_bounds (parts : List (Nat × Payload)) (rank localRank : Nat) (payload : Payload)
    (found : locate parts rank = some (payload, localRank)) :
    ∃ count, (count, payload) ∈ parts ∧ localRank < count := by
  induction parts generalizing rank with
  | nil => simp [locate] at found
  | cons first rest ih =>
      rcases first with ⟨count, value⟩
      by_cases here : rank < count
      · have same : (value, rank) = (payload, localRank) := by simpa [locate, here] using found
        cases same
        exact ⟨count, by simp, here⟩
      · obtain ⟨count, member, bound⟩ := ih (rank - count) (by simpa [locate, here] using found)
        exact ⟨count, by simp [member], bound⟩

/-- Every emitted offset is strictly below the final cumulative cardinality. -/
theorem offsets_upper (parts : List (Nat × Payload)) (offset : Nat)
    (entry : Entry Payload) (member : entry ∈ offsetParts offset parts) :
    entry.1 < offset + total parts := by
  induction parts generalizing offset with
  | nil => simp [offsetParts] at member
  | cons first rest ih =>
      rcases first with ⟨count, payload⟩
      have totalEq : total ((count, payload) :: rest) = count + total rest := by simp [total]
      rw [totalEq]
      by_cases positive : 0 < count
      · simp only [offsetParts, positive, ↓reduceIte, List.mem_cons] at member
        rcases member with rfl | member
        · omega
        · have := ih (offset + count) member; omega
      · have zero : count = 0 := by omega
        have := ih offset (by simpa [offsetParts, positive] using member)
        omega

/-- Each nonnegative branch count is bounded by the total count. -/
theorem count_le_total (parts : List (Nat × Payload)) (count : Nat) (payload : Payload)
    (member : (count, payload) ∈ parts) : count ≤ total parts := by
  induction parts with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | member
      · subst first
        simp [total]
      · have bound := ih member
        change count ≤ first.1 + total rest
        omega

/-- A checked small total bounds every stored offset and branch-local index. -/
theorem machine_bounds (parts : List (Nat × Payload)) (maximum rank : Nat)
    (fits : total parts ≤ maximum) (valid : rank < total parts) :
    rank < maximum ∧ (∀ entry ∈ offsetParts 0 parts, entry.1 < maximum) ∧
      ∀ payload localRank, locate parts rank = some (payload, localRank) → localRank < maximum := by
  refine ⟨by omega, ?_, ?_⟩
  · intro entry member
    have bound := offsets_upper parts 0 entry member
    omega
  · intro payload localRank found
    obtain ⟨count, member, bound⟩ := locate_bounds parts rank localRank payload found
    have countBound := count_le_total parts count payload member
    omega

/-- Independent concatenated values specify choice rank order. -/
theorem locate_lists (parts : List (List Value)) (rank : Nat) :
    (locate (parts.map (fun values => (values.length, values))) rank).bind
      (fun entry => entry.1[entry.2]?) = parts.flatten[rank]? := by
  induction parts generalizing rank with
  | nil => simp [locate]
  | cons first rest ih =>
      simp only [List.map_cons, locate, List.flatten_cons]
      by_cases here : rank < first.length
      · simp only [here, ↓reduceIte, Option.bind_some, List.getElem?_append_left here]
      · simp only [here, ↓reduceIte, ih]
        exact (List.getElem?_append_right (l₁ := first) (l₂ := rest.flatten) (i := rank) (by omega)).symm

/-- Compiled n-ary choice dispatch agrees with all concatenated members in source order. -/
theorem choice_decode (parts : List (List Value)) (rank : Nat) (valid : rank < parts.flatten.length) :
    let rows := offsetParts 0 (parts.map (fun values => (values.length, values)))
    ∃ tree, build rows.length rows = some tree ∧
      (select tree rank).2[rank - (select tree rank).1]? = parts.flatten[rank]? := by
  have totalEq : total (parts.map (fun values => (values.length, values))) = parts.flatten.length := by
    simp [total, List.length_flatten, Function.comp_def]
  obtain ⟨tree, built, selected⟩ := source_dispatch_exact (parts.map (fun values => (values.length, values))) rank (by rw [totalEq]; exact valid)
  refine ⟨tree, built, ?_⟩
  have exact := locate_lists parts rank
  rw [← selected] at exact
  exact exact

end MicroCFTA.DecoderDispatch
