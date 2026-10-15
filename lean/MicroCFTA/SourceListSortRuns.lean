import MicroCFTA.SourceListSortMerge

/-!
# Natural runs of the installed source sortBy

Descending runs use the source reversed list. Ascending runs retain its
function accumulator. Every finite input produces a nonempty run list.
-/
namespace MicroCFTA.SourceListSort

mutual
/-- Detect source ascending or descending runs from each first pair. -/
def sequences (gt : Item → Item → Bool) : List Item → List (List Item)
  | a :: b :: rest => if gt a b then descending gt b [a] rest else ascending gt b (a :: ·) rest
  | rest => [rest]
termination_by rest => 2 * rest.length

/-- Accumulate a strictly descending source run in reverse order. -/
def descending (gt : Item → Item → Bool) (last : Item) (reversed rest : List Item) : List (List Item) :=
  match rest with
  | [] => (last :: reversed) :: sequences gt []
  | b :: rest =>
      if gt last b then descending gt b (last :: reversed) rest
      else (last :: reversed) :: sequences gt (b :: rest)
termination_by 2 * rest.length + 1

/-- Accumulate a nondecreasing source run with the original function accumulator. -/
def ascending (gt : Item → Item → Bool) (last : Item) (initial : List Item → List Item) (rest : List Item) : List (List Item) :=
  match rest with
  | [] => initial [last] :: sequences gt []
  | b :: rest =>
      if !(gt last b) then ascending gt b (fun suffix => initial (last :: suffix)) rest
      else initial [last] :: sequences gt (b :: rest)
termination_by 2 * rest.length + 1
end

mutual
/-- Natural-run detection preserves the count of each original occurrence. -/
theorem sequences_count [DecidableEq Item] (gt : Item → Item → Bool) (input : List Item) (item : Item) :
    (sequences gt input).flatten.count item = input.count item := by
  cases input with
  | nil => simp [sequences]
  | cons a rest =>
      cases rest with
      | nil => simp [sequences]
      | cons b rest =>
          rw [sequences]
          split
          · rw [descending_count gt b [a] rest item]
            simp only [List.count_cons, List.count_nil]
            omega
          · rw [ascending_count gt b (a :: ·) rest item [a] (by intro suffix; rfl)]
            simp only [List.count_cons, List.count_nil]
            omega
termination_by 2 * input.length

/-- A reversed descending accumulator retains every original occurrence. -/
theorem descending_count [DecidableEq Item] (gt : Item → Item → Bool) (last : Item) (reversed rest : List Item) (item : Item) :
    (descending gt last reversed rest).flatten.count item = [last].count item + reversed.count item + rest.count item := by
  cases rest with
  | nil => simp only [descending, sequences, List.flatten_cons, List.flatten_nil, List.append_nil, List.count_cons, List.count_nil]; omega
  | cons b rest =>
      rw [descending]
      split
      · rw [descending_count gt b (last :: reversed) rest item]
        simp only [List.count_cons, List.count_nil]
        omega
      · simp only [List.flatten_cons, List.count_append]
        rw [sequences_count gt (b :: rest) item]
        simp only [List.count_cons, List.count_nil]
        omega
termination_by 2 * rest.length + 1

/-- A source ascending function accumulator retains its exact finite prefix and all later occurrences. -/
theorem ascending_count [DecidableEq Item] (gt : Item → Item → Bool) (last : Item)
    (append : List Item → List Item) (rest : List Item) (item : Item) (initial : List Item)
    (exact : ∀ suffix, append suffix = initial ++ suffix) :
    (ascending gt last append rest).flatten.count item = initial.count item + [last].count item + rest.count item := by
  cases rest with
  | nil => simp [ascending, exact, sequences, List.count_cons, List.count_nil]
  | cons b rest =>
      rw [ascending]
      split
      · have next : ∀ suffix, append (last :: suffix) = (initial ++ [last]) ++ suffix := by
          intro suffix
          rw [exact]
          simp only [List.append_assoc, List.singleton_append]
        rw [ascending_count gt b (fun suffix => append (last :: suffix)) rest item (initial ++ [last]) next]
        simp only [List.count_append, List.count_cons, List.count_nil]
        omega
      · simp only [List.flatten_cons, List.count_append]
        rw [sequences_count gt (b :: rest) item, exact]
        simp only [List.count_append, List.count_cons, List.count_nil]
termination_by 2 * rest.length + 1
end

mutual
/-- Natural-run detection always supplies at least one run to the source merge loop. -/
theorem sequences_nonempty (gt : Item → Item → Bool) (input : List Item) : sequences gt input ≠ [] := by
  cases input with
  | nil => simp [sequences]
  | cons a rest =>
      cases rest with
      | nil => simp [sequences]
      | cons b rest =>
          rw [sequences]
          split
          · exact descending_nonempty gt b [a] rest
          · exact ascending_nonempty gt b (a :: ·) rest
/-- Every source descending scan produces a nonempty run list. -/
theorem descending_nonempty (gt : Item → Item → Bool) (last : Item) (reversed rest : List Item) :
    descending gt last reversed rest ≠ [] := by
  cases rest with
  | nil => simp [descending]
  | cons b rest =>
      rw [descending]
      split
      · exact descending_nonempty gt b (last :: reversed) rest
      · simp
termination_by 2 * rest.length + 1

/-- Every source ascending scan produces a nonempty run list. -/
theorem ascending_nonempty (gt : Item → Item → Bool) (last : Item) (initial : List Item → List Item) (rest : List Item) :
    ascending gt last initial rest ≠ [] := by
  cases rest with
  | nil => simp [ascending]
  | cons b rest =>
      rw [ascending]
      split
      · exact ascending_nonempty gt b (fun suffix => initial (last :: suffix)) rest
      · simp
termination_by 2 * rest.length + 1
end

end MicroCFTA.SourceListSort
