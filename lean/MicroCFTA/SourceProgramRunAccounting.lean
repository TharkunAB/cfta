import MicroCFTA.Cache

/-!
# Current program-run marks and Walk listing counts

The input is a completed finite run list and its completed program decoder.
One optional program remains for each typed run. Walk adds a separate
counting marker before each run's representative expansions. Listing stops
at the next proposal and returns the exact unused tail.

This module does not prove enumeration or type erasure correctness. It does
not model GHC token forcing, wall-clock interruption, or machine Int wrap.
-/
namespace MicroCFTA.SourceProgramRunAccounting
variable {Program Run Representative Token : Type}

/-- Mark repeated programs without removing their typed-run positions. -/
def mark [DecidableEq Program] (seen : List Program) : List Program → List (Option Program)
  | [] => []
  | program :: rest =>
      if program ∈ seen then none :: mark seen rest
      else some program :: mark (program :: seen) rest

/-- Every completed typed run retains exactly one output position. -/
theorem mark_length [DecidableEq Program] (seen programs : List Program) :
    (mark seen programs).length = programs.length := by
  induction programs generalizing seen with
  | nil => rfl
  | cons program rest ih => simp only [mark]; split <;> simp only [List.length_cons, ih]

/-- Only membership in the source seen set affects the remaining marks. -/
theorem mark_congr [DecidableEq Program] (first second : List Program) (programs : List Program)
    (same : ∀ program, program ∈ first ↔ program ∈ second) : mark first programs = mark second programs := by
  induction programs generalizing first second with
  | nil => rfl
  | cons program rest ih =>
      by_cases present : program ∈ first
      · simp only [mark, present, (same program).mp present, ↓reduceIte]
        exact congrArg (none :: ·) (ih first second same)
      · have absent : program ∉ second := fun member => present ((same program).mpr member)
        simp only [mark, present, absent, ↓reduceIte]
        exact congrArg (some program :: ·) (ih (program :: first) (program :: second)
          (fun other => by simp only [List.mem_cons, same]))

/-- Completed run prefixes update seen membership before the suffix starts. -/
theorem mark_append [DecidableEq Program] (seen first second : List Program) :
    mark seen (first ++ second) = mark seen first ++ mark (seen ++ first) second := by
  induction first generalizing seen with
  | nil => simp only [List.nil_append, mark, List.append_nil]
  | cons program rest ih =>
      by_cases present : program ∈ seen
      · simp only [List.cons_append, mark, present, ↓reduceIte, ih]
        have same : ∀ other, other ∈ seen ++ rest ↔ other ∈ seen ++ program :: rest := by
          intro other
          simp only [List.mem_append, List.mem_cons]
          constructor
          · rintro (known | later)
            · exact Or.inl known
            · exact Or.inr (Or.inr later)
          · rintro (known | equal | later)
            · exact Or.inl known
            · subst other; exact Or.inl present
            · exact Or.inr later
        rw [mark_congr (seen ++ rest) (seen ++ program :: rest) second same]
      · simp only [List.cons_append, mark, present, ↓reduceIte, ih]
        have same : ∀ other, other ∈ (program :: seen) ++ rest ↔ other ∈ seen ++ program :: rest := by
          intro other
          simp only [List.mem_append, List.mem_cons]
          constructor
          · rintro ((equal | known) | later)
            · exact Or.inr (Or.inl equal)
            · exact Or.inl known
            · exact Or.inr (Or.inr later)
          · rintro (known | equal | later)
            · exact Or.inl (Or.inr known)
            · exact Or.inl (Or.inl equal)
            · exact Or.inr later
        have equal := mark_congr ((program :: seen) ++ rest) (seen ++ program :: rest) second same
        simp only [List.cons_append] at equal
        rw [equal]

/-- The run at an exact position is emitted only on its first occurrence. -/
theorem first_occurrence [DecidableEq Program] (seen earlier : List Program) (program : Program) (rest : List Program) :
    (mark seen (earlier ++ program :: rest))[earlier.length]? =
      some (if program ∈ seen ∨ program ∈ earlier then none else some program) := by
  rw [mark_append]
  simp only [List.getElem?_append, mark_length, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self]
  simp only [mark, List.mem_append]
  split <;> rfl

/-- Optional run marks have exactly the original new-program membership. -/
theorem emitted_mem [DecidableEq Program] (seen programs : List Program) (program : Program) :
    program ∈ (mark seen programs).filterMap id ↔ program ∈ programs ∧ program ∉ seen := by
  induction programs generalizing seen with
  | nil => simp [mark]
  | cons first rest ih =>
      by_cases present : first ∈ seen
      · simp only [mark, present, ↓reduceIte, List.filterMap_cons, id_eq, ih, List.mem_cons]
        constructor
        · exact fun ⟨member, absent⟩ => ⟨Or.inr member, absent⟩
        · rintro ⟨equal | member, absent⟩
          · subst program; exact False.elim (absent present)
          · exact ⟨member, absent⟩
      · simp only [mark, present, ↓reduceIte, List.filterMap_cons, id_eq, List.mem_cons, ih]
        constructor
        · rintro (equal | ⟨member, absent⟩)
          · subst program; exact ⟨Or.inl rfl, present⟩
          · exact ⟨Or.inr member, fun known => absent (Or.inr known)⟩
        · rintro ⟨equal | member, absent⟩
          · exact Or.inl equal
          · by_cases equal : program = first
            · exact Or.inl equal
            · exact Or.inr ⟨member, fun known => known.elim equal absent⟩

/-- New program proposals are distinct even when the typed-run list repeats. -/
theorem emitted_nodup [DecidableEq Program] (seen programs : List Program) :
    ((mark seen programs).filterMap id).Nodup := by
  induction programs generalizing seen with
  | nil => simp [mark]
  | cons first rest ih =>
      by_cases present : first ∈ seen
      · simpa only [mark, present, ↓reduceIte, List.filterMap_cons, id_eq] using ih seen
      · simp only [mark, present, ↓reduceIte, List.filterMap_cons, id_eq, List.nodup_cons]
        exact ⟨fun member => (emitted_mem (first :: seen) rest first).mp member |>.2 List.mem_cons_self,
          ih (first :: seen)⟩

/-- Decode each completed source run, then mark programs from the empty seen set. -/
def programRuns [DecidableEq Program] (decode : Run → Program) (runs : List Run) : List (Option Program) :=
  mark [] (runs.map decode)

/-- Program deduplication keeps the full typed-run count. -/
theorem programRuns_length [DecidableEq Program] (decode : Run → Program) (runs : List Run) :
    (programRuns decode runs).length = runs.length := by simp only [programRuns, mark_length, List.length_map]

/-- Removing duplicate marks gives distinct programs in first-occurrence order. -/
theorem programRuns_nodup [DecidableEq Program] (decode : Run → Program) (runs : List Run) :
    ((programRuns decode runs).filterMap id).Nodup := emitted_nodup [] _

/-- Every decoded program is proposed at its first completed run, and none is added. -/
theorem programRuns_mem [DecidableEq Program] (decode : Run → Program) (runs : List Run) (program : Program) :
    program ∈ (programRuns decode runs).filterMap id ↔ ∃ run ∈ runs, decode run = program := by
  simpa only [programRuns, List.not_mem_nil, not_false_eq_true, and_true, List.mem_map] using
    emitted_mem [] (runs.map decode) program

/-- Count Nothing markers separately from actual program proposals. -/
def markers (items : List (Option Program)) : Nat := items.countP Option.isNone

/-- Every optional stream position is exactly one marker or one proposal. -/
theorem option_accounting (items : List (Option Program)) :
    markers items + (items.filterMap id).length = items.length := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [markers] at * <;> omega

/-- Duplicate run marks and new programs sum to the complete typed-run count. -/
theorem programRuns_accounting [DecidableEq Program] (decode : Run → Program) (runs : List Run) :
    markers (programRuns decode runs) + ((programRuns decode runs).filterMap id).length = runs.length := by
  rw [option_accounting, programRuns_length]

/-- Walk emits one fresh counting marker before each run's optional representative expansions. -/
def pack (expand : Representative → List Program) : List (Option Representative) → List (Option Program)
  | [] => []
  | none :: rest => none :: pack expand rest
  | some representative :: rest => none :: (expand representative).map some ++ pack expand rest

/-- Each typed run contributes exactly one Walk counting marker, including duplicate programs. -/
theorem pack_markers (expand : Representative → List Program) (runs : List (Option Representative)) :
    markers (pack expand runs) = runs.length := by
  induction runs with
  | nil => rfl
  | cons run rest ih => cases run <;> simp [pack, markers, List.countP_append, List.countP_map, Function.comp_def] at * <;> assumption

/-- Walk expansion preserves source representative order and all expansion occurrences. -/
theorem pack_proposals (expand : Representative → List Program) (runs : List (Option Representative)) :
    (pack expand runs).filterMap id = (runs.filterMap id).flatMap expand := by
  induction runs with
  | nil => rfl
  | cons run rest ih => cases run <;> simp [pack, List.filterMap_append, ih]

/-- Walk has one counting marker for each original typed run before representative expansion. -/
theorem packed_run_markers [DecidableEq Representative] (decode : Run → Representative)
    (expand : Representative → List Program) (runs : List Run) :
    markers (pack expand (programRuns decode runs)) = runs.length := by
  rw [pack_markers, programRuns_length]

/-- The actual next-program read counts preceding markers and keeps the exact unused tail. -/
def nextProgram (unprefix : Program → Program) (preorder : Program → List Token) (listed : Nat) :
    List (Option Program) → Nat × Option (Program × List Token × List (Option Program))
  | [] => (listed, none)
  | none :: rest => nextProgram unprefix preorder (listed + 1) rest
  | some representative :: rest =>
      let program := unprefix representative
      (listed, some (program, preorder program, rest))

/-- A completed read consumes exactly its preceding counting markers. -/
theorem nextProgram_prefix (unprefix : Program → Program) (preorder : Program → List Token)
    (listed count : Nat) (program : Program) (rest : List (Option Program)) :
    nextProgram unprefix preorder listed (List.replicate count none ++ some program :: rest) =
      (listed + count, some (unprefix program, preorder (unprefix program), rest)) := by
  induction count generalizing listed with
  | zero => simp [nextProgram]
  | succ count ih => simpa only [List.replicate_succ, List.cons_append, nextProgram, Nat.add_assoc,
      (Nat.add_comm 1 count)] using ih (listed + 1)

/-- A final marker-only suffix still contributes to the listed-run count. -/
theorem nextProgram_exhausted (unprefix : Program → Program) (preorder : Program → List Token)
    (listed count : Nat) : nextProgram unprefix preorder listed (List.replicate count none) = (listed + count, none) := by
  induction count generalizing listed with
  | zero => simp [nextProgram]
  | succ count ih => simpa only [List.replicate_succ, nextProgram, Nat.add_assoc,
      (Nat.add_comm 1 count)] using ih (listed + 1)

/-- Every actual proposal read identifies its source occurrence and exact untouched suffix. -/
theorem nextProgram_found (unprefix : Program → Program) (preorder : Program → List Token)
    (listed : Nat) (items : List (Option Program)) (count : Nat) (program : Program)
    (tokens : List Token) (rest : List (Option Program))
    (done : nextProgram unprefix preorder listed items = (count, some (program, tokens, rest))) :
    ∃ skipped representative, items = List.replicate skipped none ++ some representative :: rest ∧
      count = listed + skipped ∧ program = unprefix representative ∧ tokens = preorder program := by
  induction items generalizing listed with
  | nil => cases done
  | cons item items ih =>
      cases item with
      | none =>
          obtain ⟨skipped, representative, shape, total, output, tokenShape⟩ := ih (listed + 1) done
          refine ⟨skipped + 1, representative, ?_, by omega, output, tokenShape⟩
          simpa only [List.replicate_succ, List.cons_append] using congrArg (none :: ·) shape
      | some representative =>
          have equal : listed = count ∧ unprefix representative = program ∧
              preorder (unprefix representative) = tokens ∧ items = rest := by
            simpa only [nextProgram, Prod.mk.injEq, Option.some.injEq] using done
          rcases equal with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨0, representative, rfl, by omega, rfl, rfl⟩

/-- One read cannot count more markers than the completed supplied suffix contains. -/
theorem nextProgram_bound (unprefix : Program → Program) (preorder : Program → List Token)
    (listed : Nat) (items : List (Option Program)) :
    (nextProgram unprefix preorder listed items).1 ≤ listed + markers items := by
  induction items generalizing listed with
  | nil => simp [nextProgram, markers]
  | cons item rest ih =>
      cases item with
      | none => simpa [nextProgram, markers, List.countP_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (listed + 1)
      | some program => simp [nextProgram, markers]

/-- A completed Walk read counts at most the original typed-run list, independent of expansions. -/
theorem nextProgram_run_bound [DecidableEq Representative] (decode : Run → Representative)
    (expand : Representative → List Program) (unprefix : Program → Program)
    (preorder : Program → List Token) (runs : List Run) :
    (nextProgram unprefix preorder 0 (pack expand (programRuns decode runs))).1 ≤ runs.length := by
  simpa only [packed_run_markers, Nat.zero_add] using
    nextProgram_bound unprefix preorder 0 (pack expand (programRuns decode runs))

/-- The source checks its program cap before it requests another listing result. -/
def limitedNext (limit : Option Nat) (checked : Nat) (unprefix : Program → Program)
    (preorder : Program → List Token) (items : List (Option Program)) :
    Option (Nat × Option (Program × List Token × List (Option Program))) :=
  if limit.any (fun bound => decide (bound ≤ checked)) then none
  else some (nextProgram unprefix preorder 0 items)

/-- Reaching the cap leaves all later counting markers and proposals outside this step. -/
theorem limitedNext_stop (bound checked : Nat) (unprefix : Program → Program)
    (preorder : Program → List Token) (items : List (Option Program)) (reached : bound ≤ checked) :
    limitedNext (some bound) checked unprefix preorder items = none := by simp [limitedNext, reached]

end MicroCFTA.SourceProgramRunAccounting
