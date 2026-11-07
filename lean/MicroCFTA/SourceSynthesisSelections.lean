import Std

/-!
# Ordered selections for the synthesis table

The list algorithms follow GHC 9.14.1, ghc-internal 9.1401.0.
See GHC.Internal.Data.OldList lines 1494–1504 and 1544–1592.
The source is installed with the compiler's HTML documentation.
The synthesis caller is Synthesis.hs lines 779–795.
The table key contains names. The last matching selection wins.
No distinct-name premise is required.
-/
set_option maxHeartbeats 2000000

namespace MicroCFTA.SourceSynthesisSelections

variable {α β : Type}

/-- The source's nonempty subsequence worker retains its fold order. -/
def nonEmptySubsequences : List α → List (List α)
  | [] => []
  | value :: rest => [value] ::
      (nonEmptySubsequences rest).foldr (fun selected later => selected :: (value :: selected) :: later) []

/-- The empty subsequence precedes the source's nonempty subsequences. -/
def subsequences (values : List α) : List (List α) := [] :: nonEmptySubsequences values

/-- The source interleave worker retains its prefix function and shared suffix. -/
def interleaveAux (value : α) (suffix : List α) (initial : List α → β) :
    List α → List β → List α × List β
  | [], later => (suffix, later)
  | first :: rest, later =>
      let result := interleaveAux value suffix (fun tail => initial (first :: tail)) rest later
      (first :: result.1, initial (value :: first :: result.1) :: result.2)

/-- Insert the selected value before each source prefix position. -/
def interleave (value : α) (suffix selected : List α) (later : List (List α)) : List (List α) :=
  (interleaveAux value suffix id selected later).2

mutual
  /-- The original list precedes the exact source permutation worker. -/
  def permutations (values : List α) : List (List α) := values :: perms values []
  termination_by (values.length, values.length + 1)
  decreasing_by all_goals simp_wf; omega

  /-- The source folds permutations of the reversed consumed prefix. -/
  def perms (suffix accumulated : List α) : List (List α) :=
    match suffix with
    | [] => []
    | value :: rest =>
        (permutations accumulated).foldr (interleave value rest) (perms rest (value :: accumulated))
  termination_by (suffix.length + accumulated.length, suffix.length)
  decreasing_by all_goals simp_wf; omega
end

/-- Enumerate ordered selections in the literal relevantTable insertion order. -/
def selections (arguments : List (String × α)) : List (List (String × α)) :=
  (subsequences arguments).flatMap permutations

/-- Read the last names-matching entry without evaluating earlier table values. -/
def lookupLast (names : List String) : List (List (String × α)) → Option (List (String × α))
  | [] => none
  | selected :: rest =>
      match lookupLast names rest with
      | some winner => some winner
      | none => if selected.map Prod.fst = names then some selected else none

/-- Resolve the same names-only key as the source LazyMap.fromList table. -/
def resolveSelection (arguments : List (String × α)) (names : List String) : Option (List (String × α)) :=
  lookupLast names (selections arguments)

theorem permutations_nil : permutations ([] : List α) = [[]] := by
  simp [permutations, perms]

theorem permutations_singleton (value : α) : permutations [value] = [[value]] := by
  simp [permutations, perms, interleave, interleaveAux]

/-- Two elements retain source order, followed by their exchange. -/
theorem permutations_two (first second : α) : permutations [first, second] = [[first, second], [second, first]] := by
  simp [permutations, perms, interleave, interleaveAux]

/-- Three elements exhibit the source's non-lexicographic order. -/
theorem permutations_three (a b c : α) :
    permutations [a, b, c] = [[a, b, c], [b, a, c], [c, b, a], [b, c, a], [c, a, b], [a, c, b]] := by
  simp [permutations, perms, interleave, interleaveAux]

theorem nil_mem_subsequences (values : List α) : [] ∈ subsequences values := List.mem_cons_self

private theorem fold_subsequences_mem (value : α) (entries : List (List α)) (selected : List α)
    (member : selected ∈ entries) :
    selected ∈ entries.foldr (fun chosen later => chosen :: (value :: chosen) :: later) [] ∧
    (value :: selected) ∈ entries.foldr (fun chosen later => chosen :: (value :: chosen) :: later) [] := by
  induction entries with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst selected
        exact ⟨List.mem_cons_self, List.mem_cons.mpr (.inr List.mem_cons_self)⟩
      · obtain ⟨without, withHead⟩ := ih later
        exact ⟨List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr without))),
          List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr withHead)))⟩

private theorem self_mem_nonEmpty (values : List α) (nonempty : values ≠ []) : values ∈ nonEmptySubsequences values := by
  induction values with
  | nil => exact (nonempty rfl).elim
  | cons first rest ih =>
      cases rest with
      | nil => exact List.mem_cons_self
      | cons second tail =>
          exact List.mem_cons.mpr (.inr
            (fold_subsequences_mem first _ _ (ih (by simp))).2)

/-- The full input is one actual source subsequence. -/
theorem self_mem_subsequences (values : List α) : values ∈ subsequences values := by
  cases values with
  | nil => exact List.mem_cons_self
  | cons first rest => exact List.mem_cons.mpr (.inr (self_mem_nonEmpty _ (by simp)))

theorem self_mem_permutations (values : List α) : values ∈ permutations values := by
  rw [permutations]
  exact List.mem_cons_self

/-- Every actual permutation of a source subsequence has a table entry. -/
theorem mem_selections (arguments subset selected : List (String × α))
    (subsequence : subset ∈ subsequences arguments) (permutation : selected ∈ permutations subset) :
    selected ∈ selections arguments := List.mem_flatMap.mpr ⟨subset, subsequence, permutation⟩

/-- Every full-input permutation requested at the root has a table entry. -/
theorem permutation_mem_selections (arguments selected : List (String × α))
    (member : selected ∈ permutations arguments) : selected ∈ selections arguments :=
  mem_selections arguments arguments selected (self_mem_subsequences arguments) member

theorem nil_mem_selections (arguments : List (String × α)) : [] ∈ selections arguments :=
  mem_selections arguments [] [] (nil_mem_subsequences arguments) (self_mem_permutations [])

/-- A returned winner is an actual source selection with exactly the requested names. -/
theorem lookupLast_spec (entries : List (List (String × α))) (names : List String)
    (winner : List (String × α)) (resolved : lookupLast names entries = some winner) :
    winner ∈ entries ∧ winner.map Prod.fst = names := by
  induction entries with
  | nil => cases resolved
  | cons first rest ih =>
      cases later : lookupLast names rest with
      | some found =>
          have same : found = winner := Option.some.inj (by simpa only [lookupLast, later] using resolved)
          subst winner
          obtain ⟨member, named⟩ := ih later
          exact ⟨List.mem_cons.mpr (.inr member), named⟩
      | none =>
          simp only [lookupLast, later] at resolved
          split at resolved
          · rename_i named
            have same := Option.some.inj resolved
            subst winner
            exact ⟨List.mem_cons_self, named⟩
          · cases resolved

/-- Names of any actual entry resolve even when several entries share the key. -/
theorem lookupLast_exists (entries : List (List (String × α))) (names : List String)
    (selected : List (String × α)) (member : selected ∈ entries) (named : selected.map Prod.fst = names) :
    ∃ winner, lookupLast names entries = some winner := by
  induction entries with
  | nil => cases member
  | cons first rest ih =>
      cases later : lookupLast names rest with
      | some winner => exact ⟨winner, by simp only [lookupLast, later]⟩
      | none =>
          rcases List.mem_cons.mp member with same | remaining
          · subst selected
            exact ⟨first, by simp only [lookupLast, later, named, ite_true]⟩
          · obtain ⟨winner, found⟩ := ih remaining
            rw [later] at found
            cases found

/-- Later source entries take priority over every earlier entry. -/
theorem lookupLast_append (names : List String) (earlier later : List (List (String × α))) :
    lookupLast names (earlier ++ later) =
      match lookupLast names later with
      | some winner => some winner
      | none => lookupLast names earlier := by
  induction earlier with
  | nil =>
      simp only [List.nil_append]
      cases lookupLast names later <;> simp only [lookupLast]
  | cons first rest ih =>
      simp only [List.cons_append, lookupLast, ih]
      cases lookupLast names later <;> rfl

/-- A resolved key retains the actual winning entry and its names. -/
theorem resolveSelection_spec (arguments : List (String × α)) (names : List String)
    (winner : List (String × α)) (resolved : resolveSelection arguments names = some winner) :
    winner ∈ selections arguments ∧ winner.map Prod.fst = names :=
  lookupLast_spec (selections arguments) names winner resolved

/-- Every actual selection key is present in the finite names-only table. -/
theorem resolveSelection_exists (arguments selected : List (String × α))
    (member : selected ∈ selections arguments) :
    ∃ winner, resolveSelection arguments (selected.map Prod.fst) = some winner :=
  lookupLast_exists (selections arguments) (selected.map Prod.fst) selected member rfl

/-- Every source root permutation has a defined lookup. -/
theorem root_lookup_exists (arguments selected : List (String × α))
    (member : selected ∈ permutations arguments) :
    ∃ winner, resolveSelection arguments (selected.map Prod.fst) = some winner :=
  resolveSelection_exists arguments selected (permutation_mem_selections arguments selected member)

/-- The empty key always resolves to the empty selection. -/
theorem resolveSelection_empty (arguments : List (String × α)) : resolveSelection arguments [] = some [] := by
  obtain ⟨winner, resolved⟩ := resolveSelection_exists arguments [] (nil_mem_selections arguments)
  have named := (resolveSelection_spec arguments [] winner resolved).2
  cases winner with
  | nil => exact resolved
  | cons first rest => simp at named

/-- Key resolution preserves the requested number of arguments. -/
theorem resolveSelection_length (arguments : List (String × α)) (names : List String)
    (winner : List (String × α)) (resolved : resolveSelection arguments names = some winner) :
    winner.length = names.length := by
  have named := (resolveSelection_spec arguments names winner resolved).2
  simpa only [List.length_map] using congrArg List.length named

/-- The two-argument table keeps both singleton insertions and both full orders. -/
theorem selections_two (first second : String × α) :
    selections [first, second] = [[], [first], [second], [first, second], [second, first]] := by
  simp [selections, subsequences, nonEmptySubsequences, permutations, perms, interleave, interleaveAux]

/-- With duplicate names, the later singleton overwrites the earlier singleton. -/
theorem duplicate_singleton (name : String) (first second : α) :
    resolveSelection [(name, first), (name, second)] [name] = some [(name, second)] := by
  simp [resolveSelection, selections_two, lookupLast]

/-- Duplicate full keys select the last source permutation, rather than the supplied order. -/
theorem duplicate_pair (name : String) (first second : α) :
    resolveSelection [(name, first), (name, second)] [name, name] = some [(name, second), (name, first)] := by
  simp [resolveSelection, selections_two, lookupLast]

end MicroCFTA.SourceSynthesisSelections
