import MicroCFTA.SourceSynthesisSelectionClosure
import MicroCFTA.SourceSynthesisOrdinaryTyping

/-!
# Actual singleton selection and ordinary last lookup

Singleton extraction retains the actual source selection order. It returns
each input occurrence once, including duplicate names and payloads. Only
singleton permutations contribute. Their order follows the source subsequence
worker. The resolver therefore selects the last matching input binding.

These laws concern lookup data. They require no relevant membership, source
output equation, name uniqueness, payload equality, or type-universe premise.
Ordinary typing and the public input domain remain unchanged.
-/
namespace MicroCFTA.SourceSynthesisRelevantSingletonLookup
open SourceSynthesisSelections
open SourceSynthesisSelectionClosure (permutations_spec)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisFirstOrderConstruction (Row context resolveArguments)
open SourceSynthesisOrdinaryTyping (queryLookup)

variable {α : Type}

private def singletonEntry : List α → Option α
  | [value] => some value
  | _ => none

private theorem folded_singletons (value : α) (entries : List (List α))
    (nonempty : ∀ selected ∈ entries, selected ≠ []) :
    (∀ selected ∈ entries.foldr (fun chosen later => chosen :: (value :: chosen) :: later) [],
      selected ≠ []) ∧
      (entries.foldr (fun chosen later => chosen :: (value :: chosen) :: later) []).filterMap
        singletonEntry = entries.filterMap singletonEntry := by
  revert nonempty
  induction entries with
  | nil =>
      intro _nonempty
      exact ⟨by simp, rfl⟩
  | cons first rest ih =>
      intro nonempty
      have own := nonempty first List.mem_cons_self
      have tail := ih (fun selected member => nonempty selected (List.mem_cons_of_mem first member))
      have doubled : singletonEntry (value :: first) = none := by
        cases first with
        | nil => exact (own rfl).elim
        | cons head remaining => rfl
      constructor
      · intro selected member
        simp only [List.foldr_cons, List.mem_cons] at member
        rcases member with same | same | member
        · subst selected; exact own
        · subst selected; exact List.cons_ne_nil _ _
        · exact tail.1 selected member
      · simp only [List.foldr_cons, List.filterMap_cons, doubled, tail.2]

private theorem nonEmpty_singletons (inputs : List α) :
    (∀ selected ∈ nonEmptySubsequences inputs, selected ≠ []) ∧
      (nonEmptySubsequences inputs).filterMap singletonEntry = inputs := by
  induction inputs with
  | nil => exact ⟨by simp [nonEmptySubsequences], rfl⟩
  | cons first rest ih =>
      have folded := folded_singletons first (nonEmptySubsequences rest) ih.1
      constructor
      · intro selected member
        rw [nonEmptySubsequences] at member
        rcases List.mem_cons.mp member with same | member
        · subst selected; exact List.cons_ne_nil _ _
        · exact folded.1 selected member
      · change first ::
          ((nonEmptySubsequences rest).foldr
            (fun chosen later => chosen :: (first :: chosen) :: later) []).filterMap singletonEntry =
            first :: rest
        rw [folded.2, ih.2]

private theorem permutation_singletons (inputs : List α) :
    (permutations inputs).filterMap singletonEntry =
      match singletonEntry inputs with
      | none => []
      | some value => [value] := by
  cases inputs with
  | nil => exact congrArg (List.filterMap singletonEntry) permutations_nil
  | cons first rest =>
      cases rest with
      | nil => exact congrArg (List.filterMap singletonEntry) (permutations_singleton first)
      | cons second tail =>
          apply List.filterMap_eq_nil_iff.mpr
          intro selected included
          have length := ((permutations_spec (first :: second :: tail) selected).mp included).length_eq
          cases selected with
          | nil => rfl
          | cons value remaining =>
              cases remaining with
              | nil =>
                  simp only [List.length_cons, List.length_nil] at length
                  omega
              | cons next rest => rfl

private theorem flat_permutation_singletons (entries : List (List α)) :
    (entries.flatMap fun inputs => (permutations inputs).filterMap singletonEntry) =
      entries.filterMap singletonEntry := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      rw [List.flatMap_cons, ih, permutation_singletons, List.filterMap_cons]
      cases singletonEntry first <;> rfl

private theorem selection_singletons (arguments : List (String × α)) :
    (selections arguments).filterMap singletonEntry = arguments := by
  rw [selections, List.filterMap_flatMap, flat_permutation_singletons]
  exact (nonEmpty_singletons arguments).2

private theorem lookupLast_singleton_filter (entries : List (List (String × α))) (name : String) :
    lookupLast [name] entries =
      (List.lookup name ((entries.filterMap singletonEntry).reverse)).map
        (fun value => [(name, value)]) := by
  induction entries with
  | nil => rfl
  | cons chosen later ih =>
      cases chosen with
      | nil =>
          change (match lookupLast [name] later with
            | some winner => some winner
            | none => none) =
              (List.lookup name ((later.filterMap singletonEntry).reverse)).map
                (fun value => [(name, value)])
          rw [ih]
          cases List.lookup name ((later.filterMap singletonEntry).reverse) <;> rfl
      | cons entry remaining =>
          cases remaining with
          | nil =>
              obtain ⟨key, value⟩ := entry
              change (match lookupLast [name] later with
                | some winner => some winner
                | none => if [key] = [name] then some [(key, value)] else none) =
                  (List.lookup name (((key, value) :: later.filterMap singletonEntry).reverse)).map
                    (fun output => [(name, output)])
              rw [ih, List.reverse_cons, List.lookup_append]
              cases found : List.lookup name ((later.filterMap singletonEntry).reverse) with
              | some previous => rfl
              | none =>
                  change (if [key] = [name] then some [(key, value)] else none) =
                    (List.lookup name [(key, value)]).map (fun output => [(name, output)])
                  by_cases same : key = name
                  · subst key
                    rw [ite_eq_left rfl, List.lookup_cons_self, Option.map_some]
                  · have named : [key] ≠ [name] := by
                      intro equal
                      exact same (List.cons.inj equal).1
                    have missing : List.lookup name [(key, value)] = none := by
                      simp [Ne.symm same]
                    rw [ite_eq_right named, missing, Option.map_none]
          | cons next rest =>
              have different : (entry :: next :: rest).map Prod.fst ≠ [name] := by simp
              change (match lookupLast [name] later with
                | some winner => some winner
                | none => if (entry :: next :: rest).map Prod.fst = [name]
                    then some (entry :: next :: rest) else none) =
                  (List.lookup name ((later.filterMap singletonEntry).reverse)).map
                    (fun value => [(name, value)])
              rw [ih]
              cases List.lookup name ((later.filterMap singletonEntry).reverse) with
              | some previous => rfl
              | none => exact ite_eq_right different

/-- The actual singleton resolver returns the last matching binding, including duplicates. -/
theorem resolveSelection_singleton (arguments : List (String × α)) (name : String) :
    resolveSelection arguments [name] =
      (List.lookup name arguments.reverse).map (fun value => [(name, value)]) := by
  unfold resolveSelection
  rw [lookupLast_singleton_filter, selection_singletons]

private theorem lookup_argument_rows (arguments : List (String × Ty)) (name : String) :
    List.lookup name (arguments.map fun entry =>
      (entry.1, (.mk entry.1 top [typeNode top entry.2] : Row))) =
        (List.lookup name arguments).map (fun typ => (.mk name top [typeNode top typ] : Row)) := by
  induction arguments with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, typ⟩ := entry
      by_cases same : name = key
      · subst key; simp
      · have different : (name == key) = false := beq_eq_false_iff_ne.mpr same
        simpa only [List.map_cons, List.lookup, different] using ih

/-- Ordinary last query lookup supplies the exact actual singleton source row. -/
theorem queryLookup_resolve_singleton (lib : Library) (query : Query) (name : String) (typ : Ty)
    (found : queryLookup query.queryArguments name = some typ) :
    resolveArguments (context lib query) [name] =
      some [(name, (.mk name top [typeNode top typ] : Row))] := by
  rw [resolveArguments, resolveSelection_singleton]
  change (List.lookup name ((query.queryArguments.map fun entry =>
    (entry.1, (.mk entry.1 top [typeNode top entry.2] : Row))).reverse)).map
      (fun row => [(name, row)]) = some [(name, (.mk name top [typeNode top typ] : Row))]
  rw [← List.map_reverse, lookup_argument_rows]
  exact congrArg (fun result : Option Ty =>
    (result.map fun value => (.mk name top [typeNode top value] : Row)).map fun row => [(name, row)]) found

end MicroCFTA.SourceSynthesisRelevantSingletonLookup
