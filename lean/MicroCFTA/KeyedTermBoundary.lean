import MicroCFTA.RecursiveNaryFieldBounds

/-!
# Private member boundaries of a recursive key family

The source stores each member under matching AtKey and Family key labels.
All three request views retain this boundary. The wrapper changes no size,
count, rank, checked flag, or candidate order.
-/
namespace MicroCFTA.KeyedTermBoundary
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveCallbackDistinct

/-- The exact private wrapper inserted by Recur.memberTerms. -/
def atKeyTerm (position : Nat) (body : EngineTerm Symbol) : EngineTerm Symbol :=
  .node .atKey [.node (.key position) [], .node .family [.node (.key position) [], body]]

/-- All source views retain the complete private family member. -/
theorem project_member (position : Nat) (body : EngineTerm Symbol) (view : View) :
    project view (atKeyTerm position body) = [atKeyTerm position body] := by
  cases view <;> simp [project, atKeyTerm, labelled, spine,
    SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]

/-- The two key labels and their body identify the complete wrapper. -/
theorem wrapper_injective (left right : Nat) (first second : EngineTerm Symbol) :
    atKeyTerm left first = atKeyTerm right second ↔ left = right ∧ first = second := by
  simp [atKeyTerm, Term.node.injEq, List.cons.injEq]

/-- The source checks both key labels before passing a whole body request. -/
def unwrap (position : Nat) : List (EngineTerm Symbol) → Option (EngineTerm Symbol)
  | [.node .atKey [.node (.key outer) [], .node .family [.node (.key inner) [], body]]] =>
      if outer = position ∧ inner = outer then some body else none
  | _ => none

/-- Successful dispatch requires the complete exact source member shape. -/
theorem unwrap_some (position : Nat) (wanted : List (EngineTerm Symbol)) (body : EngineTerm Symbol) :
    unwrap position wanted = some body ↔ wanted = [atKeyTerm position body] := by
  unfold unwrap
  split
  · split <;> simp_all [atKeyTerm, Term.node.injEq, List.cons.injEq]
  · rename_i absent
    constructor
    · intro impossible; cases impossible
    · intro same
      subst wanted
      exact False.elim (absent position position body rfl)

/-- Whole, singleton-spine, and singleton-labelled requests use the same worker. -/
def positions (position : Nat) (body : Finite Symbol) : Callback Symbol := fun _ wanted =>
  match unwrap position wanted with
  | none => []
  | some term => body.positions .whole [term]

/-- The wrapper keeps the child's exact size class and class rank. -/
def field (position : Nat) (body : Finite Symbol) : Finite Symbol :=
  ⟨body.counts, fun index => (body.select index).map (atKeyTerm position), positions position body⟩

/-- Per-key term wrapping preserves the complete selector interval. -/
theorem field_indexed (position : Nat) (body : Finite Symbol) (indexed : FiniteIndex body) :
    FiniteIndex (field position body) := by
  intro index
  constructor
  · rintro ⟨term, selected⟩
    obtain ⟨child, found, _⟩ := Option.map_eq_some_iff.mp selected
    exact (indexed index).mp ⟨child, found⟩
  · intro within
    obtain ⟨child, selected⟩ := (indexed index).mpr within
    exact ⟨atKeyTerm position child, by simp [field, selected]⟩

/-- Entering a member removes two private nodes from the requested path. -/
theorem unwrap_height (position : Nat) (wanted : List (EngineTerm Symbol))
    (body : EngineTerm Symbol) (found : unwrap position wanted = some body) :
    forestHeight [body] + 2 ≤ forestHeight wanted := by
  rw [(unwrap_some position wanted body).mp found]
  simp [atKeyTerm, forestHeight, Term.height]
  omega

/-- The key wrapper requires child inverse laws only for smaller requests. -/
theorem field_exact_below (position : Nat) (body : Finite Symbol) (bound : Nat)
    (childExact : RecursiveFieldBounds.ExactBelow bound body) :
    RecursiveFieldBounds.ExactBelow (bound + 1) (field position body) := by
  intro view wanted height index
  cases found : unwrap position wanted with
  | none =>
      constructor
      · simp [field, positions, found]
      · rintro ⟨term, selected, projected⟩
        obtain ⟨child, _, rfl⟩ := Option.map_eq_some_iff.mp selected
        have shape : wanted = [atKeyTerm position child] :=
          projected.symm.trans (project_member position child view)
        have present := (unwrap_some position wanted child).mpr shape
        rw [found] at present
        contradiction
  | some child =>
      have smaller : forestHeight [child] ≤ bound := by
        have descent := unwrap_height position wanted child found
        omega
      rw [(unwrap_some position wanted child).mp found] at *
      change (index, true) ∈ positions position body view [atKeyTerm position child] ↔ _
      unfold positions
      rw [found]
      rw [childExact .whole [child] smaller index]
      constructor
      · rintro ⟨term, selected, projected⟩
        have same := StaticCheckedRanks.whole_eq term child projected
        subst term
        exact ⟨atKeyTerm position child, by simp [field, selected], project_member position child view⟩
      · rintro ⟨term, selected, projected⟩
        obtain ⟨inner, childSelected, rfl⟩ := Option.map_eq_some_iff.mp selected
        have same : inner = child := by
          rw [project_member] at projected
          exact (wrapper_injective position position inner child).mp
            (List.cons.inj projected).1 |>.2
        exact ⟨inner, childSelected, by simp [project, same]⟩

/-- Matching key wrappers preserve exact checked preimages in every view. -/
theorem field_exact (position : Nat) (body : Finite Symbol) (childExact : FiniteExact body) :
    FiniteExact (field position body) := by
  intro view wanted index
  exact field_exact_below position body (forestHeight wanted)
    (fun view wanted _ => childExact view wanted) view wanted (by omega) index

/-- Every candidate retains the source class interval, including false flags. -/
theorem field_bounded (position : Nat) (body : Finite Symbol)
    (bounded : ∀ view wanted row, row ∈ body.positions view wanted → row.1.rank < body.counts row.1.size) :
    ∀ view wanted row, row ∈ (field position body).positions view wanted →
      row.1.rank < (field position body).counts row.1.size := by
  intro view wanted row member
  change row ∈ positions position body view wanted at member
  unfold positions at member
  split at member
  · simp at member
  · exact bounded .whole _ row member

/-- The key wrapper retains the complete candidate order. -/
theorem field_ordered (position : Nat) (body : Finite Symbol)
    (ordered : ∀ view wanted, (body.positions view wanted).Pairwise (fun first second => before first second)) :
    ∀ view wanted, ((field position body).positions view wanted).Pairwise (fun first second => before first second) := by
  intro view wanted
  change (positions position body view wanted).Pairwise _
  unfold positions
  split
  · exact .nil
  · exact ordered .whole _

/-- Matching a member boundary does not repeat any candidate position. -/
theorem field_distinct (position : Nat) (body : Finite Symbol)
    (distinct : ∀ view wanted, Distinct (body.positions view wanted)) :
    ∀ view wanted, Distinct ((field position body).positions view wanted) := by
  intro view wanted
  change Distinct (positions position body view wanted)
  unfold positions
  split
  · exact .nil
  · exact distinct .whole _

end MicroCFTA.KeyedTermBoundary
