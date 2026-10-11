import MicroCFTA.AcceptanceWorker
import MicroCFTA.TermRepresentation

/-!
# Adaptive direct and shared acceptance

The source starts without a table. It allocates a shared table only when two
alternatives match the same subtree. Both execution paths decide the same
finite-run language under stable guard truth.
-/

namespace MicroCFTA.AcceptanceDispatch
open Language NumberedTerms AcceptanceReference AcceptanceCache AcceptanceWorker

/-- The first returned alternative really matches the current term. -/
theorem fromMatch_head [DecidableEq Symbol] (term : Term Symbol) (edges : List (Edge State Symbol))
    (edge : Edge State Symbol) (rest : List (Edge State Symbol)) (found : fromMatch term edges = edge :: rest) :
    matchesRoot edge term = true := by
  induction edges with
  | nil => simp [fromMatch] at found
  | cons first tail ih =>
      cases matching : matchesRoot first term with
      | false => exact ih (by simpa [fromMatch, matching] using found)
      | true =>
          have same : first = edge := (List.cons.inj (by simpa [fromMatch, matching] using found)).1
          exact same ▸ matching

/-- If no second alternative matches, the filtered row contains precisely the first alternative. -/
theorem sole_match [DecidableEq Symbol] (term : Term Symbol) (edges : List (Edge State Symbol))
    (edge : Edge State Symbol) (rest : List (Edge State Symbol))
    (found : fromMatch term edges = edge :: rest) (alone : fromMatch term rest = []) :
    edges.filter (fun edge => matchesRoot edge term) = [edge] := by
  have head := fromMatch_head term edges edge rest found
  have tail := fromMatch_filter term rest
  rw [alone] at tail
  have whole := fromMatch_filter term edges
  rw [found] at whole
  simpa [head, ← tail] using whole.symm

/-- Matching can be moved to the source's filtered alternative list without changing acceptance. -/
theorem accept_filtered [DecidableEq Symbol] (automaton : Automaton State Symbol) (fuel : Nat)
    (key : State) (symbol : Symbol) (children : List (Term Symbol)) :
    accept automaton (fuel + 1) key (.node symbol children) =
      ((automaton key).filter (fun edge => matchesRoot edge (.node symbol children))).any
        (fun edge => zipAll (accept automaton fuel) edge.children children && edge.guard (.node symbol children)) := by
  simp [accept, List.any_filter]

/-- Pointwise equivalent child evaluators have the same ordered conjunction. -/
theorem zipAll_congr (first second : State → Term Symbol → Bool) (keys : List State) (terms : List (Term Symbol))
    (same : ∀ key term, term ∈ terms → first key term = second key term) :
    zipAll first keys terms = zipAll second keys terms := by
  induction keys generalizing terms with
  | nil => rfl
  | cons key keys ih =>
      cases terms with
      | nil => rfl
      | cons term terms =>
          rw [zipAll, zipAll, same key term (by simp)]
          congr 1
          exact ih terms (fun child value present => same child value (by simp [present]))

/-- The direct source loop reads successive child indices and stops on the first false result. -/
def childrenAt (check : α → β → Bool) : List α → Nat → List β → Bool
  | [], _, _ => true
  | key :: keys, index, children => match children[index]? with
    | none => false
    | some child => check key child && childrenAt check keys (index + 1) children

/-- An in-range direct child loop equals checking the corresponding ordered child suffix. -/
theorem childrenAt_correct (check : α → β → Bool) (keys : List α) (index : Nat) (children : List β)
    (fits : index + keys.length ≤ children.length) :
    childrenAt check keys index children = zipAll check keys (children.drop index) := by
  induction keys generalizing index with
  | nil => rfl
  | cons key keys ih =>
      have within : index < children.length := by simp only [List.length_cons] at fits; omega
      rw [childrenAt, List.getElem?_eq_getElem within, List.drop_eq_getElem_cons within, zipAll]
      dsimp only
      congr 1
      exact ih (index + 1) (by simp only [List.length_cons] at fits; omega)

/-- Matching arity proves that the partial source `childAt` branch is never reached. -/
theorem matching_childrenAt [DecidableEq Symbol] (edge : Edge State Symbol) (symbol : Symbol)
    (children : List (Term Symbol)) (matching : matchesRoot edge (.node symbol children) = true)
    (check : State → Term Symbol → Bool) :
    childrenAt check edge.children 0 children = zipAll check edge.children children := by
  have arity : edge.children.length = children.length := of_decide_eq_true (Bool.and_eq_true_iff.mp matching).2
  simpa using childrenAt_correct check edge.children 0 children (by omega)

/-- The packed source term's small-arity lookup implements the same safe child reads. -/
theorem packed_child_safe (term : TermRepresentation.Packed Symbol) (index : Nat)
    (within : index < (TermRepresentation.children term).length) :
    TermRepresentation.child term index = some ((TermRepresentation.children term)[index]'within) := by
  rw [TermRepresentation.child_correct, List.getElem?_eq_getElem within]

/-- Follow the source switch: no match fails, one match recurses directly, two matches start a cache. -/
def unshared [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol) :
    Nat → State → Term Symbol → Bool
  | 0, _, _ => false
  | fuel + 1, key, term@(.node _ children) =>
      match fromMatch term (automaton key) with
      | [] => false
      | edge :: rest => match fromMatch term rest with
        | [] => zipAll (unshared automaton fuel) edge.children children && edge.guard term
        | _ :: _ => (shared automaton (fuel + 1) key (number term 0).2 (fun _ => none)).1

/-- Adaptive cache allocation changes no acceptance result. -/
theorem unshared_correct [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (fuel : Nat) (key : State) (term : Term Symbol) (enough : term.height ≤ fuel) :
    unshared automaton fuel key term = truth automaton key term := by
  induction fuel generalizing key term with
  | zero => have positive := term.height_pos; omega
  | succ fuel ih =>
      cases term with
      | node symbol children =>
          have forestBound : forestHeight children ≤ fuel := by simpa [Term.height, forestHeight] using enough
          have childSame (key : State) (term : Term Symbol) (present : term ∈ children) :
              unshared automaton fuel key term = accept automaton fuel key term := by
            have bound := Nat.le_trans (height_le_forestHeight children term present) forestBound
            exact (ih key term bound).trans (accept_truth automaton fuel key term bound).symm
          cases first : fromMatch (.node symbol children) (automaton key) with
          | nil =>
              have filtered := fromMatch_filter (.node symbol children) (automaton key)
              rw [first] at filtered
              have rejected : accept automaton (fuel + 1) key (.node symbol children) = false := by
                rw [accept_filtered, ← filtered]
                rfl
              simpa [unshared, first] using rejected.symm.trans (accept_truth automaton (fuel + 1) key _ enough)
          | cons edge rest =>
              cases second : fromMatch (.node symbol children) rest with
              | nil =>
                  have filtered := sole_match (.node symbol children) (automaton key) edge rest first second
                  have direct : unshared automaton (fuel + 1) key (.node symbol children) =
                      accept automaton (fuel + 1) key (.node symbol children) := by
                    rw [accept_filtered, filtered]
                    simp only [unshared, first, second, List.any_cons, List.any_nil, Bool.or_false]
                    rw [zipAll_congr _ _ edge.children children childSame]
                  exact direct.trans (accept_truth automaton (fuel + 1) key _ enough)
              | cons other later =>
                  have cached := shared_correct automaton (fuel + 1) key (number (.node symbol children) 0).2
                    (fun index => (nodeEntries (number (.node symbol children) 0).2).lookup index) (fun _ => none)
                    (number_valid _ _) (number_registered _ _) (empty_sound _ _)
                    (by simpa only [number_original] using enough)
                  simpa only [unshared, first, second, number_original] using cached.1

/-- The public acceptance entry point accepts all finite runs and only finite runs. -/
theorem acceptsBy_exact [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (key : State) (term : Term Symbol) :
    unshared automaton term.height key term = true ↔ Accepts automaton key term := by
  rw [unshared_correct automaton term.height key term (Nat.le_refl _)]
  exact accept_complete automaton term.height key term (Nat.le_refl _)

end MicroCFTA.AcceptanceDispatch
