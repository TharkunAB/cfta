import MicroCFTA.Template
import MicroCFTA.Productivity

/-!
# Graph primitives used by symbolic rank selection

Path conditioning keeps all original transition guards. It changes one child
at each path step. Projection collects possible child states and then unions
their rows. Projection is an upper bound: ancestor constraints can reject a
projected subtree in its original context.
-/
namespace MicroCFTA.SymbolicGraph
open Language Template

/-- A constructor request at one path, with unrestricted sibling positions. -/
def request (symbol : Symbol) (arity : Nat) : List Nat → Pattern Symbol
  | [] => .node symbol (List.replicate arity .hole)
  | index :: rest => .anyPrefix (List.replicate index .hole ++ [request symbol arity rest])

/-- Hole matching consumes exactly the complete supplied child list. -/
theorem holes_match [DecidableEq Symbol] (terms : List (Term Symbol)) :
    matchesChildren (List.replicate terms.length .hole) terms = true := by
  induction terms with
  | nil => rfl
  | cons first rest ih =>
    simpa [List.replicate_succ, matchesChildren, ih] using (matchesTerm_correct first .hole).mpr (hole_matches first)

/-- Matching an indexed child leaves every other child unrestricted. -/
theorem indexed_match [DecidableEq Symbol] (index : Nat) (pattern : Pattern Symbol)
    (terms : List (Term Symbol)) (bound : index < terms.length) :
    matchesChildren (List.replicate index .hole ++ pattern ::
      List.replicate (terms.length - index - 1) .hole) terms = matchesTerm pattern terms[index] := by
  induction index generalizing terms with
  | zero =>
    cases terms with
    | nil => simp at bound
    | cons first rest => simp [matchesChildren, holes_match]
  | succ index ih =>
    cases terms with
    | nil => simp at bound
    | cons first rest =>
      have next : index < rest.length := by simpa using bound
      have hole := (matchesTerm_correct first .hole).mpr (hole_matches first)
      simpa [List.replicate_succ, matchesChildren, hole] using ih rest next

/-- The constructor and arity observed at a complete subtree. -/
def RootMatches (symbol : Symbol) (arity : Nat) : Term Symbol → Prop
  | .node found children => found = symbol ∧ children.length = arity

/-- A successful path request keeps exactly the requested constructor and arity. -/
theorem request_matches [DecidableEq Symbol] (symbol : Symbol) (arity : Nat)
    (path : List Nat) (term : Term Symbol) :
    Matches (request symbol arity path) term ↔
      ∃ subtree, term.atPath path = some subtree ∧ RootMatches symbol arity subtree := by
  rw [← matchesTerm_correct]
  induction path generalizing term with
  | nil =>
    cases term with
    | node found children =>
      by_cases same : symbol = found
      · subst found
        by_cases size : arity = children.length
        · subst arity
          simp [request, matchesTerm, childTemplates, exactChildren, holes_match,
            Term.atPath, RootMatches]
        · simp [request, matchesTerm, childTemplates, exactChildren, size,
            Term.atPath, RootMatches, Ne.symm size]
      · simp [request, matchesTerm, childTemplates, same, Term.atPath, RootMatches, Ne.symm same]
  | cons index rest ih =>
    cases term with
    | node found children =>
      by_cases bound : index < children.length
      · have allow : index + 1 ≤ children.length := by omega
        have padded := indexed_match index (request symbol arity rest) children bound
        have arithmetic : children.length - (index + 1) = children.length - index - 1 := by omega
        simpa [request, matchesTerm, childTemplates, prefixChildren, allow, List.append_assoc,
          arithmetic, Term.atPath, List.getElem?_eq_getElem bound, ← padded] using ih children[index]
      · have noLength : ¬index + 1 ≤ children.length := by omega
        simp [request, matchesTerm, childTemplates, prefixChildren, noLength,
          Term.atPath, List.getElem?_eq_none (by omega : children.length ≤ index)]

/-- Explicit states for the source's path-copy transformation. -/
def condition [DecidableEq Symbol] (automaton : Automaton State Symbol) :
    Automaton (State × Pattern Symbol) Symbol := Template.restrict automaton

/-- Path conditioning has exactly the original language with the requested constructor. -/
theorem condition_exact [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (state : State) (symbol : Symbol) (arity : Nat) (path : List Nat) (term : Term Symbol) :
    Accepts (condition automaton) (state, request symbol arity path) term ↔
      Accepts automaton state term ∧
        ∃ subtree, term.atPath path = some subtree ∧ RootMatches symbol arity subtree := by
  rw [condition, restrict_exact, request_matches]

/-- Updating one position in a uniform list changes exactly that position. -/
theorem set_replicate (index count : Nat) (old new : α) (bound : index < count) :
    (List.replicate count old).set index new =
      List.replicate index old ++ new :: List.replicate (count - index - 1) old := by
  induction index generalizing count with
  | zero => cases count with
    | zero => omega
    | succ count => simp [List.replicate_succ]
  | succ index ih => cases count with
    | zero => omega
    | succ count =>
      have next : index < count := by omega
      simpa [List.replicate_succ] using congrArg (old :: ·) (ih count next)

/-- At the selected position the source filters only constructor and arity. -/
theorem condition_root_step [DecidableEq Symbol] (wanted found : Symbol) (arity count : Nat) :
    childTemplates (request wanted arity []) found count =
      if wanted = found ∧ arity = count then some (List.replicate count .hole) else none := by
  by_cases same : wanted = found <;> by_cases size : arity = count <;>
    simp [request, childTemplates, exactChildren, same, size]

/-- Before the selected position the source updates one child and preserves every sibling. -/
theorem condition_child_step [DecidableEq Symbol] (wanted found : Symbol) (arity count index : Nat)
    (rest : List Nat) :
    childTemplates (request wanted arity (index :: rest)) found count =
      if index < count then
        some ((List.replicate count .hole).set index (request wanted arity rest)) else none := by
  by_cases bound : index < count
  · have allow : index + 1 ≤ count := by omega
    have arithmetic : count - (index + 1) = count - index - 1 := by omega
    simp [request, childTemplates, prefixChildren, allow, bound, set_replicate index count _ _ bound,
      List.append_assoc, arithmetic]
  · have reject : ¬index + 1 ≤ count := by omega
    simp [request, childTemplates, prefixChildren, bound, reject]

/-- Read the related source entry at one successful target-list lookup. -/
theorem all₂_lookup (relation : α → β → Prop) {left : List α} {right : List β}
    (related : All₂ relation left right) (index : Nat) (value : β)
    (found : right[index]? = some value) :
    ∃ source, left[index]? = some source ∧ relation source value := by
  induction related generalizing index with
  | nil => simp at found
  | @cons first second left right head tail ih =>
    cases index with
    | zero =>
      have same : second = value := by simpa using found
      subst value
      exact ⟨first, rfl, head⟩
    | succ index => exact ih index (by simpa using found)

/-- The source's set traversal through successive child positions. -/
def projectStates [DecidableEq State] (automaton : Automaton State Symbol) :
    List Nat → List State → List State
  | [], states => states
  | index :: rest, states => projectStates automaton rest
      (((states.flatMap automaton).filterMap fun edge => edge.children[index]?).eraseDups)

/-- Every existing subtree of an accepted term has a projected accepting state. -/
theorem projectStates_coverage [DecidableEq State] (automaton : Automaton State Symbol)
    (path : List Nat) (states : List State) (state : State) (term subtree : Term Symbol)
    (present : state ∈ states) (accepted : Accepts automaton state term)
    (found : term.atPath path = some subtree) :
    ∃ selected, selected ∈ projectStates automaton path states ∧ Accepts automaton selected subtree := by
  induction path generalizing states state term with
  | nil =>
    have same : term = subtree := by simpa [Term.atPath] using found
    subst term
    exact ⟨state, present, accepted⟩
  | cons index rest ih =>
    cases accepted with
    | node edge children member childRuns guard =>
      simp only [Term.atPath] at found
      cases lookup : children[index]? with
      | none => simp [lookup] at found
      | some child =>
        obtain ⟨childState, childLookup, childAccepted⟩ := all₂_lookup _ childRuns index child lookup
        apply ih _ childState child ?_ childAccepted (by simpa [lookup] using found)
        simp only [List.mem_eraseDups, List.mem_filterMap, List.mem_flatMap]
        exact ⟨edge, ⟨state, present, member⟩, childLookup⟩

/-- Projected rows are the union of all states selected by the path traversal. -/
def projectRows [DecidableEq State] (automaton : Automaton State Symbol)
    (path : List Nat) (root : State) : List (Edge State Symbol) :=
  (projectStates automaton path [root]).flatMap automaton

/-- Accept at newly built rows, with original graph states in their children. -/
def AcceptsRows (automaton : Automaton State Symbol) (rows : List (Edge State Symbol)) : Term Symbol → Prop
  | .node symbol children => ∃ edge ∈ rows, edge.label = symbol ∧
      All₂ (Accepts automaton) edge.children children ∧ edge.guard (.node symbol children) = true

/-- Unioning state rows has exactly their combined accepted language. -/
theorem rows_union_exact (automaton : Automaton State Symbol) (states : List State) (term : Term Symbol) :
    AcceptsRows automaton (states.flatMap automaton) term ↔
      ∃ state ∈ states, Accepts automaton state term := by
  cases term with
  | node symbol children =>
    simp only [AcceptsRows, List.mem_flatMap]
    constructor
    · rintro ⟨edge, ⟨state, present, member⟩, same, childRuns, guard⟩
      subst symbol
      exact ⟨state, present, .node edge children member childRuns guard⟩
    · rintro ⟨state, present, accepted⟩
      cases accepted with
      | node edge children member childRuns guard =>
        exact ⟨edge, ⟨state, present, member⟩, rfl, childRuns, guard⟩

/-- The actual path projection cannot omit a subtree needed by an accepted term. -/
theorem project_coverage [DecidableEq State] (automaton : Automaton State Symbol)
    (root : State) (path : List Nat) (term subtree : Term Symbol)
    (accepted : Accepts automaton root term) (found : term.atPath path = some subtree) :
    AcceptsRows automaton (projectRows automaton path root) subtree := by
  exact (rows_union_exact automaton _ subtree).mpr
    (projectStates_coverage automaton path [root] root term subtree (by simp) accepted found)

/-- Projection at the root is exact, including every original guard. -/
theorem project_root_exact [DecidableEq State] (automaton : Automaton State Symbol)
    (root : State) (term : Term Symbol) :
    AcceptsRows automaton (projectRows automaton [] root) term ↔ Accepts automaton root term := by
  simpa [projectRows, projectStates] using rows_union_exact automaton [root] term

end MicroCFTA.SymbolicGraph
