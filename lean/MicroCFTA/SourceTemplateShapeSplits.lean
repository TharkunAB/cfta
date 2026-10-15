import MicroCFTA.Template

/-!
# Source child-shape pruning of template split choices

The source supplies completed child edge shapes and the current child part
of each complete alive item. The split keeps those items, their order and
their duplicate occurrences. A common root-shape filter removes choices
that no child term can fill. Template matching remains the independent
`Template.Matches` relation.

This module does not model the full forced, dying and ground-group schedule
of edgeCopies. It does not prove exclusion or interned nodeEdges semantics.
Natural arities represent actual child lengths; source Int capacity and
runtime evaluation remain separate.
-/
namespace MicroCFTA.SourceTemplateShapeSplits
open Language Template
variable {Symbol Item State : Type}

/-- A completed child edge contributes its symbol and child count. -/
abbrev Shape (Symbol : Type) := Symbol × Nat

/-- Read the complete term's root shape. -/
def shape : Term Symbol → Shape Symbol
  | .node root children => (root, children.length)

/-- Retain candidate roots that align every required part, in original order. -/
def fits [DecidableEq Symbol] (candidates : List (Shape Symbol)) (parts : List (Pattern Symbol)) : List (Shape Symbol) :=
  candidates.filter (fun candidate => parts.all (fun part => (childTemplates part candidate.1 candidate.2).isSome))

/-- Shape filtering changes neither candidate records nor their duplicate occurrences. -/
theorem fits_sublist [DecidableEq Symbol] (candidates : List (Shape Symbol)) (parts : List (Pattern Symbol)) :
    (fits candidates parts).Sublist candidates := List.filter_sublist

/-- An empty requirement retains the exact candidate list. -/
theorem fits_nil [DecidableEq Symbol] (candidates : List (Shape Symbol)) : fits candidates [] = candidates := by
  simp [fits]

/-- Sequential shape narrowing checks both part lists on each original candidate. -/
theorem fits_append [DecidableEq Symbol] (candidates : List (Shape Symbol)) (first second : List (Pattern Symbol)) :
    fits (fits candidates first) second = fits candidates (first ++ second) := by
  simp only [fits, List.filter_filter, List.all_append]
  apply List.filter_congr
  intro candidate _
  exact Bool.and_comm _ _

/-- Tail-first split traversal keeps the head part with the same common shape test. -/
theorem fits_prepend [DecidableEq Symbol] (candidates : List (Shape Symbol)) (part : Pattern Symbol)
    (parts : List (Pattern Symbol)) : fits (fits candidates parts) [part] = fits candidates (part :: parts) := by
  simp only [fits, List.filter_filter, List.all_cons, List.all_nil, Bool.and_true]

/-- Every matching template aligns at the actual root of its complete term. -/
theorem matches_align [DecidableEq Symbol] (part : Pattern Symbol) (term : Term Symbol)
    (matched : Matches part term) : (childTemplates part (shape term).1 (shape term).2).isSome = true := by
  cases matched with
  | node pattern root children parts aligned childMatches => simp only [shape, aligned, Option.isSome_some]

/-- A matching child term keeps its own supplied shape through every required part. -/
theorem matches_fits [DecidableEq Symbol] (candidates : List (Shape Symbol)) (parts : List (Pattern Symbol))
    (term : Term Symbol) (present : shape term ∈ candidates) (matched : ∀ part ∈ parts, Matches part term) :
    shape term ∈ fits candidates parts := by
  apply List.mem_filter.mpr
  exact ⟨present, List.all_eq_true.mpr (fun part member => matches_align part term (matched part member))⟩

/-- No term with a supplied root can fill incompatible required parts. -/
theorem incompatible_empty [DecidableEq Symbol] (candidates : List (Shape Symbol)) (parts : List (Pattern Symbol))
    (term : Term Symbol) (present : shape term ∈ candidates) (empty : fits candidates parts = []) :
    ¬(∀ part ∈ parts, Matches part term) := by
  intro matched
  have member := matches_fits candidates parts term present matched
  rw [empty] at member
  cases member

/-- A filled base or ground-group root guard cannot be pruned for its actual child. -/
theorem matches_nonempty [DecidableEq Symbol] (candidates : List (Shape Symbol)) (parts : List (Pattern Symbol))
    (term : Term Symbol) (present : shape term ∈ candidates) (matched : ∀ part ∈ parts, Matches part term) :
    fits candidates parts ≠ [] := fun empty => incompatible_empty candidates parts term present empty matched

/-- The prior source split gives keep before kill for each tail choice. -/
def oldSplits : List Item → List (List Item × List Item)
  | [] => [([], [])]
  | item :: rest => (oldSplits rest).flatMap (fun choice =>
      [(item :: choice.1, choice.2), (choice.1, item :: choice.2)])

/-- One source split step keeps the complete item only when the narrowed shapes are nonempty. -/
def fork [DecidableEq Symbol] (part : Item → Pattern Symbol) (item : Item)
    (choice : (List Item × List Item) × List (Shape Symbol)) : List ((List Item × List Item) × List (Shape Symbol)) :=
  let narrowed := fits choice.2 [part item]
  (if narrowed.isEmpty then [] else [((item :: choice.1.1, choice.1.2), narrowed)]) ++
    [((choice.1.1, item :: choice.1.2), choice.2)]

/-- Match the actual source tail-first shape-pruned split recursion. -/
def splits [DecidableEq Symbol] (part : Item → Pattern Symbol) (fitting : List (Shape Symbol)) :
    List Item → List ((List Item × List Item) × List (Shape Symbol))
  | [] => [(([], []), fitting)]
  | item :: rest => (splits part fitting rest).flatMap (fork part item)

/-- Compute the exact common shape annotation of each surviving prior choice. -/
def annotate [DecidableEq Symbol] (part : Item → Pattern Symbol) (fitting : List (Shape Symbol))
    : List (List Item × List Item) → List ((List Item × List Item) × List (Shape Symbol))
  | [] => []
  | choice :: rest =>
    let remaining := fits fitting (choice.1.map part)
    (if remaining.isEmpty then [] else [(choice, remaining)]) ++ annotate part fitting rest

private theorem annotate_append [DecidableEq Symbol] (part : Item → Pattern Symbol) (fitting : List (Shape Symbol))
    (first second : List (List Item × List Item)) :
    annotate part fitting (first ++ second) = annotate part fitting first ++ annotate part fitting second := by
  induction first with
  | nil => rfl
  | cons choice rest ih => simp only [List.cons_append, annotate, ih, List.append_assoc]

private theorem annotate_fork [DecidableEq Symbol] (part : Item → Pattern Symbol) (fitting : List (Shape Symbol))
    (item : Item) (choice : List Item × List Item) :
    annotate part fitting [(item :: choice.1, choice.2), (choice.1, item :: choice.2)] =
      (annotate part fitting [choice]).flatMap (fork part item) := by
  simp only [annotate, List.map_cons, List.append_nil]
  rw [← fits_prepend fitting (part item) (choice.1.map part)]
  cases remaining : fits fitting (choice.1.map part) with
  | nil => simp [fits]
  | cons candidate rest =>
      cases narrowed : (fits (candidate :: rest) [part item]).isEmpty <;> simp [fork, narrowed]

private theorem annotate_forks [DecidableEq Symbol] (part : Item → Pattern Symbol) (fitting : List (Shape Symbol))
    (item : Item) (choices : List (List Item × List Item)) :
    annotate part fitting (choices.flatMap (fun choice => [(item :: choice.1, choice.2), (choice.1, item :: choice.2)])) =
      (annotate part fitting choices).flatMap (fork part item) := by
  induction choices with
  | nil => rfl
  | cons choice rest ih =>
      rw [List.flatMap_cons, annotate_append, annotate_fork, ih]
      rw [show choice :: rest = [choice] ++ rest from rfl, annotate_append, List.flatMap_append]

/-- The optimization is exactly ordered filtering of the prior choices with exact common shape annotations. -/
theorem splits_exact [DecidableEq Symbol] (part : Item → Pattern Symbol) (fitting : List (Shape Symbol))
    (nonempty : fitting ≠ []) (items : List Item) :
    splits part fitting items = annotate part fitting (oldSplits items) := by
  induction items with
  | nil => simp [splits, oldSplits, annotate, fits_nil, List.isEmpty_eq_false_iff.mpr nonempty]
  | cons item rest ih => rw [splits, ih, oldSplits, annotate_forks]

private theorem annotate_pairs [DecidableEq Symbol] (part : Item → Pattern Symbol) (fitting : List (Shape Symbol))
    (choices : List (List Item × List Item)) :
    (annotate part fitting choices).map Prod.fst =
      choices.filter (fun choice => !(fits fitting (choice.1.map part)).isEmpty) := by
  induction choices with
  | nil => rfl
  | cons choice rest ih =>
      simp only [annotate, List.map_append, List.filter_cons]
      cases empty : (fits fitting (choice.1.map part)).isEmpty <;> simp [ih]

/-- Surviving split choices retain their exact old order and duplicate multiplicity. -/
theorem splits_pairs [DecidableEq Symbol] (part : Item → Pattern Symbol) (fitting : List (Shape Symbol))
    (nonempty : fitting ≠ []) (items : List Item) :
    (splits part fitting items).map Prod.fst =
      (oldSplits items).filter (fun choice => !(fits fitting (choice.1.map part)).isEmpty) := by
  rw [splits_exact part fitting nonempty, annotate_pairs]

/-- Decide whether this child's complete term fills one keep/kill choice. -/
def acceptsChoice [DecidableEq Symbol] (part : Item → Pattern Symbol) (term : Term Symbol)
    (choice : List Item × List Item) : Bool :=
  choice.1.all (fun item => matchesTerm (part item) term) &&
    choice.2.all (fun item => !(matchesTerm (part item) term))

/-- A filled old choice keeps at least the actual child's root shape. -/
theorem accepted_fits [DecidableEq Symbol] (part : Item → Pattern Symbol) (fitting : List (Shape Symbol))
    (term : Term Symbol) (present : shape term ∈ fitting) (choice : List Item × List Item)
    (accepted : acceptsChoice part term choice = true) : (fits fitting (choice.1.map part)).isEmpty = false := by
  apply List.isEmpty_eq_false_iff.mpr
  apply matches_nonempty fitting (choice.1.map part) term present
  intro pattern member
  obtain ⟨item, included, rfl⟩ := List.mem_map.mp member
  exact (matchesTerm_correct term (part item)).mp
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp accepted).1 item included)

/-- Every old choice filled by an actual child survives, with the same order and occurrence count. -/
theorem accepted_splits_exact [DecidableEq Symbol] (part : Item → Pattern Symbol) (fitting : List (Shape Symbol))
    (term : Term Symbol) (present : shape term ∈ fitting) (items : List Item) :
    ((splits part fitting items).map Prod.fst).filter (acceptsChoice part term) =
      (oldSplits items).filter (acceptsChoice part term) := by
  have nonempty : fitting ≠ [] := fun empty => by rw [empty] at present; cases present
  rw [splits_pairs part fitting nonempty, List.filter_filter]
  apply List.filter_congr
  intro choice _
  cases accepted : acceptsChoice part term choice with
  | false => simp
  | true => simp [accepted_fits part fitting term present choice accepted]

/-- The source omits killed parts that fit no possible child root. -/
def killedParts [DecidableEq Symbol] (fitting : List (Shape Symbol)) (parts : List (Pattern Symbol)) : List (Pattern Symbol) :=
  parts.filter (fun part => !(fits fitting [part]).isEmpty)

/-- Omitting impossible killed parts does not change avoidance for any supplied child term. -/
theorem killedParts_exact [DecidableEq Symbol] (fitting : List (Shape Symbol)) (parts : List (Pattern Symbol))
    (term : Term Symbol) (present : shape term ∈ fitting) :
    (∀ part ∈ killedParts fitting parts, ¬Matches part term) ↔ ∀ part ∈ parts, ¬Matches part term := by
  constructor
  · intro avoided part member matched
    have nonempty := matches_nonempty fitting [part] term present (by simpa using matched)
    exact avoided part (List.mem_filter.mpr ⟨member, by simp [List.isEmpty_eq_false_iff.mpr nonempty]⟩) matched
  · intro avoided part member
    exact avoided part (List.mem_filter.mp member).1

/-- The actual explicit transition rows supply each child root inventory. -/
def shapesOf (automaton : Automaton State Symbol) (state : State) : List (Shape Symbol) :=
  (automaton state).map (fun edge => (edge.label, edge.children.length))

/-- An actual accepted child derives its shape from one literal source transition. -/
theorem accepted_shape (automaton : Automaton State Symbol) (state : State) (term : Term Symbol)
    (accepted : Accepts automaton state term) : shape term ∈ shapesOf automaton state := by
  cases accepted with
  | node edge children present childRuns guard =>
      exact List.mem_map.mpr ⟨edge, present, by simp only [shape, childRuns.length_eq]⟩

/-- Actual accepted explicit-state children derive exact preservation of all filled old split occurrences. -/
theorem accepted_child_splits [DecidableEq Symbol] (part : Item → Pattern Symbol)
    (automaton : Automaton State Symbol) (state : State) (term : Term Symbol)
    (accepted : Accepts automaton state term) (items : List Item) :
    ((splits part (shapesOf automaton state) items).map Prod.fst).filter (acceptsChoice part term) =
      (oldSplits items).filter (acceptsChoice part term) :=
  accepted_splits_exact part _ term (accepted_shape automaton state term accepted) items

end MicroCFTA.SourceTemplateShapeSplits
