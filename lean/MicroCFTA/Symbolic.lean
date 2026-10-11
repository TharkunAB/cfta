import MicroCFTA.Language
import MicroCFTA.Lattice

/-!
# Symbolic equality counting

This model separates the signed map used by `Internal.Symbolic.countUnion`
from the languages denoted by its keys. It implements coefficient insertion,
intersection generation, zero removal, and the left fold over alternatives.
The finite-list instance makes intersection and membership executable.
-/

namespace MicroCFTA.Symbolic

open Language
open Lattice (indicator)

/-- A finite map represented by its entries. Equal keys can be collected. -/
abbrev Coefficients (Key : Type) := List (Key × Int)

/-- Apply the signed map to a numeric interpretation of its keys. -/
def weighted (value : Key → Int) : Coefficients Key → Int
  | [] => 0
  | (key, coefficient) :: rest => coefficient * value key + weighted value rest

/-- Add one coefficient. This is `Map.insertWith (+)`. -/
def insertCoefficient [DecidableEq Key] (key : Key) (coefficient : Int) :
    Coefficients Key → Coefficients Key
  | [] => [(key, coefficient)]
  | (other, previous) :: rest =>
      if key = other then (other, coefficient + previous) :: rest
      else (other, previous) :: insertCoefficient key coefficient rest

/-- Collect equal keys. This is `Map.fromListWith (+)`. -/
def collect [DecidableEq Key] (entries : Coefficients Key) : Coefficients Key :=
  entries.foldr (fun entry rest => insertCoefficient entry.1 entry.2 rest) []

/-- Remove zero coefficients after collecting intersections. -/
def trim (entries : Coefficients Key) : Coefficients Key :=
  entries.filter fun entry => entry.2 != 0

/-- Inserting a coefficient adds exactly its contribution. -/
theorem weighted_insert [DecidableEq Key] (value : Key → Int)
    (key : Key) (coefficient : Int) (entries : Coefficients Key) :
    weighted value (insertCoefficient key coefficient entries) =
      coefficient * value key + weighted value entries := by
  induction entries with
  | nil => simp [insertCoefficient, weighted]
  | cons entry entries ih =>
      rcases entry with ⟨other, previous⟩
      by_cases h : key = other
      · subst other
        simp [insertCoefficient, weighted, Int.add_mul, Int.add_assoc]
      · simp [insertCoefficient, h, weighted, ih]
        omega

/-- Collecting equal graph keys preserves every numeric interpretation. -/
theorem weighted_collect [DecidableEq Key] (value : Key → Int)
    (entries : Coefficients Key) : weighted value (collect entries) = weighted value entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [collect, List.foldr_cons, weighted_insert, weighted] at *
      rw [ih]

/-- Removing a zero coefficient preserves every numeric interpretation. -/
theorem weighted_trim (value : Key → Int) (entries : Coefficients Key) :
    weighted value (trim entries) = weighted value entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨key, coefficient⟩
      by_cases h : coefficient = 0
      · subst coefficient
        simpa [trim, weighted] using ih
      · simpa [trim, h, weighted] using ih

/-- Concatenation adds the values of signed maps. -/
theorem weighted_append (value : Key → Int) (left right : Coefficients Key) :
    weighted value (left ++ right) = weighted value left + weighted value right := by
  induction left with
  | nil => simp [weighted]
  | cons entry left ih => simp [weighted, ih, Int.add_assoc]

/-- Negated intersections introduced by one union insertion. -/
def overlaps (meet : Key → Key → Option Key) (key : Key)
    (entries : Coefficients Key) : Coefficients Key :=
  entries.filterMap fun (other, coefficient) =>
    (meet key other).map fun common => (common, -coefficient)

/-- Insert a new union alternative with collected intersection coefficients. -/
def addAlternative [DecidableEq Key] (meet : Key → Key → Option Key)
    (entries : Coefficients Key) (key : Key) : Coefficients Key :=
  trim (insertCoefficient key 1 (collect (entries ++ overlaps meet key entries)))

/-- The full inclusion-exclusion fold. Counts are needed only for its final keys. -/
def unionCoefficients [DecidableEq Key] (meet : Key → Key → Option Key)
    (keys : List Key) : Coefficients Key :=
  keys.foldl (addAlternative meet) []

/-- The intersection interface used by the source. An omitted intersection is empty. -/
def ExactMeet (member : Key → Value → Bool) (meet : Key → Key → Option Key) : Prop :=
  ∀ left right value,
    (match meet left right with
    | none => false
    | some common => member common value) = (member left value && member right value)

/-- Each generated intersection contributes the negative product of indicators. -/
theorem weighted_overlaps (member : Key → Value → Bool)
    (meet : Key → Key → Option Key) (exact : ExactMeet member meet)
    (key : Key) (entries : Coefficients Key) (value : Value) :
    weighted (fun edge => indicator (member edge value)) (overlaps meet key entries) =
      -(indicator (member key value) *
        weighted (fun edge => indicator (member edge value)) entries) := by
  induction entries with
  | nil => simp [overlaps, weighted]
  | cons entry entries ih =>
      rcases entry with ⟨other, coefficient⟩
      have he := exact key other value
      cases hm : meet key other with
      | none =>
          simp only [hm] at he
          have hz : indicator (member key value) * indicator (member other value) = 0 := by
            rw [← Lattice.indicator_and, ← he]
            rfl
          simp only [overlaps, List.filterMap_cons, hm, Option.map_none] at *
          simp only [weighted]
          rw [ih]
          grind
      | some common =>
          simp only [hm] at he
          have hc : indicator (member common value) =
              indicator (member key value) * indicator (member other value) := by
            rw [he, Lattice.indicator_and]
          simp only [overlaps, List.filterMap_cons, hm, Option.map_some] at *
          simp only [weighted]
          rw [ih, hc]
          grind

/-- One insertion implements `old + new - old * new` at every term. -/
theorem weighted_addAlternative [DecidableEq Key] (member : Key → Value → Bool)
    (meet : Key → Key → Option Key) (exact : ExactMeet member meet)
    (entries : Coefficients Key) (key : Key) (value : Value) :
    weighted (fun edge => indicator (member edge value)) (addAlternative meet entries key) =
      weighted (fun edge => indicator (member edge value)) entries +
      indicator (member key value) - indicator (member key value) *
        weighted (fun edge => indicator (member edge value)) entries := by
  simp only [addAlternative, weighted_trim, weighted_insert, weighted_collect,
    weighted_append, weighted_overlaps member meet exact, Int.one_mul]
  omega

/-- The signed fold is a Boolean union indicator, including all overlaps. -/
theorem union_indicator [DecidableEq Key] (member : Key → Value → Bool)
    (meet : Key → Key → Option Key) (exact : ExactMeet member meet)
    (keys : List Key) (value : Value) :
    weighted (fun edge => indicator (member edge value)) (unionCoefficients meet keys) =
      indicator (keys.any fun edge => member edge value) := by
  have loop : ∀ (rest : List Key) (entries : Coefficients Key) (seen : Bool),
      weighted (fun edge => indicator (member edge value)) entries = indicator seen →
      weighted (fun edge => indicator (member edge value))
        (rest.foldl (addAlternative meet) entries) =
      indicator (seen || rest.any fun edge => member edge value) := by
    intro rest
    induction rest with
    | nil => intro entries seen h; simpa using h
    | cons key rest ih =>
        intro entries seen h
        simp only [List.foldl_cons]
        have step : weighted (fun edge => indicator (member edge value))
            (addAlternative meet entries key) = indicator (seen || member key value) := by
          rw [weighted_addAlternative member meet exact, h, Lattice.indicator_or]
          grind
        rw [ih _ _ step]
        simp [Bool.or_assoc]
  simpa [unionCoefficients, indicator] using loop keys [] false rfl

/-- Sum a numeric interpretation over a finite candidate candidates. -/
def totalOver (candidates : List Value) (value : Value → Int) : Int :=
  (candidates.map value).sum

/-- A signed map is linear in the interpretation of its keys. -/
theorem weighted_add (left right : Key → Int) (entries : Coefficients Key) :
    weighted (fun key => left key + right key) entries =
      weighted left entries + weighted right entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simp only [weighted, ih]; grind

/-- Exchanging the finite candidate sum and signed coefficient sum is exact. -/
theorem weighted_totalOver (candidates : List Value) (value : Key → Value → Int)
    (entries : Coefficients Key) :
    weighted (fun key => totalOver candidates (value key)) entries =
      totalOver candidates (fun item => weighted (fun key => value key item) entries) := by
  induction candidates with
  | nil =>
      induction entries with
      | nil => rfl
      | cons entry entries ih => simpa [totalOver, weighted] using ih
  | cons item candidates ih =>
      simp only [totalOver, List.map_cons, List.sum_cons] at *
      rw [weighted_add, ih]

/-- The computed signed count is the number of accepted candidates.
Use a duplicate-free candidates to count distinct terms rather than runs. -/
theorem union_count [DecidableEq Key] (member : Key → Value → Bool)
    (meet : Key → Key → Option Key) (exact : ExactMeet member meet)
    (keys : List Key) (candidates : List Value) :
    weighted (fun key => totalOver candidates (fun item => indicator (member key item)))
        (unionCoefficients meet keys) =
      totalOver candidates (fun item => indicator (keys.any fun key => member key item)) := by
  rw [weighted_totalOver]
  unfold totalOver
  congr 1
  apply List.map_congr_left
  intro item _
  exact union_indicator member meet exact keys item

/-- Concrete finite languages use membership, not multiplicity. -/
def finiteMember [DecidableEq Value] (language : List Value) (value : Value) : Bool :=
  decide (value ∈ language)

/-- Intersect two finite languages and omit an empty intersection. -/
def finiteMeet [DecidableEq Value] (left right : List Value) : Option (List Value) :=
  let common := left.filter fun value => finiteMember right value
  if common.isEmpty then none else some common

/-- The concrete intersection satisfies the required source interface. -/
theorem finiteMeet_exact [DecidableEq Value] : ExactMeet (@finiteMember Value _) finiteMeet := by
  intro left right value
  by_cases h : (left.filter fun item => finiteMember right item).isEmpty = true
  · have hempty : left.filter (fun item => finiteMember right item) = [] := List.isEmpty_iff.mp h
    have hn : ¬ (value ∈ left ∧ value ∈ right) := by
      intro hv
      have hm : value ∈ left.filter (fun item => finiteMember right item) := by
        simp [finiteMember, hv]
      rw [hempty] at hm
      cases hm
    simp only [finiteMeet, h, ↓reduceIte]
    simpa [finiteMember] using hn
  · simp only [finiteMeet, h]
    simp [finiteMember, Bool.decide_and]

/-- Three overlapping alternatives have three distinct values, not six runs. -/
theorem overlap_example :
    weighted (fun edge => totalOver [0, 1, 2]
      (fun item => indicator (finiteMember edge item)))
      (unionCoefficients finiteMeet [[0, 1], [1, 2], [0, 2]]) = 3 := by decide

/-- Repeating an alternative does not add ranks. -/
theorem duplicate_alternative_example :
    weighted (fun edge => totalOver [0, 1]
      (fun item => indicator (finiteMember edge item)))
      (unionCoefficients finiteMeet [[0, 1], [0, 1], [0, 1]]) = 2 := by decide

/-- A constructor context. Each var denotes one complete subtree. -/
inductive Fragment (Symbol : Type) where
  | var : Nat → Fragment Symbol
  | constructor : Symbol → List (Fragment Symbol) → Fragment Symbol

mutual
  /-- Instantiate a constructor context with a var assignment. -/
  def instantiate (assignment : Nat → Term Symbol) : Fragment Symbol → Term Symbol
    | .var var => assignment var
    | .constructor symbol children => .node symbol (instantiateMany assignment children)

  /-- Instantiate the ordered children of a constructor context. -/
  def instantiateMany (assignment : Nat → Term Symbol) :
      List (Fragment Symbol) → List (Term Symbol)
    | [] => []
    | child :: rest => instantiate assignment child :: instantiateMany assignment rest
end

mutual
  /-- Substitute a context for all occurrences of one var. -/
  def substitute (var : Nat) (replacement : Fragment Symbol) :
      Fragment Symbol → Fragment Symbol
    | .var other => if other = var then replacement else .var other
    | .constructor symbol children =>
        .constructor symbol (substituteMany var replacement children)

  /-- Substitute one var in each child context. -/
  def substituteMany (var : Nat) (replacement : Fragment Symbol) :
      List (Fragment Symbol) → List (Fragment Symbol)
    | [] => []
    | child :: rest => substitute var replacement child :: substituteMany var replacement rest
end

/-- Substitution and assignment update have exactly the same meaning. -/
theorem instantiate_substitute (assignment : Nat → Term Symbol) (var : Nat)
    (replacement fragment : Fragment Symbol) :
    instantiate assignment (substitute var replacement fragment) =
      instantiate (fun other => if other = var then instantiate assignment replacement
        else assignment other) fragment := by
  induction fragment using Fragment.rec
    (motive_2 := fun children =>
      instantiateMany assignment (substituteMany var replacement children) =
      instantiateMany (fun other => if other = var then instantiate assignment replacement
        else assignment other) children) with
  | var other =>
      by_cases same : other = var <;> simp [substitute, instantiate, same]
  | constructor symbol children ih => simp [substitute, instantiate, ih]
  | nil => rfl
  | cons child rest ihchild ihrest => simp [substituteMany, instantiateMany, ihchild, ihrest]

/-- A path in a constructor context. -/
structure Target (Symbol : Type) where
  fragment : Fragment Symbol
  path : List Nat

/-- A position must exist, or two positions must hold the same subtree. -/
inductive Obligation (Symbol : Type) where
  | exists : Target Symbol → Obligation Symbol
  | equal : Target Symbol → Target Symbol → Obligation Symbol

/-- Evaluate a position after all variables have values. -/
def targetValue (assignment : Nat → Term Symbol) (target : Target Symbol) : Option (Term Symbol) :=
  (instantiate assignment target.fragment).atPath target.path

/-- An equality requires existing positions. Two absent positions do not satisfy it. -/
def Satisfies (assignment : Nat → Term Symbol) : Obligation Symbol → Prop
  | .exists target => ∃ term, targetValue assignment target = some term
  | .equal left right => ∃ term,
      targetValue assignment left = some term ∧ targetValue assignment right = some term

/-- A constructor context and its pending path requirements. -/
structure Problem (Symbol : Type) where
  domains : List (Nat × List (Term Symbol))
  bindings : List (Nat × Fragment Symbol)
  nextVariable : Nat
  obligations : List (Obligation Symbol)

/-- The concrete meaning of every field except the fresh-name supply. -/
def Solution (problem : Problem Symbol) (assignment : Nat → Term Symbol) : Prop :=
  (∀ entry ∈ problem.domains, assignment entry.1 ∈ entry.2) ∧
  (∀ entry ∈ problem.bindings, assignment entry.1 = instantiate assignment entry.2) ∧
  (∀ obligation ∈ problem.obligations, Satisfies assignment obligation)

/-- One equality class becomes one existence test and a star of equality tests. -/
def classObligations (context : Fragment Symbol) : List (List Nat) → List (Obligation Symbol)
  | [] => []
  | first :: rest => .exists ⟨context, first⟩ ::
      rest.map (fun path => .equal ⟨context, first⟩ ⟨context, path⟩)

/-- The source converts each path class separately. -/
def edgeObligations (context : Fragment Symbol) (classes : List (List (List Nat))) :
    List (Obligation Symbol) := classes.flatMap (classObligations context)

/-- A nonempty class has one common existing value. The empty class has no requirement. -/
def ClassSatisfied (term : Term Symbol) : List (List Nat) → Prop
  | [] => True
  | first :: rest => ∃ common, term.atPath first = some common ∧
      ∀ path ∈ rest, term.atPath path = some common

/-- The star representation preserves all equalities and path existence. -/
theorem classObligations_correct (context : Fragment Symbol)
    (assignment : Nat → Term Symbol) (paths : List (List Nat)) :
    (∀ obligation ∈ classObligations context paths, Satisfies assignment obligation) ↔
      ClassSatisfied (instantiate assignment context) paths := by
  cases paths with
  | nil => simp [classObligations, ClassSatisfied]
  | cons first rest =>
      simp only [classObligations, List.forall_mem_cons, List.forall_mem_map,
        Satisfies, targetValue, ClassSatisfied]
      constructor
      · rintro ⟨⟨common, hfirst⟩, hrest⟩
        refine ⟨common, hfirst, ?_⟩
        intro path member
        obtain ⟨other, hleft, hright⟩ := hrest path member
        have same : other = common := Option.some.inj (hleft.symm.trans hfirst)
        simpa [same] using hright
      · rintro ⟨common, hfirst, hrest⟩
        exact ⟨⟨common, hfirst⟩, fun path member => ⟨common, hfirst, hrest path member⟩⟩

/-- Converting all edge classes preserves their conjunction. -/
theorem edgeObligations_correct (context : Fragment Symbol)
    (assignment : Nat → Term Symbol) (classes : List (List (List Nat))) :
    (∀ obligation ∈ edgeObligations context classes, Satisfies assignment obligation) ↔
      ∀ paths ∈ classes, ClassSatisfied (instantiate assignment context) paths := by
  constructor
  · intro holds paths member
    apply (classObligations_correct context assignment paths).mp
    intro obligation inside
    exact holds obligation (List.mem_flatMap.mpr ⟨paths, member, inside⟩)
  · intro holds obligation member
    obtain ⟨paths, inside, requirement⟩ := List.mem_flatMap.mp member
    exact (classObligations_correct context assignment paths).mpr
      (holds paths inside) obligation requirement

/-- Normalization of `Equal target target` must keep its existence requirement. -/
theorem self_equality_iff_exists (assignment : Nat → Term Symbol) (target : Target Symbol) :
    Satisfies assignment (.equal target target) ↔ Satisfies assignment (.exists target) := by
  simp [Satisfies]

/-- An empty path exists for every instantiated context. -/
theorem empty_path_exists (assignment : Nat → Term Symbol) (fragment : Fragment Symbol) :
    Satisfies assignment (.exists ⟨fragment, []⟩) := by
  exact ⟨instantiate assignment fragment, rfl⟩

/-- A singleton equality class cannot be deleted when its path is absent. -/
theorem singleton_class_counterexample :
    ¬ ClassSatisfied (Term.node 0 []) [[0]] := by
  simp [ClassSatisfied, Term.atPath]

/-- Unifying two constructors requires equal symbols and equal ordered children. -/
theorem constructor_equality (assignment : Nat → Term Symbol)
    (left right : Symbol) (children others : List (Fragment Symbol)) :
    instantiate assignment (.constructor left children) =
        instantiate assignment (.constructor right others) ↔
      left = right ∧ instantiateMany assignment children = instantiateMany assignment others := by
  simp [instantiate, Term.node.injEq]

/-- Whole-var unification replaces two domain tests by their intersection. -/
theorem variable_intersection [DecidableEq Value] (left right : List Value) (value : Value) :
    value ∈ left.filter (fun item => finiteMember right item) ↔
      value ∈ left ∧ value ∈ right := by
  simp [finiteMember]

/-- A var cannot equal a context that contains it at a strict descendant path. -/
theorem occurs_reject (assignment : Nat → Term Symbol) (var : Nat)
    (fragment : Fragment Symbol) (path : List Nat) (proper : path ≠ [])
    (occurrence : (instantiate assignment fragment).atPath path = some (assignment var)) :
    assignment var ≠ instantiate assignment fragment := by
  intro equal
  have impossible : PathsEqual (instantiate assignment fragment) [] ([] ++ path) := by
    exact ⟨assignment var, by simpa [Term.atPath] using congrArg some equal.symm, occurrence⟩
  exact strict_prefix_paths_not_equal _ [] path proper impossible

/-- Independent domains contribute the product of their cardinalities. -/
theorem independent_product_count (domains : List (List Value)) :
    (products id domains).length = (domains.map List.length).prod := by
  induction domains with
  | nil => rfl
  | cons domain domains ih =>
      simp only [products, id_eq, List.length_flatMap, List.length_map, List.map_cons,
        List.prod_cons]
      simp only [List.map_const', List.sum_replicate_nat, ih]

/-- Enumerate a shared value once, from the intersection of its two domains. -/
def equalProduct [DecidableEq Value] (left right : List Value) : List (Value × Value) :=
  (left.filter fun value => finiteMember right value).map fun value => (value, value)

/-- Shared-domain enumeration gives all and only equality-constrained pairs. -/
theorem equalProduct_members [DecidableEq Value] (left right : List Value) (a b : Value) :
    (a, b) ∈ equalProduct left right ↔ a ∈ left ∧ b ∈ right ∧ a = b := by
  simp [equalProduct, List.mem_map, finiteMember]
  grind

/-- One rank is required per intersection member, not per independent pair. -/
theorem equalProduct_count [DecidableEq Value] (left right : List Value) :
    (equalProduct left right).length = (left.filter fun value => finiteMember right value).length := by
  simp [equalProduct]

/-- Sharing an intersection preserves uniqueness when the original domain has no duplicates. -/
theorem equalProduct_nodup [DecidableEq Value] (left right : List Value) (unique : left.Nodup) :
    (equalProduct left right).Nodup := by
  unfold equalProduct
  apply List.Pairwise.map (R := fun a b : Value => a ≠ b)
  · intro a b different same
    exact different (congrArg Prod.fst same)
  · exact unique.filter _

/-- Read graph states at a path. Parent guards are deliberately omitted. -/
def projectStates (automaton : Automaton State Symbol) : List Nat → List State → List State
  | [], states => states
  | child :: rest, states =>
      projectStates automaton rest (states.flatMap fun state =>
        (automaton state).filterMap fun edge => edge.children[child]?)

/-- A pointwise child relation can be followed by a valid child index. -/
theorem All₂.child {left : List α} {right : List β} {relation : α → β → Prop}
    (paired : Language.All₂ relation left right) (index : Nat) (value : β)
    (found : right[index]? = some value) :
    ∃ state, left[index]? = some state ∧ relation state value := by
  induction paired generalizing index with
  | nil => simp at found
  | cons first rest ih =>
      cases index with
      | zero =>
          have same : _ = value := Option.some.inj found
          subst value
          exact ⟨_, rfl, first⟩
      | succ index => exact ih index found

/-- Every actual subtree is accepted by a state in the projected graph. -/
theorem projection_covers_subterms (automaton : Automaton State Symbol)
    (states : List State) (path : List Nat) (state : State) (term subterm : Term Symbol)
    (member : state ∈ states) (accepted : Accepts automaton state term)
    (found : term.atPath path = some subterm) :
    ∃ projected, projected ∈ projectStates automaton path states ∧ Accepts automaton projected subterm := by
  induction path generalizing states state term with
  | nil =>
      have same : term = subterm := Option.some.inj found
      subst subterm
      exact ⟨state, member, accepted⟩
  | cons child rest ih =>
      cases accepted with
      | node edge children edgeMember childAccepted guard =>
          obtain ⟨childTerm, childFound, subtermFound⟩ := Option.bind_eq_some_iff.mp found
          obtain ⟨childState, stateFound, localAccepted⟩ := All₂.child childAccepted child childTerm childFound
          apply ih _ childState childTerm ?_ localAccepted subtermFound
          exact List.mem_flatMap.mpr ⟨state, member,
            List.mem_filterMap.mpr ⟨edge, edgeMember, stateFound⟩⟩

/-- A singleton projected language fixes the subtree for every actual term.
This justifies returning the unique subtree without restricting siblings. -/
theorem singleton_projection_shortcut (automaton : Automaton State Symbol)
    (root : State) (path : List Nat) (unique term subtree : Term Symbol)
    (singleton : ∀ state ∈ projectStates automaton path [root],
      ∀ value, Accepts automaton state value → value = unique)
    (accepted : Accepts automaton root term) (found : term.atPath path = some subtree) :
    subtree = unique := by
  obtain ⟨state, member, localAccepted⟩ :=
    projection_covers_subterms automaton [root] path root term subtree (by simp) accepted found
  exact singleton state member subtree localAccepted

/-- The constructor tag at a position contains both its symbol and arity. -/
def constructorAt (term : Term Symbol) (path : List Nat) : Option (Symbol × Nat) :=
  (term.atPath path).map fun (.node symbol children) => (symbol, children.length)

/-- Exact semantic conditioning used to specify `condition`. -/
def conditioned [DecidableEq Symbol] (terms : List (Term Symbol))
    (path : List Nat) (constructor : Symbol × Nat) : List (Term Symbol) :=
  terms.filter fun term => decide (constructorAt term path = some constructor)

/-- A conditioned language includes exactly the terms with the selected constructor. -/
theorem conditioned_members [DecidableEq Symbol] (terms : List (Term Symbol))
    (path : List Nat) (constructor : Symbol × Nat) (term : Term Symbol) :
    term ∈ conditioned terms path constructor ↔
      term ∈ terms ∧ constructorAt term path = some constructor := by
  simp [conditioned]

/-- Different constructor blocks do not share a term. -/
theorem constructor_blocks_disjoint [DecidableEq Symbol] (terms : List (Term Symbol))
    (path : List Nat) (first second : Symbol × Nat) (different : first ≠ second)
    (term : Term Symbol) :
    ¬ (term ∈ conditioned terms path first ∧ term ∈ conditioned terms path second) := by
  rintro ⟨left, right⟩
  have hl := (conditioned_members terms path first term).mp left
  have hr := (conditioned_members terms path second term).mp right
  exact different (Option.some.inj (hl.2.symm.trans hr.2))

/-- Every term with an existing position belongs to a constructor block. -/
theorem constructor_blocks_cover [DecidableEq Symbol] (terms : List (Term Symbol))
    (path : List Nat) (term subtree : Term Symbol) (member : term ∈ terms)
    (found : term.atPath path = some subtree) :
    ∃ constructor, term ∈ conditioned terms path constructor := by
  cases subtree with
  | node symbol children =>
      exact ⟨(symbol, children.length), (conditioned_members _ _ _ _).mpr
        ⟨member, by simp [constructorAt, found]⟩⟩

/-- Constructor conditioning preserves a distinct-term enumeration. -/
theorem conditioned_nodup [DecidableEq Symbol] (terms : List (Term Symbol))
    (path : List Nat) (constructor : Symbol × Nat) (unique : terms.Nodup) :
    (conditioned terms path constructor).Nodup := unique.filter _

/-- Select a constructor block, then a local rank. This skips empty blocks. -/
def selectBlock : List (Key × List Value) → Nat → Option Value
  | [], _ => none
  | (_, values) :: rest, rank =>
      if rank < values.length then values[rank]? else selectBlock rest (rank - values.length)

/-- Constructor block selection agrees with indexing their ordered concatenation. -/
theorem selectBlock_correct (blocks : List (Key × List Value)) (rank : Nat) :
    selectBlock blocks rank = (blocks.flatMap Prod.snd)[rank]? := by
  induction blocks generalizing rank with
  | nil => rfl
  | cons block blocks ih =>
      rcases block with ⟨key, values⟩
      simp only [selectBlock, List.flatMap_cons, List.getElem?_append, ih]

/-- The block counter computes its index range without concatenating its values. -/
theorem block_count_correct (blocks : List (Key × List Value)) :
    (blocks.map fun block => block.2.length).sum = (blocks.flatMap Prod.snd).length := by
  simp [List.length_flatMap]

/-- No gaps or out-of-range ranks arise in the constructor-block selector. -/
theorem selectBlock_none_iff (blocks : List (Key × List Value)) (rank : Nat) :
    selectBlock blocks rank = none ↔ (blocks.map fun block => block.2.length).sum ≤ rank := by
  rw [selectBlock_correct, block_count_correct]
  exact List.getElem?_eq_none_iff

/-- The three outcomes of following a target without choosing a variable value. -/
inductive Resolution (Symbol : Type) where
  | resolved : Fragment Symbol → Resolution Symbol
  | absent : Resolution Symbol
  | expand : Nat → Resolution Symbol

/-- Follow a target in a normalized problem, whose bindings are empty. -/
def resolveContext : Fragment Symbol → List Nat → Resolution Symbol
  | fragment, [] => .resolved fragment
  | .var name, _ :: _ => .expand name
  | .constructor _ children, child :: rest =>
      match children[child]? with
      | none => .absent
      | some fragment => resolveContext fragment rest

/-- Instantiation commutes with child lookup. -/
theorem instantiateMany_lookup (assignment : Nat → Term Symbol)
    (children : List (Fragment Symbol)) (child : Nat) :
    (instantiateMany assignment children)[child]? = (children[child]?).map (instantiate assignment) := by
  induction children generalizing child with
  | nil => simp [instantiateMany]
  | cons first rest ih => cases child <;> simp [instantiateMany, ih]

/-- A resolved target has the same value as its returned root context. -/
theorem resolveContext_sound (assignment : Nat → Term Symbol)
    (fragment resolved : Fragment Symbol) (path : List Nat)
    (found : resolveContext fragment path = .resolved resolved) :
    (instantiate assignment fragment).atPath path = some (instantiate assignment resolved) := by
  induction path generalizing fragment with
  | nil =>
      have same : fragment = resolved := Resolution.resolved.inj found
      subst fragment
      rfl
  | cons child rest ih =>
      cases fragment with
      | var name => cases found
      | constructor symbol children =>
          simp only [resolveContext] at found
          cases hchild : children[child]? with
          | none => simp [hchild] at found
          | some subcontext =>
              simp only [hchild] at found
              simpa [instantiate, Term.atPath, instantiateMany_lookup, hchild] using ih subcontext found

/-- An absent target stays absent under every variable assignment. -/
theorem resolveContext_absent (assignment : Nat → Term Symbol)
    (fragment : Fragment Symbol) (path : List Nat)
    (missing : resolveContext fragment path = .absent) :
    (instantiate assignment fragment).atPath path = none := by
  induction path generalizing fragment with
  | nil => cases missing
  | cons child rest ih =>
      cases fragment with
      | var name => cases missing
      | constructor symbol children =>
          simp only [resolveContext] at missing
          cases hchild : children[child]? with
          | none => simp [instantiate, Term.atPath, instantiateMany_lookup, hchild]
          | some subcontext =>
              simp only [hchild] at missing
              simpa [instantiate, Term.atPath, instantiateMany_lookup, hchild] using ih subcontext missing

/-- Follow constructor prefixes and retain any unexpanded variable suffix. -/
def followContext : Fragment Symbol → List Nat → Option (Target Symbol)
  | fragment, [] => some ⟨fragment, []⟩
  | .var name, child :: rest => some ⟨.var name, child :: rest⟩
  | .constructor _ children, child :: rest =>
      (children[child]?).bind fun fragment => followContext fragment rest

/-- Removing resolved constructor prefixes preserves the target value. -/
theorem followContext_sound (assignment : Nat → Term Symbol)
    (fragment : Fragment Symbol) (path : List Nat) (target : Target Symbol)
    (found : followContext fragment path = some target) :
    (instantiate assignment fragment).atPath path = targetValue assignment target := by
  induction path generalizing fragment with
  | nil =>
      have same : ⟨fragment, []⟩ = target := Option.some.inj found
      subst target
      rfl
  | cons child rest ih =>
      cases fragment with
      | var name =>
          have same : ⟨.var name, child :: rest⟩ = target := Option.some.inj found
          subst target
          rfl
      | constructor symbol children =>
          obtain ⟨subcontext, hchild, hrest⟩ := Option.bind_eq_some_iff.mp found
          simpa [instantiate, Term.atPath, instantiateMany_lookup, hchild] using ih subcontext hrest

/-- Failed prefix normalization identifies an absent target. -/
theorem followContext_absent (assignment : Nat → Term Symbol)
    (fragment : Fragment Symbol) (path : List Nat)
    (missing : followContext fragment path = none) :
    (instantiate assignment fragment).atPath path = none := by
  induction path generalizing fragment with
  | nil => cases missing
  | cons child rest ih =>
      cases fragment with
      | var name => cases missing
      | constructor symbol children =>
          simp only [followContext] at missing
          cases hchild : children[child]? with
          | none => simp [instantiate, Term.atPath, instantiateMany_lookup, hchild]
          | some subcontext =>
              simp only [hchild, Option.bind_some] at missing
              simpa [instantiate, Term.atPath, instantiateMany_lookup, hchild] using ih subcontext missing

/-- Swapping equality operands does not change an obligation. -/
theorem equality_symmetric (assignment : Nat → Term Symbol) (left right : Target Symbol) :
    Satisfies assignment (.equal left right) ↔ Satisfies assignment (.equal right left) := by
  simp only [Satisfies, and_comm]

/-- A semantic cache key must retain every independent domain, even if no guard reads it. -/
theorem dropping_free_domain_changes_count :
    (products id ([[0, 1], [0, 1, 2]] : List (List Nat))).length = 6 ∧
    (products id ([[0, 1]] : List (List Nat))).length = 2 := by decide

/-- An unsupported path can require expansion even though one assignment makes it absent. -/
theorem unresolved_is_not_absent :
    resolveContext (Fragment.var (Symbol := Nat) 0) [0] = .expand 0 ∧
    (instantiate (fun _ => Term.node 0 []) (Fragment.var 0)).atPath [0] = none := by
  constructor <;> rfl

/-- Coefficient insertion introduces only its requested key. -/
theorem insert_key_members [DecidableEq Key] (key wanted : Key) (coefficient : Int)
    (entries : Coefficients Key) :
    wanted ∈ (insertCoefficient key coefficient entries).map Prod.fst ↔
      wanted = key ∨ wanted ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [insertCoefficient]
  | cons entry entries ih =>
      rcases entry with ⟨other, previous⟩
      by_cases same : key = other
      · subst other
        simp [insertCoefficient]
      · simp [insertCoefficient, same, ih]
        grind

/-- Inserting a coefficient does not duplicate a map key. -/
theorem insert_keys_nodup [DecidableEq Key] (key : Key) (coefficient : Int)
    (entries : Coefficients Key) (unique : (entries.map Prod.fst).Nodup) :
    ((insertCoefficient key coefficient entries).map Prod.fst).Nodup := by
  induction entries with
  | nil => simp [insertCoefficient]
  | cons entry entries ih =>
      rcases entry with ⟨other, previous⟩
      have splitUnique : other ∉ entries.map Prod.fst ∧ (entries.map Prod.fst).Nodup := by
        simpa using unique
      by_cases same : key = other
      · simpa [insertCoefficient, same] using unique
      · simp only [insertCoefficient, same, ↓reduceIte, List.map_cons, List.nodup_cons]
        exact ⟨fun member =>
          (insert_key_members key other coefficient entries).mp member |>.elim
            (fun equal => same equal.symm) splitUnique.1,
          ih splitUnique.2⟩

/-- Collecting coefficients gives one entry for every distinct key. -/
theorem collect_keys_nodup [DecidableEq Key] (entries : Coefficients Key) :
    ((collect entries).map Prod.fst).Nodup := by
  induction entries with
  | nil => simp [collect]
  | cons entry entries ih =>
      exact insert_keys_nodup _ _ _ ih

/-- Every retained coefficient is nonzero. -/
theorem trim_coefficients_nonzero (entries : Coefficients Key)
    (entry : Key × Int) (member : entry ∈ trim entries) : entry.2 ≠ 0 := by
  simpa using (List.mem_filter.mp member).2

/-- Four independent overlapping alternatives require fifteen distinct intersections. -/
theorem exponential_intersections_example :
    (unionCoefficients finiteMeet
      ([[1, 3, 5, 7, 9, 11, 13, 15], [2, 3, 6, 7, 10, 11, 14, 15],
        [4, 5, 6, 7, 12, 13, 14, 15], [8, 9, 10, 11, 12, 13, 14, 15]] : List (List Nat))).length = 15 := by
  decide

end MicroCFTA.Symbolic
