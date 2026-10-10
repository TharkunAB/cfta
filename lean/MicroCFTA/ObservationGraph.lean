import MicroCFTA.Observation

/-!
# Structural specialization of a cyclic graph by a finite observation plan

New nodes contain specialized alternatives. Unobserved children remain
references to the original graph. The graph may contain cycles. Specialization
recurses only through the finite observation plan, represented here by an
explicit recursion budget.

The graph representation does not intern nodes or memoize repeated queries.
Original recursive references are ordinary graph states. Mapping the Haskell
binder and interning representations to these states remains separate.
-/

namespace MicroCFTA.ObservationGraph
open MicroCFTA.Language MicroCFTA.Observation

/-- A finite fragment with references to the unchanged original graph. -/
inductive Node (State Symbol : Type) where
  | original (state : State)
  | branches (edges : List (Edge (Node State Symbol) Symbol))

/-- Finite acceptance in a specialized fragment and its original graph references. -/
inductive AcceptsNode (automaton : Automaton State Symbol) : Node State Symbol → Term Symbol → Prop where
  | original : Accepts automaton state term → AcceptsNode automaton (.original state) term
  | branch (edge : Edge (Node State Symbol) Symbol) (terms : List (Term Symbol)) :
      edge ∈ edges → All₂ (AcceptsNode automaton) edge.children terms →
      edge.guard (.node edge.label terms) = true →
      AcceptsNode automaton (.branches edges) (.node edge.label terms)

/-- A transition builds a term from accepted children and a successful guard. -/
def Fits (accepts : State → Term Symbol → Prop) (edge : Edge State Symbol) (term : Term Symbol) : Prop :=
  ∃ terms, term = .node edge.label terms ∧ All₂ accepts edge.children terms ∧ edge.guard term = true

/-- The original graph accepts exactly the terms of its outgoing transitions. -/
theorem accepts_iff_edge (automaton : Automaton State Symbol) (state : State) (term : Term Symbol) :
    Accepts automaton state term ↔ ∃ edge, edge ∈ automaton state ∧ Fits (Accepts automaton) edge term := by
  constructor
  · intro accepted
    cases accepted with
    | node edge terms member runs guard => exact ⟨edge, member, terms, rfl, runs, guard⟩
  · rintro ⟨edge, member, terms, rfl, runs, guard⟩
    exact .node edge terms member runs guard

/-- An unchanged graph reference has exactly the original language. -/
theorem original_accepts_iff (automaton : Automaton State Symbol) (state : State) (term : Term Symbol) :
    AcceptsNode automaton (.original state) term ↔ Accepts automaton state term := by
  constructor
  · intro accepted
    cases accepted with | original run => exact run
  · exact .original

/-- A specialized node denotes the union of the languages of its alternatives. -/
theorem branches_accepts_iff (automaton : Automaton State Symbol)
    (edges : List (Edge (Node State Symbol) Symbol)) (term : Term Symbol) :
    AcceptsNode automaton (.branches edges) term ↔
      ∃ edge, edge ∈ edges ∧ Fits (AcceptsNode automaton) edge term := by
  constructor
  · intro accepted
    cases accepted with
    | branch edge terms member runs guard => exact ⟨edge, member, terms, rfl, runs, guard⟩
  · rintro ⟨edge, member, terms, rfl, runs, guard⟩
    exact .branch edge terms member runs guard

/-- A graph variant carries the observations common to its terms. -/
structure Variant (State Symbol Refinement : Type) where
  node : Node State (Label Symbol Refinement)
  view : Path → Option (Entry Symbol Refinement)

/-- A transition candidate before alternatives with equal keys are regrouped. -/
structure Candidate (State Symbol Refinement : Type) where
  edge : Edge (Node State (Label Symbol Refinement)) (Label Symbol Refinement)
  view : Path → Option (Entry Symbol Refinement)

mutual
  /-- All positions represented in the finite trie. -/
  def planPaths : Plan → List Path
    | .node observation children =>
        (if observation.isSome then [[]] else []) ++ planChildrenPaths children

  /-- Prefix and concatenate the paths in a sparse child map. -/
  def planChildrenPaths : List (Nat × Plan) → List Path
    | [] => []
    | entry :: rest => planChildPaths entry ++ planChildrenPaths rest

  /-- Prefix one sparse child's paths with its index. -/
  def planChildPaths : Nat × Plan → List Path
    | (index, child) => (planPaths child).map (index :: ·)
end

/-- A finite comparison key for one sparse signature. -/
def viewKey (plan : Plan) (view : Path → Option (Entry Symbol Refinement)) :
    List (Option (Entry Symbol Refinement)) := (planPaths plan).map view

/-- Collect one homogeneous group into a single graph node. -/
def groupedVariant (members : List (Candidate State Symbol Refinement)) : Variant State Symbol Refinement :=
  ⟨.branches (members.map Candidate.edge),
    fun path => members.head?.bind (fun first => first.view path)⟩

/-- Group transition alternatives by their complete finite observation key. -/
def groupCandidates [DecidableEq Symbol] [DecidableEq Refinement] (plan : Plan)
    (candidates : List (Candidate State Symbol Refinement)) : List (Variant State Symbol Refinement) :=
  ((candidates.map (fun candidate => viewKey plan candidate.view)).eraseDups).map
    (fun key => groupedVariant (candidates.filter (fun candidate => decide (viewKey plan candidate.view = key))))

/-- Regrouping an arbitrary candidate list preserves its exact union language. -/
theorem groupCandidates_cover [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (plan : Plan)
    (candidates : List (Candidate State Symbol Refinement)) (term : Term (Label Symbol Refinement)) :
    (∃ variant, variant ∈ groupCandidates plan candidates ∧ AcceptsNode automaton variant.node term) ↔
      ∃ candidate, candidate ∈ candidates ∧ Fits (AcceptsNode automaton) candidate.edge term := by
  constructor
  · rintro ⟨variant, member, accepted⟩
    obtain ⟨key, _, same⟩ := List.mem_map.mp member
    subst variant
    obtain ⟨edge, member, fits⟩ := (branches_accepts_iff automaton _ term).mp accepted
    obtain ⟨candidate, filtered, same⟩ := List.mem_map.mp member
    subst edge
    exact ⟨candidate, (List.mem_filter.mp filtered).1, fits⟩
  · rintro ⟨candidate, member, fits⟩
    let key := viewKey plan candidate.view
    have keyMember : key ∈ (candidates.map (fun candidate => viewKey plan candidate.view)).eraseDups :=
      List.mem_eraseDups.mpr (List.mem_map.mpr ⟨candidate, member, rfl⟩)
    have filtered : candidate ∈ candidates.filter (fun candidate => decide (viewKey plan candidate.view = key)) :=
      List.mem_filter.mpr ⟨member, by simp [key]⟩
    refine ⟨_, List.mem_map.mpr ⟨key, keyMember, rfl⟩, ?_⟩
    exact (branches_accepts_iff automaton _ term).mpr
      ⟨candidate.edge, List.mem_map.mpr ⟨candidate, filtered, rfl⟩, fits⟩

/-- An unobserved child stays shared as an original graph reference. -/
def originalVariant (state : State) : Variant State Symbol Refinement :=
  ⟨.original state, fun _ => none⟩

/-- Specialize a requested child, or preserve an unobserved reference. -/
def childChoices (previous : Plan → State → List (Variant State Symbol Refinement))
    (planned : List (Nat × Plan)) (child : State × Nat) : List (Variant State Symbol Refinement) :=
  match childAt child.2 planned with
  | none => [originalVariant child.1]
  | some childPlan => previous childPlan child.1

/-- The root signature reads the edge label and its actual child count. -/
def rootEntry (need : Need) (edge : Edge State (Label Symbol Refinement)) : Entry Symbol Refinement :=
  match need with
  | .refinement => .refinement edge.label.refinement
  | .symbol => .symbol ⟨edge.label, edge.children.isEmpty⟩

/-- Assemble one specialized edge and prefix its child observation functions. -/
def assemble (plan : Plan) (edge : Edge State (Label Symbol Refinement))
    (children : List (Variant State Symbol Refinement)) : Candidate State Symbol Refinement :=
  match plan with
  | .node observation _ =>
      ⟨⟨edge.label, children.map Variant.node, edge.guard⟩,
        fun path => match path with
          | [] => observation.map (fun need => rootEntry need edge)
          | index :: rest => children[index]?.bind (fun child => child.view rest)⟩

/-- Build the Cartesian product of specialized child choices for one edge. -/
def edgeCandidates (previous : Plan → State → List (Variant State Symbol Refinement))
    (plan : Plan) (edge : Edge State (Label Symbol Refinement)) : List (Candidate State Symbol Refinement) :=
  match plan with
  | .node _ planned =>
      (products (childChoices previous planned) edge.children.zipIdx).map (assemble plan edge)

/-- Specialize only as far as the finite observation plan requests. -/
def specialize [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) :
    Nat → Plan → State → List (Variant State Symbol Refinement)
  | 0, _, state => [originalVariant state]
  | fuel + 1, plan, state =>
      groupCandidates plan ((automaton state).flatMap (edgeCandidates (specialize automaton fuel) plan))

/-- Move a function on the left list into a pointwise relation. -/
theorem all₂_map_left (map : α → β) (relation : β → γ → Prop) (left : List α) (right : List γ) :
    All₂ relation (left.map map) right ↔ All₂ (fun value result => relation (map value) result) left right := by
  induction left generalizing right with
  | nil =>
      constructor <;> intro related <;> cases related <;> exact .nil
  | cons value rest ih =>
      constructor
      · intro related
        cases related with
        | cons head tail => exact .cons head ((ih _).mp tail)
      · intro related
        cases related with
        | cons head tail => exact .cons head ((ih _).mpr tail)

/-- Factor a pointwise existential relation into one finite middle list. -/
theorem all₂_factor (left : List α) (right : List γ) (first : α → β → Prop) (second : β → γ → Prop) :
    All₂ (fun a c => ∃ b, first a b ∧ second b c) left right ↔
      ∃ middle, All₂ first left middle ∧ All₂ second middle right := by
  constructor
  · intro related
    induction related with
    | nil => exact ⟨[], .nil, .nil⟩
    | cons head tail ih =>
        obtain ⟨value, hf, hs⟩ := head
        obtain ⟨values, hfs, hss⟩ := ih
        exact ⟨value :: values, .cons hf hfs, .cons hs hss⟩
  · rintro ⟨middle, hf, hs⟩
    induction hf generalizing right with
    | nil => cases hs; exact .nil
    | cons head tail ih =>
        cases hs with
        | cons head' tail' => exact .cons ⟨_, head, head'⟩ (ih _ tail')

/-- A child choice preserves its original state language when recursive choices do. -/
theorem childChoices_cover (automaton : Automaton State (Label Symbol Refinement))
    (previous : Plan → State → List (Variant State Symbol Refinement))
    (correct : ∀ plan state term,
      (∃ variant, variant ∈ previous plan state ∧ AcceptsNode automaton variant.node term) ↔
        Accepts automaton state term)
    (planned : List (Nat × Plan)) (child : State × Nat) (term : Term (Label Symbol Refinement)) :
    (∃ variant, variant ∈ childChoices previous planned child ∧ AcceptsNode automaton variant.node term) ↔
      Accepts automaton child.1 term := by
  cases found : childAt child.2 planned with
  | none => simp [childChoices, found, originalVariant, original_accepts_iff]
  | some childPlan => simpa [childChoices, found] using correct childPlan child.1 term

/-- Cartesian child specialization preserves one edge's complete accepted language. -/
theorem edgeCandidates_cover (automaton : Automaton State (Label Symbol Refinement))
    (previous : Plan → State → List (Variant State Symbol Refinement))
    (correct : ∀ plan state term,
      (∃ variant, variant ∈ previous plan state ∧ AcceptsNode automaton variant.node term) ↔
        Accepts automaton state term)
    (plan : Plan) (edge : Edge State (Label Symbol Refinement)) (term : Term (Label Symbol Refinement)) :
    (∃ candidate, candidate ∈ edgeCandidates previous plan edge ∧
      Fits (AcceptsNode automaton) candidate.edge term) ↔ Fits (Accepts automaton) edge term := by
  cases plan with
  | node observation planned =>
      constructor
      · rintro ⟨candidate, member, terms, shape, runs, guard⟩
        obtain ⟨variants, selected, same⟩ := List.mem_map.mp member
        subst candidate
        have selections := (mem_products _ _ _).mp selected
        have childRuns := (all₂_map_left Variant.node (AcceptsNode automaton) variants terms).mp runs
        have combined := (all₂_factor _ _ _ _).mpr ⟨variants, selections, childRuns⟩
        have original := combined.imp (fun child term witness =>
          (childChoices_cover automaton previous correct planned child term).mp witness)
        have mapped := (all₂_map_left Prod.fst (Accepts automaton) edge.children.zipIdx terms).mpr original
        rw [List.zipIdx_map_fst] at mapped
        exact ⟨terms, shape, mapped, guard⟩
      · rintro ⟨terms, shape, runs, guard⟩
        have indexed : All₂ (fun child term => Accepts automaton child.1 term) edge.children.zipIdx terms := by
          apply (all₂_map_left Prod.fst (Accepts automaton) edge.children.zipIdx terms).mp
          simpa using runs
        have choices := indexed.imp (fun child term run =>
          (childChoices_cover automaton previous correct planned child term).mpr run)
        obtain ⟨variants, selected, childRuns⟩ := (all₂_factor _ _ _ _).mp choices
        refine ⟨assemble (.node observation planned) edge variants,
          List.mem_map.mpr ⟨variants, (mem_products _ _ _).mpr selected, rfl⟩, terms, shape, ?_, guard⟩
        exact (all₂_map_left Variant.node (AcceptsNode automaton) variants terms).mpr childRuns

/-- Structural specialization preserves every accepted finite term of a cyclic graph. -/
theorem specialize_cover [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (fuel : Nat) (plan : Plan)
    (state : State) (term : Term (Label Symbol Refinement)) :
    (∃ variant, variant ∈ specialize automaton fuel plan state ∧ AcceptsNode automaton variant.node term) ↔
      Accepts automaton state term := by
  induction fuel generalizing plan state term with
  | zero => simp [specialize, originalVariant, original_accepts_iff]
  | succ fuel ih =>
      rw [specialize, groupCandidates_cover, accepts_iff_edge]
      constructor
      · rintro ⟨candidate, member, fits⟩
        obtain ⟨edge, originalMember, selected⟩ := List.mem_flatMap.mp member
        exact ⟨edge, originalMember,
          (edgeCandidates_cover automaton (specialize automaton fuel) ih plan edge term).mp
            ⟨candidate, selected, fits⟩⟩
      · rintro ⟨edge, member, fits⟩
        obtain ⟨candidate, selected, accepted⟩ :=
          (edgeCandidates_cover automaton (specialize automaton fuel) ih plan edge term).mpr fits
        exact ⟨candidate, List.mem_flatMap.mpr ⟨edge, member, selected⟩, accepted⟩

/-- A requested child contributes its paths to the finite trie path list. -/
theorem childAt_mem_planPaths (children : List (Nat × Plan)) (index : Nat) (child : Plan)
    (found : childAt index children = some child) (path : Path) (member : path ∈ planPaths child) :
    index :: path ∈ planChildrenPaths children := by
  induction children with
  | nil => simp [childAt] at found
  | cons entry rest ih =>
      obtain ⟨key, previous⟩ := entry
      by_cases same : index = key
      · subst key
        have equal : previous = child := by simpa [childAt] using found
        subst previous
        exact List.mem_append_left _ (List.mem_map.mpr ⟨path, member, rfl⟩)
      · apply List.mem_append_right
        exact ih (by simpa [childAt, same] using found)

/-- Every requested path occurs in the finite key domain. -/
theorem lookup_mem_planPaths (plan : Plan) (path : Path) (need : Need)
    (requested : lookup plan path = some need) : path ∈ planPaths plan := by
  induction path generalizing plan with
  | nil =>
      cases plan with
      | node observation children =>
          have equal : observation = some need := requested
          simp [planPaths, equal]
  | cons index rest ih =>
      cases plan with
      | node observation children =>
          obtain ⟨child, found, request⟩ := Option.bind_eq_some_iff.mp requested
          exact List.mem_append_right _
            (childAt_mem_planPaths children index child found rest (ih child request))

/-- Sparse observations have no entries outside their planned requests. -/
def Supported (plan : Plan) (view : Path → Option (Entry Symbol Refinement)) : Prop :=
  ∀ path, lookup plan path = none → view path = none

/-- Equal finite keys determine the entire supported sparse observation function. -/
theorem viewKey_ext (plan : Plan) (left right : Path → Option (Entry Symbol Refinement))
    (leftSupported : Supported plan left) (rightSupported : Supported plan right)
    (same : viewKey plan left = viewKey plan right) : left = right := by
  funext path
  cases found : lookup plan path with
  | none => rw [leftSupported path found, rightSupported path found]
  | some need =>
      exact List.map_eq_map_iff.mp same path (lookup_mem_planPaths plan path need found)

/-- The recursion budget reaches every requested observation. -/
def PlanBound (fuel : Nat) (plan : Plan) : Prop :=
  ∀ path need, lookup plan path = some need → path.length < fuel

/-- A child plan consumes one level of the parent budget. -/
theorem child_plan_bound (observation : Option Need) (children : List (Nat × Plan))
    (fuel index : Nat) (child : Plan) (parent : PlanBound (fuel + 1) (.node observation children))
    (found : childAt index children = some child) : PlanBound fuel child := by
  intro path need requested
  have extended : lookup (.node observation children) (index :: path) = some need := by
    simp [lookup, found, requested]
  have bound := parent (index :: path) need extended
  simp only [List.length_cons] at bound
  omega

/-- The greatest requested path length, plus one for its root observation. -/
def planBudget (plan : Plan) : Nat :=
  (planPaths plan).foldr (fun path depth => max path.length depth) 0 + 1

/-- A path's length is bounded by the maximum over its finite list. -/
theorem path_length_le_fold (paths : List Path) (path : Path) (member : path ∈ paths) :
    path.length ≤ paths.foldr (fun path depth => max path.length depth) 0 := by
  induction paths with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih tail) (Nat.le_max_right _ _)

/-- The executable budget is sufficient for every request in an arbitrary finite trie. -/
theorem planBudget_sufficient (plan : Plan) : PlanBound (planBudget plan) plan := by
  intro path need requested
  exact Nat.lt_succ_of_le (path_length_le_fold (planPaths plan) path
    (lookup_mem_planPaths plan path need requested))

/-- Relate optional entries at the same index of two aligned lists. -/
def OptionRel (relation : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some left, some right => relation left right
  | _, _ => False

/-- Pointwise list relations preserve index lookup, including absent positions. -/
theorem all₂_at (relation : α → β → Prop) {left : List α} {right : List β}
    (related : All₂ relation left right) (index : Nat) :
    OptionRel relation left[index]? right[index]? := by
  induction related generalizing index with
  | nil => simp [OptionRel]
  | cons head tail ih =>
      cases index with
      | zero => exact head
      | succ index => exact ih index

/-- A selected child at an index belongs to the choices for that exact graph child. -/
theorem selected_at
    (choices : State × Nat → List (Variant State Symbol Refinement))
    (states : List State) (variants : List (Variant State Symbol Refinement))
    (selected : All₂ (fun child variant => variant ∈ choices child) states.zipIdx variants)
    (index : Nat) (variant : Variant State Symbol Refinement)
    (found : variants[index]? = some variant) :
    ∃ state, states[index]? = some state ∧ variant ∈ choices (state, index) := by
  have related := all₂_at _ selected index
  rw [found, List.getElem?_zipIdx] at related
  cases child : states[index]? with
  | none => simp [child, OptionRel] at related
  | some state => exact ⟨state, rfl, by simpa [child, OptionRel] using related⟩

/-- A variant's stored observation is supported and exact for every accepted term. -/
def ValidVariant (automaton : Automaton State (Label Symbol Refinement)) (plan : Plan)
    (variant : Variant State Symbol Refinement) : Prop :=
  Supported plan variant.view ∧
    ∀ term, AcceptsNode automaton variant.node term → variant.view = signature plan term

/-- A candidate has the corresponding supported, exact observation invariant. -/
def ValidCandidate (automaton : Automaton State (Label Symbol Refinement)) (plan : Plan)
    (candidate : Candidate State Symbol Refinement) : Prop :=
  Supported plan candidate.view ∧
    ∀ term, Fits (AcceptsNode automaton) candidate.edge term → candidate.view = signature plan term

/-- Grouping equal keys preserves the exact observation invariant of graph candidates. -/
theorem groupCandidates_valid [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (plan : Plan)
    (candidates : List (Candidate State Symbol Refinement))
    (valid : ∀ candidate, candidate ∈ candidates → ValidCandidate automaton plan candidate)
    (variant : Variant State Symbol Refinement) (member : variant ∈ groupCandidates plan candidates) :
    ValidVariant automaton plan variant := by
  obtain ⟨key, _, same⟩ := List.mem_map.mp member
  subst variant
  let members := candidates.filter (fun candidate => decide (viewKey plan candidate.view = key))
  change ValidVariant automaton plan (groupedVariant members)
  have belongs : ∀ candidate, candidate ∈ members →
      candidate ∈ candidates ∧ viewKey plan candidate.view = key := by
    intro candidate member
    exact ⟨(List.mem_filter.mp member).1, by simpa using (List.mem_filter.mp member).2⟩
  cases hm : members with
  | nil =>
      constructor
      · intro path _
        simp [groupedVariant]
      · intro term accepted
        have witnesses := (branches_accepts_iff automaton _ term).mp accepted
        simp at witnesses
  | cons first rest =>
      have firstMember : first ∈ members := by simp [hm]
      have firstValid := valid first (belongs first firstMember).1
      constructor
      · simpa [groupedVariant, hm] using firstValid.1
      · intro term accepted
        obtain ⟨edge, edgeMember, fits⟩ := (branches_accepts_iff automaton _ term).mp accepted
        obtain ⟨candidate, candidateMember, same⟩ := List.mem_map.mp edgeMember
        subst edge
        have originalCandidateMember : candidate ∈ members := by simpa [hm] using candidateMember
        have candidateValid := valid candidate (belongs candidate originalCandidateMember).1
        have sameViews := viewKey_ext plan first.view candidate.view firstValid.1 candidateValid.1
          ((belongs first firstMember).2.trans (belongs candidate originalCandidateMember).2.symm)
        simpa [groupedVariant, hm] using sameViews.trans (candidateValid.2 term fits)

/-- A selected child's observation is exact for its optional child plan. -/
def ChildValid (automaton : Automaton State (Label Symbol Refinement))
    (planned : List (Nat × Plan)) (index : Nat) (variant : Variant State Symbol Refinement) : Prop :=
  (∀ path, (childAt index planned).bind (fun plan => lookup plan path) = none → variant.view path = none) ∧
    ∀ term, AcceptsNode automaton variant.node term →
      variant.view = fun path => (childAt index planned).bind (fun plan => signature plan term path)

/-- Recursive child specialization supplies exact observations for the chosen child. -/
theorem childChoices_valid (automaton : Automaton State (Label Symbol Refinement))
    (previous : Plan → State → List (Variant State Symbol Refinement)) (fuel : Nat)
    (valid : ∀ plan, PlanBound fuel plan → ∀ state variant,
      variant ∈ previous plan state → ValidVariant automaton plan variant)
    (observation : Option Need) (planned : List (Nat × Plan))
    (bound : PlanBound (fuel + 1) (.node observation planned))
    (child : State × Nat) (variant : Variant State Symbol Refinement)
    (member : variant ∈ childChoices previous planned child) : ChildValid automaton planned child.2 variant := by
  cases found : childAt child.2 planned with
  | none =>
      have same : variant = originalVariant child.1 := by simpa [childChoices, found] using member
      subst variant
      constructor
      · intro path _
        rfl
      · intro term _
        funext path
        simp [originalVariant, found]
  | some childPlan =>
      have childBound := child_plan_bound observation planned fuel child.2 childPlan bound found
      have childValid := valid childPlan childBound child.1 variant
        (by simpa [childChoices, found] using member)
      constructor
      · intro path absent
        exact childValid.1 path (by simpa [found] using absent)
      · intro term accepted
        simpa [found] using childValid.2 term accepted

/-- Lists of the same length agree on whether they are empty. -/
theorem isEmpty_of_length_eq (left : List α) (right : List β) (same : left.length = right.length) :
    left.isEmpty = right.isEmpty := by
  cases left <;> cases right <;> simp_all

/-- Root and prefixed child observations are exact for a specialized edge. -/
theorem assemble_valid (automaton : Automaton State (Label Symbol Refinement))
    (previous : Plan → State → List (Variant State Symbol Refinement))
    (observation : Option Need) (planned : List (Nat × Plan))
    (edge : Edge State (Label Symbol Refinement)) (variants : List (Variant State Symbol Refinement))
    (selected : All₂ (fun child variant => variant ∈ childChoices previous planned child)
      edge.children.zipIdx variants)
    (valid : ∀ child variant, variant ∈ childChoices previous planned child →
      ChildValid automaton planned child.2 variant) :
    ValidCandidate automaton (.node observation planned) (assemble (.node observation planned) edge variants) := by
  constructor
  · intro path absent
    cases path with
    | nil =>
        have empty : observation = none := absent
        simp [assemble, empty]
    | cons index rest =>
        cases found : variants[index]? with
        | none => simp [assemble, found]
        | some variant =>
            obtain ⟨state, _, chosen⟩ := selected_at _ edge.children variants selected index variant found
            have absentChild := (valid (state, index) variant chosen).1 rest absent
            simpa [assemble, found] using absentChild
  · rintro term ⟨terms, shape, runs, guard⟩
    have shape' : term = .node edge.label terms := shape
    subst term
    have childRuns := (all₂_map_left Variant.node (AcceptsNode automaton) variants terms).mp runs
    have childLength : edge.children.length = variants.length := by simpa using selected.length_eq
    have sameLeaf := isEmpty_of_length_eq edge.children terms (childLength.trans childRuns.length_eq)
    funext path
    cases path with
    | nil =>
        cases observation with
        | none => rfl
        | some need =>
            cases need <;> simp [assemble, signature, readWith, signatureEntry, rootEntry, rootObservation, sameLeaf]
    | cons index rest =>
        have aligned := all₂_at _ childRuns index
        cases hv : variants[index]? with
        | none =>
            cases ht : terms[index]? with
            | none =>
                cases hp : childAt index planned <;>
                  simp [assemble, hv, signature, readWith, ht, hp]
            | some term => simp [hv, ht, OptionRel] at aligned
        | some variant =>
            cases ht : terms[index]? with
            | none => simp [hv, ht, OptionRel] at aligned
            | some term =>
                obtain ⟨state, _, chosen⟩ := selected_at _ edge.children variants selected index variant hv
                have accepted : AcceptsNode automaton variant.node term := by
                  simpa [hv, ht, OptionRel] using aligned
                have sameView := (valid (state, index) variant chosen).2 term accepted
                simp only [assemble, hv, Option.bind_some]
                rw [congrFun sameView rest]
                cases hp : childAt index planned <;>
                  simp [signature, readWith, ht, hp]

/-- Every graph variant has the observations that its complete accepted terms produce. -/
theorem specialize_valid [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (fuel : Nat) (plan : Plan)
    (bound : PlanBound fuel plan) (state : State) (variant : Variant State Symbol Refinement)
    (member : variant ∈ specialize automaton fuel plan state) : ValidVariant automaton plan variant := by
  induction fuel generalizing plan state variant with
  | zero =>
      have same : variant = originalVariant state := by simpa [specialize] using member
      subst variant
      constructor
      · intro path _
        rfl
      · intro term _
        funext path
        cases found : lookup plan path with
        | none => simp [originalVariant, signature, readWith_correct, found]
        | some need => have impossible := bound path need found; omega
  | succ fuel ih =>
      apply groupCandidates_valid automaton plan _ ?_ variant member
      intro candidate candidateMember
      obtain ⟨edge, _, selected⟩ := List.mem_flatMap.mp candidateMember
      cases plan with
      | node observation planned =>
          obtain ⟨variants, chosen, same⟩ := List.mem_map.mp selected
          subst candidate
          exact assemble_valid automaton (specialize automaton fuel) observation planned edge variants
            ((mem_products _ _ _).mp chosen)
            (childChoices_valid automaton (specialize automaton fuel) fuel ih observation planned bound)

/-- The finite plan budget specializes every observation, even over cyclic graph references. -/
theorem specialize_exact [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (plan : Plan)
    (state : State) (variant : Variant State Symbol Refinement)
    (member : variant ∈ specialize automaton (planBudget plan) plan state)
    (term : Term (Label Symbol Refinement)) (accepted : AcceptsNode automaton variant.node term) :
    Accepts automaton state term ∧ variant.view = signature plan term := by
  exact ⟨(specialize_cover automaton (planBudget plan) plan state term).mp ⟨variant, member, accepted⟩,
    (specialize_valid automaton (planBudget plan) plan (planBudget_sufficient plan) state variant member).2 term accepted⟩

/-- Every original accepted term appears in a graph variant with its exact sparse signature. -/
theorem specialize_complete [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (plan : Plan)
    (state : State) (term : Term (Label Symbol Refinement)) (accepted : Accepts automaton state term) :
    ∃ variant, variant ∈ specialize automaton (planBudget plan) plan state ∧
      AcceptsNode automaton variant.node term ∧ variant.view = signature plan term := by
  obtain ⟨variant, member, run⟩ := (specialize_cover automaton (planBudget plan) plan state term).mpr accepted
  exact ⟨variant, member, run,
    (specialize_valid automaton (planBudget plan) plan (planBudget_sufficient plan) state variant member).2 term run⟩

/-- Every term in one specialized semantic group has the same complete guard decision. -/
theorem specialized_guard_homogeneous [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State) (variant : Variant State Symbol Refinement)
    (member : variant ∈ specialize automaton (planBudget (guardPlan guard)) (guardPlan guard) state)
    (left right : Term (Label Symbol Refinement))
    (acceptedLeft : AcceptsNode automaton variant.node left)
    (acceptedRight : AcceptsNode automaton variant.node right) :
    verdict queries guard left = verdict queries guard right := by
  have leftView := (specialize_exact automaton (guardPlan guard) state variant member left acceptedLeft).2
  have rightView := (specialize_exact automaton (guardPlan guard) state variant member right acceptedRight).2
  have sameKey := (key_eq_iff_signature_eq guard left right).mpr (leftView.symm.trans rightView)
  exact key_homogeneous queries guard left right sameKey true

/-- Read the refinement from either kind of signature entry. -/
def entryRefinement : Entry Symbol Refinement → Refinement
  | .refinement value => value
  | .symbol observation => observation.label.refinement

/-- The evaluator's refinement view reconstructed from stored sparse observations. -/
def refinementView (view : Path → Option (Entry Symbol Refinement)) : Path → Option Refinement :=
  fun path => (view path).map entryRefinement

/-- Decide a specialized group directly from its stored observations. -/
def variantVerdict (queries : Queries Refinement) (guard : Guards.Guard (Atom Refinement))
    (variant : Variant State Symbol Refinement) : Guards.Verdict :=
  Guards.evaluate (atomQuery queries (refinementView variant.view)) true guard

/-- The stored-view query equals complete-term evaluation for every accepted group member. -/
theorem variantVerdict_correct [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State) (variant : Variant State Symbol Refinement)
    (member : variant ∈ specialize automaton (planBudget (guardPlan guard)) (guardPlan guard) state)
    (term : Term (Label Symbol Refinement)) (accepted : AcceptsNode automaton variant.node term) :
    variantVerdict queries guard variant = verdict queries guard term := by
  have exactView := (specialize_exact automaton (guardPlan guard) state variant member term accepted).2
  apply guardQuery_ext
  intro path used
  have request : lookup (guardPlan guard) path = some .refinement := by
    simp [lookup_guardPlan, used]
  simp only [refinementView, exactView]
  rw [signature_refinement (guardPlan guard) term path request]
  cases refinementAt term path <;> rfl

/-- Retain proved groups, drop refuted groups, and report solver uncertainty. -/
def selectDecided (decision : α → Guards.Verdict) : List α → Option (List α)
  | [] => some []
  | member :: rest => match decision member with
      | .yes => (selectDecided decision rest).map (member :: ·)
      | .no => selectDecided decision rest
      | .unknown => none

/-- A successful decision pass returns exactly the proved groups. -/
theorem selectDecided_eq_filter (decision : α → Guards.Verdict) (members kept : List α)
    (success : selectDecided decision members = some kept) :
    kept = members.filter (fun member => decide (decision member = .yes)) := by
  induction members generalizing kept with
  | nil => simpa [selectDecided] using success.symm
  | cons member rest ih =>
      cases found : decision member with
      | unknown => simp [selectDecided, found] at success
      | no =>
          have recursive : selectDecided decision rest = some kept := by
            simpa [selectDecided, found] using success
          simpa [found] using ih kept recursive
      | yes =>
          cases remaining : selectDecided decision rest with
          | none => simp [selectDecided, found, remaining] at success
          | some tail =>
              have result : kept = member :: tail := by simpa [selectDecided, found, remaining] using success.symm
              rw [result, ih tail remaining]
              simp [found]

/-- A successful decision pass preserves precisely the proved memberships. -/
theorem mem_selectDecided (decision : α → Guards.Verdict)
    (members kept : List α) (success : selectDecided decision members = some kept) (member : α) :
    member ∈ kept ↔ member ∈ members ∧ decision member = .yes := by
  rw [selectDecided_eq_filter decision members kept success]
  simp

/-- Specialize a graph by a semantic guard and select from its stored observations. -/
def selectSpecialized [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State) : Option (List (Variant State Symbol Refinement)) :=
  selectDecided (variantVerdict queries guard)
    (specialize automaton (planBudget (guardPlan guard)) (guardPlan guard) state)

/-- Successful sparse graph selection preserves exactly the guard-filtered accepted language. -/
theorem selectSpecialized_correct [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State)
    (kept : List (Variant State Symbol Refinement)) (success : selectSpecialized automaton queries guard state = some kept)
    (term : Term (Label Symbol Refinement)) :
    (∃ variant, variant ∈ kept ∧ AcceptsNode automaton variant.node term) ↔
      Accepts automaton state term ∧ verdict queries guard term = .yes := by
  have keptEq := selectDecided_eq_filter (variantVerdict queries guard) _ kept success
  constructor
  · rintro ⟨variant, member, accepted⟩
    rw [keptEq] at member
    obtain ⟨original, proved⟩ := List.mem_filter.mp member
    have result : variantVerdict queries guard variant = .yes := by simpa using proved
    exact ⟨(specialize_cover automaton _ _ state term).mp ⟨variant, original, accepted⟩,
      (variantVerdict_correct automaton queries guard state variant original term accepted).symm.trans result⟩
  · rintro ⟨accepted, proved⟩
    obtain ⟨variant, member, run, _⟩ := specialize_complete automaton (guardPlan guard) state term accepted
    have decision : variantVerdict queries guard variant = .yes :=
      (variantVerdict_correct automaton queries guard state variant member term run).trans proved
    refine ⟨variant, ?_, run⟩
    rw [keptEq]
    exact List.mem_filter.mpr ⟨member, by simp [decision]⟩

/-- Attach a semantic guard to the root alternatives without changing their children. -/
def guardedRoot (automaton : Automaton State Symbol) (state : State) (test : Term Symbol → Bool) :
    Node State Symbol :=
  .branches ((automaton state).map (fun edge =>
    ⟨edge.label, edge.children.map Node.original, fun term => edge.guard term && test term⟩))

/-- Root guard syntax denotes exactly conjunction with the accepted candidate language. -/
theorem guardedRoot_accepts_iff (automaton : Automaton State Symbol) (state : State)
    (test : Term Symbol → Bool) (term : Term Symbol) :
    AcceptsNode automaton (guardedRoot automaton state test) term ↔
      Accepts automaton state term ∧ test term = true := by
  constructor
  · intro accepted
    obtain ⟨edge, member, terms, shape, runs, checks⟩ := (branches_accepts_iff automaton _ term).mp accepted
    obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
    subst edge
    have shape' : term = .node original.label terms := shape
    have children := (all₂_map_left Node.original (AcceptsNode automaton) original.children terms).mp runs
    have originalChildren := children.imp (fun state term accepted =>
      (original_accepts_iff automaton state term).mp accepted)
    have guards := (Bool.and_eq_true _ _).mp checks
    subst term
    exact ⟨.node original terms originalMember originalChildren guards.1, guards.2⟩
  · rintro ⟨accepted, succeeds⟩
    cases accepted with
    | node edge terms member runs guard =>
        have children := (all₂_map_left Node.original (AcceptsNode automaton) edge.children terms).mpr
          (runs.imp (fun _ _ accepted => AcceptsNode.original accepted))
        exact .branch _ terms (List.mem_map.mpr ⟨edge, member, rfl⟩) children
          (by simp [guard, succeeds])

/-- Specialization and successful sparse decisions discharge the root semantic guard exactly. -/
theorem selectSpecialized_discharges_guard [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (queries : Queries Refinement)
    (guard : Guards.Guard (Atom Refinement)) (state : State)
    (kept : List (Variant State Symbol Refinement)) (success : selectSpecialized automaton queries guard state = some kept)
    (term : Term (Label Symbol Refinement)) :
    (∃ variant, variant ∈ kept ∧ AcceptsNode automaton variant.node term) ↔
      AcceptsNode automaton
        (guardedRoot automaton state (fun term => decide (verdict queries guard term = .yes))) term := by
  rw [selectSpecialized_correct automaton queries guard state kept success term, guardedRoot_accepts_iff]
  simp

end MicroCFTA.ObservationGraph
