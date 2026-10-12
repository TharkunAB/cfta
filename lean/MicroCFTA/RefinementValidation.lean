import MicroCFTA.FTAValidation
import MicroCFTA.EpsilonUnion

/-!
# Finite refinement automaton validation

The source checks base constructor names after the explicit FTA view succeeds.
Path traversal follows every alternative and removes repeated node identities.
The cycle set and the finite exposed node table remain explicit inputs.
-/
namespace MicroCFTA.RefinementValidation

/-- A refined transition keeps its base name separate from its refinement. -/
structure Transition (State Symbol Refinement Guard : Type) where
  symbol : Symbol
  refinement : Refinement
  children : List State
  guard : Guard

/-- The exposed alternatives at each finite node identity. -/
abbrev Graph (State Symbol Refinement Guard : Type) := State → List (Transition State Symbol Refinement Guard)

/-- An ordered finite list of located source nodes and their exposed alternatives. -/
abbrev Rows (State Symbol Refinement Guard : Type) := List (State × List (Transition State Symbol Refinement Guard))

/-- Keep the first occurrence of each identity, as the source's nubOrdOn does. -/
def dedup [DecidableEq State] (seen : List State) : List State → List State
  | [] => []
  | first :: rest => if first ∈ seen then dedup seen rest else first :: dedup (first :: seen) rest

/-- Identity deduplication retains exactly the identities not previously seen. -/
theorem dedup_member [DecidableEq State] (seen values : List State) (target : State) :
    target ∈ dedup seen values ↔ target ∈ values ∧ target ∉ seen := by
  induction values generalizing seen with
  | nil => simp [dedup]
  | cons first rest ih =>
      by_cases old : first ∈ seen
      · simp only [dedup, old, ↓reduceIte, ih, List.mem_cons]
        constructor
        · rintro ⟨member, fresh⟩; exact ⟨Or.inr member, fresh⟩
        · rintro ⟨same | member, fresh⟩
          · subst target; exact False.elim (fresh old)
          · exact ⟨member, fresh⟩
      · simp only [dedup, old, ↓reduceIte, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨member, fresh⟩)
          · exact ⟨Or.inl rfl, old⟩
          · exact ⟨Or.inr member, fun present => fresh (Or.inr present)⟩
        · rintro ⟨same | member, fresh⟩
          · exact Or.inl same
          · by_cases same : target = first
            · exact Or.inl same
            · exact Or.inr ⟨member, fun present => present.elim same fresh⟩

/-- No identity occurs twice after deduplication. -/
theorem dedup_nodup [DecidableEq State] (seen values : List State) : (dedup seen values).Nodup := by
  induction values generalizing seen with
  | nil => simp [dedup]
  | cons first rest ih =>
      by_cases old : first ∈ seen
      · simpa [dedup, old] using ih seen
      · simp only [dedup, old, ↓reduceIte, List.nodup_cons]
        exact ⟨by simp [dedup_member], ih (first :: seen)⟩

/-- A fresh deduplication pass preserves every endpoint identity. -/
theorem dedup_new_member [DecidableEq State] (values : List State) (target : State) :
    target ∈ dedup [] values ↔ target ∈ values := by simp [dedup_member]

/-- Source list lookup returns no child for a negative signed index. -/
def childAt (children : List State) : Int → Option State
  | .ofNat index => children[index]?
  | .negSucc _ => none

/-- Every successful signed lookup selects an actual child. -/
theorem childAt_member (children : List State) (index : Int) (child : State)
    (selected : childAt children index = some child) : child ∈ children := by
  cases index with
  | ofNat index => exact List.mem_of_getElem? selected
  | negSucc index => cases selected

/-- Traverse the remaining child indexes through every exposed alternative. -/
def descend [DecidableEq State] (graph : Graph State Symbol Refinement Guard) : List Int → State → List State
  | [], node => [node]
  | index :: rest, node => dedup [] ((graph node).flatMap fun edge =>
      match childAt edge.children index with
      | none => []
      | some child => descend graph rest child)

/-- The first child index belongs to the supplied transition. Empty paths have no node result. -/
def nodesAt [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (edge : Transition State Symbol Refinement Guard) : List Int → List State
  | [] => []
  | index :: rest => match childAt edge.children index with
      | none => []
      | some child => descend graph rest child

/-- An empty transition position denotes the supplied transition itself. -/
def transitionsAt [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (edge : Transition State Symbol Refinement Guard) (target : List Int) : List (Transition State Symbol Refinement Guard) :=
  match target with
  | [] => [edge]
  | _ :: _ => (nodesAt graph edge target).flatMap graph

/-- Independent path reachability chooses one available alternative at each index. -/
inductive Endpoint (graph : Graph State Symbol Refinement Guard) : State → List Int → State → Prop where
  | here (state) : Endpoint graph state [] state
  | child {state index rest child target} (edge : Transition State Symbol Refinement Guard) :
      edge ∈ graph state → childAt edge.children index = some child →
      Endpoint graph child rest target → Endpoint graph state (index :: rest) target

/-- Exposing every alternative and deduplicating identities gives exactly the reachable endpoints. -/
theorem descend_exact [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (path : List Int) (state target : State) : target ∈ descend graph path state ↔ Endpoint graph state path target := by
  induction path generalizing state with
  | nil =>
      constructor
      · intro member
        have same : target = state := by simpa [descend] using member
        subst target
        exact .here state
      · intro reached; cases reached; simp [descend]
  | cons index rest ih =>
      simp only [descend, dedup_new_member, List.mem_flatMap]
      constructor
      · rintro ⟨edge, member, present⟩
        cases selected : childAt edge.children index with
        | none => simp [selected] at present
        | some child => exact .child edge member selected ((ih child).mp (by simpa [selected] using present))
      · intro reached
        cases reached with
        | child edge member selected further =>
            exact ⟨edge, member, by simpa [selected] using (ih _).mpr further⟩

/-- Path traversal returns each endpoint identity at most once. -/
theorem descend_nodup [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (path : List Int) (state : State) : (descend graph path state).Nodup := by
  cases path with
  | nil => simp [descend]
  | cons index rest => exact dedup_nodup _ _

/-- Reachability below a transition includes its first child lookup. -/
def EdgeEndpoint (graph : Graph State Symbol Refinement Guard)
    (edge : Transition State Symbol Refinement Guard) (path : List Int) (target : State) : Prop :=
  ∃ index rest child, path = index :: rest ∧ childAt edge.children index = some child ∧ Endpoint graph child rest target

/-- The source nodesAt recursion returns all and only the path endpoints. -/
theorem nodesAt_exact [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (edge : Transition State Symbol Refinement Guard) (path : List Int) (target : State) :
    target ∈ nodesAt graph edge path ↔ EdgeEndpoint graph edge path target := by
  cases path with
  | nil => simp [nodesAt, EdgeEndpoint]
  | cons index rest =>
      constructor
      · intro member
        cases selected : childAt edge.children index with
        | none => simp [nodesAt, selected] at member
        | some child => exact ⟨index, rest, child, rfl, selected,
            (descend_exact graph rest child target).mp (by simpa [nodesAt, selected] using member)⟩
      · rintro ⟨selectedIndex, selectedRest, child, same, selected, reached⟩
        rcases List.cons.inj same with ⟨rfl, rfl⟩
        simpa [nodesAt, selected, descend_exact] using reached

/-- The source nodesAt result contains no repeated identity. -/
theorem nodesAt_nodup [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (edge : Transition State Symbol Refinement Guard) (path : List Int) : (nodesAt graph edge path).Nodup := by
  cases path with
  | nil => simp [nodesAt]
  | cons index rest =>
      cases selected : childAt edge.children index with
      | none => simp [nodesAt, selected]
      | some child => simpa [nodesAt, selected] using descend_nodup graph rest child

/-- A negative first child index yields no endpoints. -/
theorem nodesAt_negative [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (edge : Transition State Symbol Refinement Guard) (index : Nat) (rest : List Int) :
    nodesAt graph edge (Int.negSucc index :: rest) = [] := rfl

/-- The empty path case and all nonempty alternative cases follow the public transition API. -/
theorem transitionsAt_exact [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (edge result : Transition State Symbol Refinement Guard) (path : List Int) :
    result ∈ transitionsAt graph edge path ↔
      (path = [] ∧ result = edge) ∨ ∃ state, EdgeEndpoint graph edge path state ∧ result ∈ graph state := by
  cases path with
  | nil => simp [transitionsAt, EdgeEndpoint]
  | cons index rest => simp [transitionsAt, List.mem_flatMap, nodesAt_exact]

/-- Validation checks the owning node when a guard path is empty. -/
def endpoints [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (owner : State) (edge : Transition State Symbol Refinement Guard) : List Int → List State
  | [] => [owner]
  | index :: rest => nodesAt graph edge (index :: rest)

/-- A guard endpoint is either its owner or a reached child-path endpoint. -/
def GuardEndpoint (graph : Graph State Symbol Refinement Guard) (owner : State)
    (edge : Transition State Symbol Refinement Guard) (path : List Int) (target : State) : Prop :=
  (path = [] ∧ target = owner) ∨ EdgeEndpoint graph edge path target

/-- The validator's endpoint list has exactly the independently defined meaning. -/
theorem endpoints_exact [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (owner : State) (edge : Transition State Symbol Refinement Guard) (path : List Int) (target : State) :
    target ∈ endpoints graph owner edge path ↔ GuardEndpoint graph owner edge path target := by
  cases path with
  | nil => simp [endpoints, GuardEndpoint, EdgeEndpoint]
  | cons index rest => simp [endpoints, GuardEndpoint, nodesAt_exact]

/-- Read base constructor names, independently of their refinements. -/
def arityEntries (rows : Rows State Symbol Refinement Guard) : List (Symbol × Nat) :=
  (rows.flatMap Prod.snd).map fun edge => (edge.symbol, edge.children.length)

/-- A single base-symbol arity assignment describes every located transition. -/
def Consistent (rows : Rows State Symbol Refinement Guard) : Prop :=
  ∃ assignment : Symbol → Nat, ∀ owner edges, (owner, edges) ∈ rows →
    ∀ edge ∈ edges, assignment edge.symbol = edge.children.length

/-- The reused executable arity loop checks exactly the base-symbol condition. -/
theorem arities_exact [DecidableEq Symbol] (rows : Rows State Symbol Refinement Guard) :
    (∃ after, FTAValidation.checkArities (fun _ => none) (arityEntries rows) = .ok after) ↔ Consistent rows := by
  rw [FTAValidation.check_exact]
  constructor
  · rintro ⟨assignment, _, describes⟩
    refine ⟨assignment, ?_⟩
    intro owner edges located edge member
    exact describes (edge.symbol, edge.children.length)
      (List.mem_map.mpr ⟨edge, List.mem_flatMap.mpr ⟨(owner, edges), located, member⟩, rfl⟩)
  · rintro ⟨assignment, consistent⟩
    refine ⟨assignment, by simp [FTAValidation.Extends], ?_⟩
    intro entry member
    change entry ∈ (rows.flatMap Prod.snd).map (fun edge => (edge.symbol, edge.children.length)) at member
    obtain ⟨edge, edgeMember, same⟩ := List.mem_map.mp member
    obtain ⟨⟨owner, edges⟩, located, found⟩ := List.mem_flatMap.mp edgeMember
    cases same
    exact consistent owner edges located edge found

/-- Every cyclic endpoint contributes its edge and guard path in source traversal order. -/
def offending [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (paths : Guard → List (List Int)) (cyclic : State → Bool) (rows : Rows State Symbol Refinement Guard) :
    List (Transition State Symbol Refinement Guard × List Int) :=
  rows.flatMap fun (owner, edges) => edges.flatMap fun edge =>
    (paths edge.guard).flatMap fun path =>
      ((endpoints graph owner edge path).filter cyclic).map fun _ => (edge, path)

/-- The offending list enumerates all listed paths and all cyclic endpoints. -/
theorem offending_exact [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (paths : Guard → List (List Int)) (cyclic : State → Bool) (rows : Rows State Symbol Refinement Guard)
    (edge : Transition State Symbol Refinement Guard) (path : List Int) :
    (edge, path) ∈ offending graph paths cyclic rows ↔
      ∃ owner edges, (owner, edges) ∈ rows ∧ edge ∈ edges ∧ path ∈ paths edge.guard ∧
        ∃ target, GuardEndpoint graph owner edge path target ∧ cyclic target = true := by
  simp only [offending, List.mem_flatMap, List.mem_map, List.mem_filter, endpoints_exact]
  constructor
  · rintro ⟨⟨owner, edges⟩, located, found, member, targetPath, listed, target, reached, same⟩
    have edgeEq := congrArg Prod.fst same
    have pathEq := congrArg Prod.snd same
    simp only at edgeEq pathEq
    subst found
    subst targetPath
    exact ⟨owner, edges, located, member, listed, target, reached⟩
  · rintro ⟨owner, edges, located, member, listed, target, reached⟩
    exact ⟨(owner, edges), located, edge, member, path, listed, target, reached, rfl⟩

/-- No listed guard path reaches a state supplied as cyclic. -/
def NoCyclicGuard (graph : Graph State Symbol Refinement Guard)
    (paths : Guard → List (List Int)) (cyclic : State → Bool) (rows : Rows State Symbol Refinement Guard) : Prop :=
  ∀ owner edges, (owner, edges) ∈ rows → ∀ edge ∈ edges, ∀ path ∈ paths edge.guard,
    ∀ target, GuardEndpoint graph owner edge path target → cyclic target = false

/-- A guard on the empty path checks the owning node itself. -/
theorem empty_guard_checks_owner (graph : Graph State Symbol Refinement Guard)
    (paths : Guard → List (List Int)) (cyclic : State → Bool) (rows : Rows State Symbol Refinement Guard)
    (safe : NoCyclicGuard graph paths cyclic rows) (owner : State)
    (edges : List (Transition State Symbol Refinement Guard)) (located : (owner, edges) ∈ rows)
    (edge : Transition State Symbol Refinement Guard) (member : edge ∈ edges) (listed : [] ∈ paths edge.guard) :
    cyclic owner = false := safe owner edges located edge member [] listed owner (Or.inl ⟨rfl, rfl⟩)

/-- The complete offending scan is empty exactly when every listed endpoint is permitted. -/
theorem offending_empty [DecidableEq State] (graph : Graph State Symbol Refinement Guard)
    (paths : Guard → List (List Int)) (cyclic : State → Bool) (rows : Rows State Symbol Refinement Guard) :
    offending graph paths cyclic rows = [] ↔ NoCyclicGuard graph paths cyclic rows := by
  constructor
  · intro empty owner edges located edge member path listed target reached
    cases cycle : cyclic target with
    | false => rfl
    | true =>
        have found := (offending_exact graph paths cyclic rows edge path).mpr
          ⟨owner, edges, located, member, listed, target, reached, cycle⟩
        simp [empty] at found
  · intro safe
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨edge, path⟩ member
    obtain ⟨owner, edges, located, member, listed, target, reached, cycle⟩ :=
      (offending_exact graph paths cyclic rows edge path).mp member
    simp [safe owner edges located edge member path listed target reached] at cycle

/-- Structural validation preserves the source error precedence. -/
inductive Error (State Symbol Refinement Guard : Type) where
  | inconsistent : FTAValidation.ArityError Symbol → Error State Symbol Refinement Guard
  | cyclicGuard : Transition State Symbol Refinement Guard → List Int → Error State Symbol Refinement Guard

/-- Validate exposed finite rows after the source explicit-view check succeeds. -/
def validate [DecidableEq State] [DecidableEq Symbol] (graph : Graph State Symbol Refinement Guard)
    (paths : Guard → List (List Int)) (cyclic : State → Bool) (rows : Rows State Symbol Refinement Guard) :
    Except (Error State Symbol Refinement Guard) Unit :=
  match FTAValidation.checkArities (fun _ => none) (arityEntries rows) with
  | .error error => .error (.inconsistent error)
  | .ok _ => match offending graph paths cyclic rows with
    | [] => .ok ()
    | (edge, path) :: _ => .error (.cyclicGuard edge path)

/-- Successful validation is exactly consistent base arity and absence of cyclic guard endpoints. -/
theorem validate_exact [DecidableEq State] [DecidableEq Symbol] (graph : Graph State Symbol Refinement Guard)
    (paths : Guard → List (List Int)) (cyclic : State → Bool) (rows : Rows State Symbol Refinement Guard) :
    validate graph paths cyclic rows = .ok () ↔ Consistent rows ∧ NoCyclicGuard graph paths cyclic rows := by
  cases arities : FTAValidation.checkArities (fun _ => none) (arityEntries rows) with
  | error error =>
      have invalid : ¬ Consistent rows := by
        intro valid
        obtain ⟨after, found⟩ := (arities_exact rows).mpr valid
        simp [arities] at found
      simp [validate, arities, invalid]
  | ok after =>
      have valid := (arities_exact rows).mp ⟨after, arities⟩
      rw [← offending_empty]
      cases blocked : offending graph paths cyclic rows with
      | nil => simp [validate, arities, blocked, valid]
      | cons first rest => cases first; simp [validate, arities, blocked]

/-- Every alternative contributes its ordered child requests to located traversal. -/
def children (graph : Graph State Symbol Refinement Guard) (state : State) : List State :=
  (graph state).flatMap Transition.children

/-- Visit each finite identity once and return its row in identity order. -/
def located [DecidableEq State] [Ord State] (states : List State)
    (graph : Graph State Symbol Refinement Guard) (root : Option State) : Rows State Symbol Refinement Guard :=
  match root with
  | none => []
  | some initial =>
      ((EpsilonUnion.visit (children graph) states [initial]).mergeSort
        (fun left right => compare left right != .gt)).map fun state => (state, graph state)

/-- The located worklist returns exactly the reachable exposed rows. -/
theorem located_exact [DecidableEq State] [Ord State] (states : List State)
    (complete : ∀ state, state ∈ states) (unique : states.Nodup)
    (graph : Graph State Symbol Refinement Guard) (root state : State)
    (edges : List (Transition State Symbol Refinement Guard)) :
    (state, edges) ∈ located states graph (some root) ↔
      Productivity.Reachable (children graph) [root] state ∧ edges = graph state := by
  simp only [located, List.mem_map, List.mem_mergeSort, EpsilonUnion.visit_exact states complete unique, Prod.mk.injEq]
  constructor
  · rintro ⟨state, reached, rfl, same⟩
    exact ⟨reached, same.symm⟩
  · rintro ⟨reached, same⟩
    exact ⟨state, reached, rfl, same.symm⟩

/-- Reaching a child by an index also reaches it in the located worklist. -/
theorem selected_reachable (graph : Graph State Symbol Refinement Guard) (root state : State)
    (reached : Productivity.Reachable (children graph) [root] state)
    (edge : Transition State Symbol Refinement Guard) (member : edge ∈ graph state)
    (index : Int) (child : State) (selected : childAt edge.children index = some child) :
    Productivity.Reachable (children graph) [root] child :=
  .step reached (List.mem_flatMap.mpr ⟨edge, member, childAt_member edge.children index child selected⟩)

/-- Every finite descendant endpoint is among the graph's reachable identities. -/
theorem endpoint_reachable (graph : Graph State Symbol Refinement Guard) (root : State)
    {state path target} (endpoint : Endpoint graph state path target)
    (reached : Productivity.Reachable (children graph) [root] state) :
    Productivity.Reachable (children graph) [root] target := by
  induction endpoint with
  | here state => exact reached
  | child edge member selected further ih =>
      exact ih (selected_reachable graph root _ reached edge member _ _ selected)

/-- The validator never inspects an identity outside the located reachability domain. -/
theorem guard_endpoint_reachable (graph : Graph State Symbol Refinement Guard) (root owner : State)
    (reached : Productivity.Reachable (children graph) [root] owner)
    (edge : Transition State Symbol Refinement Guard) (member : edge ∈ graph owner)
    (path : List Int) (target : State) (endpoint : GuardEndpoint graph owner edge path target) :
    Productivity.Reachable (children graph) [root] target := by
  rcases endpoint with ⟨_, rfl⟩ | ⟨index, rest, child, _, selected, further⟩
  · exact reached
  · exact endpoint_reachable graph root further (selected_reachable graph root owner reached edge member index child selected)

/-- Located arity checking quantifies over exactly the reachable source alternatives. -/
theorem located_consistent [DecidableEq State] [Ord State] (states : List State)
    (complete : ∀ state, state ∈ states) (unique : states.Nodup)
    (graph : Graph State Symbol Refinement Guard) (root : State) :
    Consistent (located states graph (some root)) ↔
      ∃ assignment : Symbol → Nat, ∀ state, Productivity.Reachable (children graph) [root] state →
        ∀ edge ∈ graph state, assignment edge.symbol = edge.children.length := by
  constructor
  · rintro ⟨assignment, consistent⟩
    exact ⟨assignment, fun state reached edge member =>
      consistent state (graph state) ((located_exact states complete unique graph root state _).mpr ⟨reached, rfl⟩) edge member⟩
  · rintro ⟨assignment, consistent⟩
    refine ⟨assignment, ?_⟩
    intro state edges located edge member
    obtain ⟨reached, rfl⟩ := (located_exact states complete unique graph root state edges).mp located
    exact consistent state reached edge member

/-- Located guard checking quantifies over every endpoint of every reachable transition. -/
theorem located_guards [DecidableEq State] [Ord State] (states : List State)
    (complete : ∀ state, state ∈ states) (unique : states.Nodup)
    (graph : Graph State Symbol Refinement Guard) (root : State)
    (paths : Guard → List (List Int)) (cyclic : State → Bool) :
    NoCyclicGuard graph paths cyclic (located states graph (some root)) ↔
      ∀ owner, Productivity.Reachable (children graph) [root] owner →
        ∀ edge ∈ graph owner, ∀ path ∈ paths edge.guard,
          ∀ target, GuardEndpoint graph owner edge path target → cyclic target = false := by
  constructor
  · intro safe owner reached edge member path listed target endpoint
    exact safe owner (graph owner) ((located_exact states complete unique graph root owner _).mpr ⟨reached, rfl⟩)
      edge member path listed target endpoint
  · intro safe owner edges located edge member path listed target endpoint
    obtain ⟨reached, rfl⟩ := (located_exact states complete unique graph root owner edges).mp located
    exact safe owner reached edge member path listed target endpoint

/-- The complete finite traversal and source validator enforce exactly both structural requirements. -/
theorem validate_located_exact [DecidableEq State] [Ord State] [DecidableEq Symbol]
    (states : List State) (complete : ∀ state, state ∈ states) (unique : states.Nodup)
    (graph : Graph State Symbol Refinement Guard) (root : State)
    (paths : Guard → List (List Int)) (cyclic : State → Bool) :
    validate graph paths cyclic (located states graph (some root)) = .ok () ↔
      (∃ assignment : Symbol → Nat, ∀ state, Productivity.Reachable (children graph) [root] state →
        ∀ edge ∈ graph state, assignment edge.symbol = edge.children.length) ∧
      (∀ owner, Productivity.Reachable (children graph) [root] owner →
        ∀ edge ∈ graph owner, ∀ path ∈ paths edge.guard,
          ∀ target, GuardEndpoint graph owner edge path target → cyclic target = false) := by
  rw [validate_exact, located_consistent states complete unique, located_guards states complete unique]

end MicroCFTA.RefinementValidation
