import MicroCFTA.Productivity
import MicroCFTA.ObservationGraph

/-!
# Exact elimination of recursive union references

An epsilon edge selects another state without consuming a constructor.
Interned unions and binder references use these edges. A transition keeps
its symbol, ordered children, and guard. Epsilon cycles use least finite-run
semantics; they do not create a term by themselves.
-/

namespace MicroCFTA.EpsilonUnion
open Language Productivity

/-- A finite graph can contain constructor transitions and epsilon references. -/
structure Graph (State Symbol : Type) where
  references : State → List State
  transitions : Automaton State Symbol

/-- Independent finite-run semantics before epsilon elimination. -/
inductive Accepts (graph : Graph State Symbol) : State → Term Symbol → Prop where
  | reference {source target : State} {term : Term Symbol} :
      target ∈ graph.references source → Accepts graph target term → Accepts graph source term
  | node (edge : Edge State Symbol) (children : List (Term Symbol)) :
      edge ∈ graph.transitions state → All₂ (Accepts graph) edge.children children →
      edge.guard (.node edge.label children) = true → Accepts graph state (.node edge.label children)

/-- Constructor rows reached through finite epsilon paths. -/
def eliminate [DecidableEq State] (states : List State) (graph : Graph State Symbol) : Automaton State Symbol :=
  fun source => (states.filter (reachClosure states graph.references [source])).flatMap graph.transitions

/-- A copied transition occurs exactly at an epsilon-reachable original state. -/
theorem edge_exact [DecidableEq State] (states : List State) (complete : ∀ state, state ∈ states)
    (graph : Graph State Symbol) (source : State) (edge : Edge State Symbol) :
    edge ∈ eliminate states graph source ↔
      ∃ target, Reachable graph.references [source] target ∧ edge ∈ graph.transitions target := by
  simp only [eliminate, List.mem_flatMap, List.mem_filter,
    reachClosure_correct states complete]
  constructor
  · rintro ⟨target, ⟨_, reachable⟩, member⟩
    exact ⟨target, reachable, member⟩
  · rintro ⟨target, reachable, member⟩
    exact ⟨target, ⟨complete target, reachable⟩, member⟩

/-- A finite epsilon path transports an accepting run back to its start. -/
theorem along_reference (graph : Graph State Symbol) (source target : State)
    (reachable : Reachable graph.references [source] target) (term : Term Symbol)
    (accepted : Accepts graph target term) : Accepts graph source term := by
  induction reachable with
  | seed present =>
      simp only [List.mem_singleton] at present
      subst_vars
      exact accepted
  | @step parent child before member ih =>
      exact ih (.reference member accepted)

/-- Concatenate finite epsilon paths. -/
theorem reach_trans (next : State → List State) (first middle last : State)
    (left : Reachable next [first] middle) (right : Reachable next [middle] last) :
    Reachable next [first] last := by
  induction right with
  | seed present =>
      simp only [List.mem_singleton] at present
      subst_vars
      exact left
  | step _ member ih => exact .step ih member

/-- Epsilon elimination neither creates nor drops any accepted finite term. -/
theorem eliminate_exact [DecidableEq State] (states : List State)
    (complete : ∀ state, state ∈ states) (graph : Graph State Symbol)
    (source : State) (term : Term Symbol) :
    Language.Accepts (eliminate states graph) source term ↔ Accepts graph source term := by
  constructor
  · intro accepted
    induction accepted using Language.Accepts.rec
      (motive_2 := fun qs ts _ => All₂ (Accepts graph) qs ts) with
    | @node q edge terms member children guard ih =>
        obtain ⟨target, reached, original⟩ := (edge_exact states complete graph q edge).mp member
        exact along_reference graph q target reached _ (.node edge terms original ih guard)
    | nil => exact .nil
    | cons _ _ child children => exact .cons child children
  · intro accepted
    induction accepted using Accepts.rec
      (motive_2 := fun qs ts _ => All₂ (Language.Accepts (eliminate states graph)) qs ts) with
    | @reference q target term member accepted ih =>
        cases ih with
        | node edge terms copied children guard =>
            obtain ⟨last, reached, original⟩ := (edge_exact states complete graph target edge).mp copied
            have first : Reachable graph.references [q] target := .step (.seed (by simp)) member
            exact .node edge terms
              ((edge_exact states complete graph q edge).mpr
                ⟨last, reach_trans _ _ _ _ first reached, original⟩) children guard
    | @node q edge terms member children guard ih =>
        exact .node edge terms
          ((edge_exact states complete graph q edge).mpr ⟨q, .seed (by simp), member⟩) ih guard
    | nil => exact .nil
    | cons _ _ child children => exact .cons child children

/-- A state consisting only of epsilon operands denotes their exact union. -/
theorem union_exact (graph : Graph State Symbol) (source : State)
    (noConstructors : graph.transitions source = []) (term : Term Symbol) :
    Accepts graph source term ↔ ∃ member, member ∈ graph.references source ∧ Accepts graph member term := by
  constructor
  · intro accepted
    cases accepted with
    | reference member accepted => exact ⟨_, member, accepted⟩
    | node edge children absent => simp [noConstructors] at absent
  · rintro ⟨member, present, accepted⟩
    exact .reference present accepted

/-- Empty epsilon cycles cannot manufacture a constructor or an accepted term. -/
theorem no_constructor_no_term (graph : Graph State Symbol)
    (empty : ∀ state, graph.transitions state = []) (source : State) (term : Term Symbol) :
    ¬ Accepts graph source term := by
  intro accepted
  induction accepted using Accepts.rec
    (motive_2 := fun _ _ _ => True) with
  | reference _ _ ih => exact ih
  | @node q edge terms member => simp [empty] at member
  | nil => trivial
  | cons => trivial

/-- Source-order depth-first closure. `available` is the complement of the visited set. -/
def visit [DecidableEq State] (next : State → List State)
    (available pending : List State) : List State :=
  match pending with
  | [] => []
  | state :: rest =>
      if _fresh : state ∈ available then
        state :: visit next (available.erase state) (next state ++ rest)
      else visit next available rest
termination_by (available.length, pending.length)
decreasing_by
  · apply Prod.Lex.left
    rw [List.length_erase_of_mem _fresh]
    have positive := List.length_pos_of_mem _fresh
    omega
  · apply Prod.Lex.right
    simp

/-- A state was visited previously or is included in the new traversal result. -/
def Covered (available found : List State) (state : State) : Prop :=
  state ∉ available ∨ state ∈ found

/-- Restore one just-visited state in the worklist invariant. -/
theorem covered_restore [DecidableEq State] (available found : List State) (state target : State)
    (covered : Covered (available.erase state) found target) :
    Covered available (state :: found) target := by
  by_cases same : target = state
  · exact Or.inr (by simp [same])
  · rcases covered with absent | present
    · exact Or.inl (fun member => absent ((List.mem_erase_of_ne same).mpr member))
    · exact Or.inr (by simp [present])

/-- All five facts needed to connect the source worklist to graph reachability. -/
structure VisitSpec (next : State → List State) (available pending found : List State) : Prop where
  allocated : ∀ state ∈ found, state ∈ available
  distinct : found.Nodup
  requested : ∀ state ∈ pending, Covered available found state
  closed : ∀ state ∈ found, ∀ child ∈ next state, Covered available found child
  reachable : ∀ state ∈ found, Reachable next pending state

/-- A path remains reachable when each of its seeds is reachable in another frontier. -/
theorem change_seeds (next : State → List State) (before after : List State)
    (included : ∀ state ∈ before, Reachable next after state) (target : State)
    (path : Reachable next before target) : Reachable next after target := by
  induction path with
  | seed member => exact included _ member
  | step _ member ih => exact .step ih member

/-- The terminating depth-first loop visits precisely its reachable unvisited states. -/
theorem visit_spec [DecidableEq State] (next : State → List State)
    (available pending : List State) (unique : available.Nodup) :
    VisitSpec next available pending (visit next available pending) := by
  induction available, pending using visit.induct next with
  | case1 available =>
      simp only [visit]
      exact ⟨by simp, by simp, by simp, by simp, by simp⟩
  | case2 available state rest fresh ih =>
      have tail := ih (unique.erase state)
      simp only [visit, fresh, ↓reduceDIte]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro target member
        rcases List.mem_cons.mp member with same | later
        · simpa [same] using fresh
        · exact List.mem_of_mem_erase (tail.allocated target later)
      · apply List.nodup_cons.mpr
        refine ⟨?_, tail.distinct⟩
        intro repeated
        have member := tail.allocated state repeated
        exact unique.not_mem_erase member
      · intro target member
        rcases List.mem_cons.mp member with same | later
        · exact Or.inr (by simp [same])
        · exact covered_restore available _ state target (tail.requested target (by simp [later]))
      · intro target member child edge
        rcases List.mem_cons.mp member with same | later
        · subst target
          exact covered_restore available _ state child (tail.requested child (by simp [edge]))
        · exact covered_restore available _ state child (tail.closed target later child edge)
      · intro target member
        rcases List.mem_cons.mp member with same | later
        · exact .seed (by simp [same])
        · apply change_seeds next (next state ++ rest) (state :: rest) ?_ target (tail.reachable target later)
          intro seed member
          rcases List.mem_append.mp member with child | old
          · exact .step (.seed (by simp)) child
          · exact .seed (by simp [old])
  | case3 available state rest old ih =>
      have tail := ih unique
      simp only [visit, old, ↓reduceDIte]
      refine ⟨tail.allocated, tail.distinct, ?_, tail.closed, ?_⟩
      · intro target member
        rcases List.mem_cons.mp member with same | later
        · subst target
          exact Or.inl old
        · exact tail.requested target later
      · intro target member
        exact change_seeds next rest (state :: rest)
          (fun seed member => .seed (by simp [member])) target (tail.reachable target member)

/-- On a complete finite state set, the source worklist computes exact epsilon reachability. -/
theorem visit_exact [DecidableEq State] (states : List State) (complete : ∀ state, state ∈ states)
    (unique : states.Nodup) (next : State → List State) (seeds : List State) (target : State) :
    target ∈ visit next states seeds ↔ Reachable next seeds target := by
  have spec := visit_spec next states seeds unique
  constructor
  · exact spec.reachable target
  · intro reached
    induction reached with
    | seed member =>
        exact (spec.requested _ member).resolve_left (fun absent => absent (complete _))
    | step _ edge ih =>
        exact (spec.closed _ ih _ edge).resolve_left (fun absent => absent (complete _))

/-- Constructor collection after the depth-first worklist. -/
def collect [DecidableEq State] (states : List State) (graph : Graph State Symbol) : Automaton State Symbol :=
  fun source => (visit graph.references states [source]).flatMap graph.transitions

/-- The source-order closure has the same finite language as the independent epsilon graph. -/
theorem collect_exact [DecidableEq State] (states : List State) (complete : ∀ state, state ∈ states)
    (unique : states.Nodup) (graph : Graph State Symbol) (source : State) (term : Term Symbol) :
    Language.Accepts (collect states graph) source term ↔ Accepts graph source term := by
  have rows : ∀ q edge, edge ∈ collect states graph q ↔ edge ∈ eliminate states graph q := by
    intro q edge
    simp only [collect, List.mem_flatMap, visit_exact states complete unique]
    exact (edge_exact states complete graph q edge).symm
  have equivalent : ∀ A B : Automaton State Symbol,
      (∀ q edge, edge ∈ A q ↔ edge ∈ B q) →
      ∀ q t, Language.Accepts A q t → Language.Accepts B q t := by
    intro A B same q t accepted
    induction accepted using Language.Accepts.rec
      (motive_2 := fun qs ts _ => All₂ (Language.Accepts B) qs ts) with
    | @node q edge terms member children guard ih => exact .node edge terms ((same q edge).mp member) ih guard
    | nil => exact .nil
    | cons _ _ child children => exact .cons child children
  constructor
  · intro accepted
    exact (eliminate_exact states complete graph source term).mp
      (equivalent _ _ rows source term accepted)
  · intro accepted
    exact equivalent _ _ (fun q edge => (rows q edge).symm) source term
      ((eliminate_exact states complete graph source term).mpr accepted)

end MicroCFTA.EpsilonUnion
