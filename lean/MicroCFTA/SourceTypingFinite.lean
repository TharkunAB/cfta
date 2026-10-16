import MicroCFTA.SourceTypingRules

/-!
# Finite source typing-goal exploration

Every literal candidate child decreases a lexicographic rank. A finite
occurrence inventory therefore exists without a finite type or environment
carrier. Its length bounds the pending work of the visited-map traversal.

The traversal uses completed resolved candidate rows. Source validation can
fail before or during row production. Error precedence, codecs, native Map
storage, and lazy automaton import remain separate source adapters. Arbitrary
fixed values do not imply closedness or a target-datatype nesting bound.
-/
namespace MicroCFTA.SourceTypingFinite
open Language SourceTypingRules
variable {Ty Symbol : Type}

/-- Compare the complete source goal, including every literal fixed subtree. -/
def goalDecidableEq [DecidableEq Ty] [DecidableEq Symbol] : DecidableEq (Goal Ty Symbol) := by
  letI : DecidableEq (Term Symbol) := fun left right =>
    decidable_of_iff (termEq left right = true) (termEq_correct left right)
  intro left right
  cases left with
  | root =>
      cases right with
      | root => exact isTrue rfl
      | typed => exact isFalse (by intro same; cases same)
      | fixed => exact isFalse (by intro same; cases same)
  | typed env typ remaining =>
      cases right with
      | root => exact isFalse (by intro same; cases same)
      | typed otherEnv otherTyp otherRemaining =>
          exact decidable_of_iff (env = otherEnv ∧ typ = otherTyp ∧ remaining = otherRemaining)
            (by simp only [Goal.typed.injEq])
      | fixed => exact isFalse (by intro same; cases same)
  | fixed term =>
      cases right with
      | root => exact isFalse (by intro same; cases same)
      | typed => exact isFalse (by intro same; cases same)
      | fixed other => exact decidable_of_iff (term = other) (by simp only [Goal.fixed.injEq])

/-- Root is above the initial typed budget; fixed terms have primary rank zero. -/
def primary (bound : Int) : Goal Ty Symbol → Nat
  | .root => bound.toNat + 2
  | .typed _ _ remaining => remaining.toNat + 1
  | .fixed _ => 0

/-- Only fixed trees need a secondary rank. -/
def secondary : Goal Ty Symbol → Nat
  | .fixed term => term.height
  | _ => 0

/-- The rank permits arbitrarily tall finite fixed values below every typed goal. -/
def rank (bound : Int) (state : Goal Ty Symbol) : Nat × Nat := (primary bound state, secondary state)

private theorem child_primary_le (bound : Int) (env : List Ty) (remaining : Int) (child : Child Ty Symbol) :
    primary bound (childGoal env remaining child) ≤ remaining.toNat + 1 := by
  cases child <;> simp only [childGoal, primary] <;> omega

/-- Every admitted Subterm consumes a positive level; fixed values enter the lower rank family. -/
theorem typed_child_decreases [DecidableEq Ty] (rules : List (Rule Ty Symbol))
    (bound : Int) (env : List Ty) (typ : Ty) (remaining : Int)
    (edge : Language.Edge (Goal Ty Symbol) Symbol) (member : edge ∈ typedRow rules env typ remaining)
    (child : Goal Ty Symbol) (included : child ∈ edge.children) :
    Prod.Lex (· < ·) (· < ·) (rank bound child) (rank bound (.typed env typ remaining : Goal Ty Symbol)) := by
  obtain ⟨alternative, selected, rfl⟩ := List.mem_map.mp member
  obtain ⟨field, fieldIn, rfl⟩ := List.mem_map.mp included
  have admitted := selected_nests rules env typ remaining alternative selected
  cases field with
  | value term =>
      apply Prod.Lex.left
      simp [primary, childGoal]
  | subterm binds typ =>
      have present : alternative.2.any Child.isSubterm = true :=
        List.any_eq_true.mpr ⟨.subterm binds typ, fieldIn, rfl⟩
      have positive : 0 < remaining := by
        simpa only [nests, present, Bool.not_true, Bool.or_false, decide_eq_true_eq] using admitted
      apply Prod.Lex.left
      simp only [primary, childGoal]
      omega

/-- Every actual row child decreases, including children of the inlined root rows. -/
theorem row_child_decreases [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol))
    (bound : Int) (state : Goal Ty Symbol) (edge : Language.Edge (Goal Ty Symbol) Symbol)
    (member : edge ∈ row roots rules bound state) (child : Goal Ty Symbol) (included : child ∈ edge.children) :
    Prod.Lex (· < ·) (· < ·) (rank bound child) (rank bound state) := by
  cases state with
  | typed env typ remaining => exact typed_child_decreases rules bound env typ remaining edge member child included
  | root =>
      obtain ⟨typ, _, selected⟩ := List.mem_flatMap.mp member
      obtain ⟨alternative, _, rfl⟩ := List.mem_map.mp selected
      obtain ⟨field, _, rfl⟩ := List.mem_map.mp included
      have bounded := child_primary_le bound ([] : List Ty) bound field
      apply Prod.Lex.left
      change primary bound (childGoal [] bound field) < bound.toNat + 2
      omega
  | fixed term =>
      cases term with
      | node label terms =>
          have same := List.mem_singleton.mp member
          subst edge
          obtain ⟨term, termIn, rfl⟩ := List.mem_map.mp included
          have bounded := height_le_forestHeight terms term termIn
          apply Prod.Lex.right
          simpa only [rank, primary, secondary, Term.height, forestHeight] using Nat.lt_succ_of_le bounded

/-- Pending child states follow transition order and then field order. -/
def children [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol)) (bound : Int)
    (state : Goal Ty Symbol) : List (Goal Ty Symbol) :=
  (row roots rules bound state).flatMap Language.Edge.children

/-- Concatenating actual transition children preserves their derived rank decrease. -/
theorem children_decrease [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol))
    (bound : Int) (state child : Goal Ty Symbol) (member : child ∈ children roots rules bound state) :
    Prod.Lex (· < ·) (· < ·) (rank bound child) (rank bound state) := by
  obtain ⟨edge, edgeIn, childIn⟩ := List.mem_flatMap.mp member
  exact row_child_decreases roots rules bound state edge edgeIn child childIn

/-- Finite occurrence inventory follows every literal branch; repeated states can occur. -/
def inventory [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol)) (bound : Int)
    (state : Goal Ty Symbol) : List (Goal Ty Symbol) :=
  state :: (children roots rules bound state).attach.flatMap
    (fun child => inventory roots rules bound child.val)
termination_by (primary bound state, secondary state)
decreasing_by
  exact children_decrease roots rules bound state child.val child.property

/-- The original state is an actual inventory occurrence. -/
theorem inventory_self [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol))
    (bound : Int) (state : Goal Ty Symbol) : state ∈ inventory roots rules bound state := by
  rw [inventory]
  exact List.mem_cons_self

/-- A child's finite inventory is contained in its parent's literal branch inventory. -/
theorem inventory_child [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol))
    (bound : Int) (state child : Goal Ty Symbol) (member : child ∈ children roots rules bound state)
    {target : Goal Ty Symbol} (included : target ∈ inventory roots rules bound child) :
    target ∈ inventory roots rules bound state := by
  rw [inventory]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨⟨child, member⟩, by simp, included⟩)

/-- Reachability uses only actual candidate-row child occurrences. -/
inductive Reaches [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol)) (bound : Int) :
    Goal Ty Symbol → Goal Ty Symbol → Prop where
  | refl : Reaches roots rules bound state state
  | step (first : child ∈ children roots rules bound state) (rest : Reaches roots rules bound child target) :
      Reaches roots rules bound state target

/-- Every reachable typed state belongs to the computed finite inventory. -/
theorem Reaches.member [DecidableEq Ty] {roots : List Ty} {rules : List (Rule Ty Symbol)} {bound : Int}
    {state target : Goal Ty Symbol} (actual : Reaches roots rules bound state target) :
    target ∈ inventory roots rules bound state := by
  induction actual with
  | refl => exact inventory_self _ _ _ _
  | step first _ ih => exact inventory_child _ _ _ _ _ first ih

/-- The finite inventory contains only states reached by the actual candidate branches. -/
theorem inventory_reaches [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol))
    (bound : Int) (state target : Goal Ty Symbol) (member : target ∈ inventory roots rules bound state) :
    Reaches roots rules bound state target := by
  rw [inventory] at member
  rcases List.mem_cons.mp member with same | later
  · subst target
    exact .refl
  · obtain ⟨child, _, included⟩ := List.mem_flatMap.mp later
    exact .step child.property (inventory_reaches roots rules bound child.val target included)
termination_by (primary bound state, secondary state)
decreasing_by
  exact children_decrease roots rules bound state child.val child.property

/-- The explicit finite list classifies the whole reachable graph exactly. -/
theorem inventory_iff [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol))
    (bound : Int) (state target : Goal Ty Symbol) :
    target ∈ inventory roots rules bound state ↔ Reaches roots rules bound state target :=
  ⟨inventory_reaches roots rules bound state target, Reaches.member⟩

/-- The pending potential counts the remaining occurrences of the finite branch trees. -/
def potential [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol)) (bound : Int)
    (pending : List (Goal Ty Symbol)) : Nat :=
  (pending.map fun state => (inventory roots rules bound state).length).sum

/-- Expanding one state removes exactly its root occurrence from the pending potential. -/
theorem inventory_length [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol))
    (bound : Int) (state : Goal Ty Symbol) :
    (inventory roots rules bound state).length = potential roots rules bound (children roots rules bound state) + 1 := by
  rw [inventory, List.length_cons, List.length_flatMap]
  exact congrArg (fun lengths : List Nat => lengths.sum + 1)
    (List.attach_map_val (l := children roots rules bound state)
      (f := fun child => (inventory roots rules bound child).length))

/-- Each pending state has positive potential. -/
theorem inventory_length_pos [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol))
    (bound : Int) (state : Goal Ty Symbol) : 0 < (inventory roots rules bound state).length := by
  rw [inventory_length]
  omega

/-- Concatenated pending states retain the exact source order and additive potential. -/
theorem potential_append [DecidableEq Ty] (roots : List Ty) (rules : List (Rule Ty Symbol))
    (bound : Int) (first second : List (Goal Ty Symbol)) :
    potential roots rules bound (first ++ second) = potential roots rules bound first + potential roots rules bound second := by
  simp only [potential, List.map_append, List.sum_append]

/-- Stored rows retain complete candidate transitions under their original goal keys. -/
abbrev Table (Ty Symbol : Type) := List (Goal Ty Symbol × List (Language.Edge (Goal Ty Symbol) Symbol))

/-- Logical map lookup observes the first stored matching goal. -/
def lookup [DecidableEq (Goal Ty Symbol)] (state : Goal Ty Symbol) : Table Ty Symbol →
    Option (List (Language.Edge (Goal Ty Symbol) Symbol))
  | [] => none
  | (key, edges) :: rest => if state = key then some edges else lookup state rest

/-- An absent map key has no stored key occurrence. -/
theorem lookup_none_iff [DecidableEq (Goal Ty Symbol)] (state : Goal Ty Symbol) (table : Table Ty Symbol) :
    lookup state table = none ↔ state ∉ table.map Prod.fst := by
  induction table with
  | nil => simp [lookup]
  | cons entry table ih =>
      rcases entry with ⟨key, edges⟩
      by_cases same : state = key
      · simp [lookup, same]
      · simp [lookup, same, ih]

/-- Source close skips visited keys; a fresh key is inserted before its ordered children. -/
def close [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)] (roots : List Ty) (rules : List (Rule Ty Symbol))
    (bound : Int) (table : Table Ty Symbol) (pending : List (Goal Ty Symbol)) : Table Ty Symbol :=
  match pending with
  | [] => table
  | state :: rest => match lookup state table with
      | some _ => close roots rules bound table rest
      | none => close roots rules bound ((state, row roots rules bound state) :: table)
          (children roots rules bound state ++ rest)
termination_by potential roots rules bound pending
decreasing_by
  · simp only [potential, List.map_cons, List.sum_cons]
    have positive := inventory_length_pos roots rules bound state
    omega
  · rw [potential_append]
    simp only [potential, List.map_cons, List.sum_cons]
    have exactLength := inventory_length roots rules bound state
    unfold potential at exactLength
    omega

/-- A completed visited-map traversal retains its exact branch choices. -/
inductive Close [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)]
    (roots : List Ty) (rules : List (Rule Ty Symbol)) (bound : Int) :
    Table Ty Symbol → List (Goal Ty Symbol) → Table Ty Symbol → Prop where
  | done : Close roots rules bound table [] table
  | seen (present : lookup state table = some edges) (rest : Close roots rules bound table pending after) :
      Close roots rules bound table (state :: pending) after
  | fresh (absent : lookup state table = none)
      (rest : Close roots rules bound ((state, row roots rules bound state) :: table)
        (children roots rules bound state ++ pending) after) :
      Close roots rules bound table (state :: pending) after

/-- The decreasing pending potential derives a finite actual traversal for every initial table. -/
theorem close_graph [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)] (roots : List Ty) (rules : List (Rule Ty Symbol))
    (bound : Int) (table : Table Ty Symbol) (pending : List (Goal Ty Symbol)) :
    Close roots rules bound table pending (close roots rules bound table pending) := by
  cases pending with
  | nil => simpa only [close] using (Close.done (roots := roots) (rules := rules) (bound := bound) (table := table))
  | cons state pending =>
      cases present : lookup state table with
      | some edges =>
          rw [close, present]
          exact .seen present (close_graph roots rules bound table pending)
      | none =>
          rw [close, present]
          exact .fresh present (close_graph roots rules bound ((state, row roots rules bound state) :: table)
            (children roots rules bound state ++ pending))
termination_by potential roots rules bound pending
decreasing_by
  all_goals
    simp only [potential, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    have positive := inventory_length_pos roots rules bound state
    have exactLength := inventory_length roots rules bound state
    unfold potential at exactLength
    omega

/-- Every earlier map entry keeps its exact transition list. -/
theorem Close.retains [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)]
    {roots : List Ty} {rules : List (Rule Ty Symbol)} {bound : Int}
    {before after : Table Ty Symbol} {pending : List (Goal Ty Symbol)} (actual : Close roots rules bound before pending after) :
    ∀ state edges, lookup state before = some edges → lookup state after = some edges := by
  induction actual with
  | done => exact fun _ _ found => found
  | seen _ _ ih => exact ih
  | @fresh state table pending after absent rest ih =>
      intro query edges found
      apply ih query edges
      by_cases same : query = state
      · subst query
        rw [absent] at found
        cases found
      · simpa only [lookup, same, ite_false] using found

/-- Every initial pending key has a row when the actual traversal returns. -/
theorem Close.pending [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)]
    {roots : List Ty} {rules : List (Rule Ty Symbol)} {bound : Int}
    {before after : Table Ty Symbol} {pending : List (Goal Ty Symbol)}
    (actual : Close roots rules bound before pending after) :
    ∀ state ∈ pending, ∃ edges, lookup state after = some edges := by
  induction actual with
  | done => simp
  | @seen state table edges pending after present rest ih =>
      intro query member
      rcases List.mem_cons.mp member with same | later
      · subst query
        exact ⟨edges, rest.retains state edges present⟩
      · exact ih query later
  | @fresh state table pending after absent rest ih =>
      intro query member
      rcases List.mem_cons.mp member with same | later
      · subst query
        exact ⟨row roots rules bound state, rest.retains state _ (by simp [lookup])⟩
      · exact ih query (List.mem_append_right _ later)

/-- Fresh insertion cannot duplicate any admitted or original map key. -/
theorem Close.nodup [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)]
    {roots : List Ty} {rules : List (Rule Ty Symbol)} {bound : Int}
    {before after : Table Ty Symbol} {pending : List (Goal Ty Symbol)}
    (actual : Close roots rules bound before pending after) (unique : (before.map Prod.fst).Nodup) :
    (after.map Prod.fst).Nodup := by
  induction actual with
  | done => exact unique
  | seen _ _ ih => exact ih unique
  | fresh absent _ ih =>
      apply ih
      exact List.nodup_cons.mpr ⟨(lookup_none_iff _ _).mp absent, unique⟩

/-- Each new final row is literal, and every child of that row has been visited. -/
theorem Close.entry_origin [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)]
    {roots : List Ty} {rules : List (Rule Ty Symbol)} {bound : Int}
    {before after : Table Ty Symbol} {pending : List (Goal Ty Symbol)}
    (actual : Close roots rules bound before pending after) :
    ∀ state edges, lookup state after = some edges →
      lookup state before = some edges ∨
        (edges = row roots rules bound state ∧
          ∀ child ∈ edges.flatMap Language.Edge.children, ∃ childEdges, lookup child after = some childEdges) := by
  induction actual with
  | done => exact fun _ _ found => .inl found
  | seen _ _ ih => exact ih
  | @fresh state table pending after absent rest ih =>
      intro query edges found
      rcases ih query edges found with old | fresh
      · by_cases same : query = state
        · subst query
          have equal : row roots rules bound state = edges := by
            simpa only [lookup, ite_true, Option.some.injEq] using old
          subst edges
          right
          refine ⟨rfl, ?_⟩
          intro child member
          exact rest.pending child (List.mem_append_left _ member)
        · left
          simpa only [lookup, same, ite_false] using old
      · exact .inr fresh

/-- Cold traversal computes a complete finite graph with the exact source rows. -/
theorem close_complete [DecidableEq Ty] [DecidableEq (Goal Ty Symbol)]
    (roots : List Ty) (rules : List (Rule Ty Symbol)) (bound : Int) (start : Goal Ty Symbol) :
    let final := close roots rules bound [] [start]
    Close roots rules bound [] [start] final ∧
      lookup start final = some (row roots rules bound start) ∧
      ∀ state edges, lookup state final = some edges →
        edges = row roots rules bound state ∧
          ∀ child ∈ edges.flatMap Language.Edge.children, ∃ childEdges, lookup child final = some childEdges := by
  dsimp only
  have actual := close_graph roots rules bound [] [start]
  have literal : ∀ state edges, lookup state (close roots rules bound [] [start]) = some edges →
      edges = row roots rules bound state ∧
        ∀ child ∈ edges.flatMap Language.Edge.children,
          ∃ childEdges, lookup child (close roots rules bound [] [start]) = some childEdges := by
    intro state edges found
    rcases actual.entry_origin state edges found with old | new
    · cases old
    · exact new
  obtain ⟨edges, found⟩ := actual.pending start (by simp)
  obtain ⟨same, _⟩ := literal start edges found
  subst edges
  exact ⟨actual, found, literal⟩

end MicroCFTA.SourceTypingFinite
