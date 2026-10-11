import MicroCFTA.SymbolicNormalization

/-!
# The symbolic counter's memo tables and signed folds

The monadic proofs use the executable source driver. Each recursive call has
an explicit induction contract. The signed union theorem counts membership
in a finite candidate language. It does not count accepting runs.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- Every graph memo entry records the semantic count of its identity. -/
def GraphCacheCorrect (count : Nat → Int) (counts : Counts Symbol) : Prop :=
  ∀ entry ∈ counts.graphs, entry.2 = count entry.1

/-- Every normalized context memo entry records the semantic count of its full key. -/
def ContextCacheCorrect (count : Key Symbol → Int) (counts : Counts Symbol) : Prop :=
  ∀ entry ∈ counts.contexts, entry.2 = count entry.1

/-- Inserting a graph count preserves all other entries and replaces only that identity. -/
theorem insert_member (entries : List (Nat × Value)) (key : Nat) (value : Value)
    (entry : Nat × Value) :
    entry ∈ insert entries key value ↔ entry = (key, value) ∨ entry ∈ entries ∧ entry.1 ≠ key := by
  simp [insert, delete, List.mem_mergeSort, List.mem_filter]

/-- The graph cache preserves semantic correctness when a proved count is stored. -/
theorem graph_cache_store (meaning : Nat → Int) (counts : Counts Symbol)
    (correct : GraphCacheCorrect meaning counts) (node : Nat) (count : Int)
    (proved : count = meaning node) :
    GraphCacheCorrect meaning {counts with graphs := insert counts.graphs node count} := by
  intro entry member
  rcases (insert_member counts.graphs node count entry).mp member with rfl | old
  · exact proved
  · exact correct entry old.1

/-- A graph cache hit returns the count of the queried graph identity. -/
theorem graph_cache_hit (meaning : Nat → Int) (counts : Counts Symbol)
    (correct : GraphCacheCorrect meaning counts) (node : Nat) (count : Int)
    (found : lookup counts.graphs node = some count) : count = meaning node :=
  correct (node, count) (lookup_member counts.graphs node count found)

/-- The source context-cache lookup cannot reuse a count for a different normalized key. -/
theorem context_cache_hit [DecidableEq Symbol] (meaning : Key Symbol → Int) (counts : Counts Symbol)
    (correct : ContextCacheCorrect meaning counts) (key stored : Key Symbol) (count : Int)
    (found : counts.contexts.find? (fun entry => keyEq entry.1 key) = some (stored, count)) :
    count = meaning key := by
  have member := List.mem_of_find?_eq_some found
  have checked := List.find?_some found
  have same := (keyEq_correct stored key).mp checked
  subst stored
  exact correct (key, count) member

/-- Storing a context result preserves correctness of every older cache entry. -/
theorem context_cache_store (meaning : Key Symbol → Int) (counts : Counts Symbol)
    (correct : ContextCacheCorrect meaning counts) (key : Key Symbol) (count : Int)
    (proved : count = meaning key) :
    ContextCacheCorrect meaning {counts with contexts := (key, count) :: counts.contexts} := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | old
  · exact proved
  · exact correct entry old

/-- A state traversal composes the result and cache invariant of each successful action. -/
theorem state_mapM_correct (action : Input → StateT State (Except Failure) Output)
    (value : Input → Output) (invariant : State → Prop)
    (correct : ∀ input before result after, invariant before →
      action input before = .ok (result, after) → result = value input ∧ invariant after)
    (inputs : List Input) (before after : State) (outputs : List Output)
    (starts : invariant before)
    (success : (inputs.mapM action : StateT State (Except Failure) (List Output)) before = .ok (outputs, after)) :
    outputs = inputs.map value ∧ invariant after := by
  induction inputs generalizing before after outputs with
  | nil => cases success; exact ⟨rfl, starts⟩
  | cons input inputs ih =>
      simp only [List.mapM_cons] at success
      change Except.bind (action input before) (fun (head, middle) =>
        Except.bind ((inputs.mapM action : StateT State (Except Failure) (List Output)) middle)
          (fun (tail, finalState) => .ok (head :: tail, finalState))) = .ok (outputs, after) at success
      cases first : action input before with
      | error error => simp only [first] at success; cases success
      | ok pair =>
          rcases pair with ⟨head, middle⟩
          have headCorrect := correct input before head middle starts first
          cases rest : (inputs.mapM action : StateT State (Except Failure) (List Output)) middle with
          | error error => simp only [first, Except.bind, rest] at success; cases success
          | ok pair =>
              rcases pair with ⟨tail, finalState⟩
              have tailCorrect := ih middle finalState tail headCorrect.2 rest
              simp only [first, Except.bind, rest, Except.ok.injEq, Prod.mk.injEq] at success
              rcases success with ⟨rfl, rfl⟩
              exact ⟨by simp only [List.map_cons, headCorrect.1, tailCorrect.1], tailCorrect.2⟩

/-- Multiplying a recursively counted contribution preserves the cache induction invariant. -/
theorem coefficient_action_correct (action : Edge Symbol → CountM Symbol Int)
    (meaning : Edge Symbol → Int) (invariant : Counts Symbol → Prop)
    (correct : ∀ edge before count after, invariant before →
      action edge before = .ok (count, after) → count = meaning edge ∧ invariant after)
    (piece : Edge Symbol × Int) (before after : Counts Symbol) (result : Int)
    (starts : invariant before)
    (success : ((do pure (piece.2 * (← action piece.1))) : CountM Symbol Int) before = .ok (result, after)) :
    result = piece.2 * meaning piece.1 ∧ invariant after := by
  change Except.bind (action piece.1 before) (fun (count, state) => .ok (piece.2 * count, state)) =
    .ok (result, after) at success
  cases counted : action piece.1 before with
  | error error => simp only [counted] at success; cases success
  | ok pair =>
      rcases pair with ⟨count, state⟩
      have recursive := correct piece.1 before count state starts counted
      simp only [counted, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨by rw [recursive.1], recursive.2⟩

/-- The source's successful monadic union count equals its signed coefficient interpretation. -/
theorem countUnion_correct [DecidableEq Symbol] (graph : Graph Symbol)
    (action : Edge Symbol → CountM Symbol Int) (meaning : Edge Symbol → Int)
    (invariant : Counts Symbol → Prop)
    (correct : ∀ edge before count after, invariant before →
      action edge before = .ok (count, after) → count = meaning edge ∧ invariant after)
    (edges : List (Edge Symbol)) (before after : Counts Symbol) (count : Int)
    (starts : invariant before) (success : countUnion graph action edges before = .ok (count, after)) :
    count = Symbolic.weighted meaning (Symbolic.unionCoefficients (intersectEdge graph) edges) ∧ invariant after := by
  let pieces := Symbolic.unionCoefficients (intersectEdge graph) edges
  let contribution := fun piece : Edge Symbol × Int => (do pure (piece.2 * (← action piece.1)) : CountM Symbol Int)
  change Except.bind ((pieces.mapM contribution : CountM Symbol (List Int)) before)
    (fun (values, state) => .ok (values.sum, state)) = .ok (count, after) at success
  cases counted : (pieces.mapM contribution : CountM Symbol (List Int)) before with
  | error error => simp only [counted] at success; cases success
  | ok pair =>
      rcases pair with ⟨values, state⟩
      have contributions := state_mapM_correct contribution (fun piece => piece.2 * meaning piece.1) invariant
        (fun piece initial result finalState start done =>
          coefficient_action_correct action meaning invariant correct piece initial finalState result start done)
        pieces before state values starts counted
      simp only [counted, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      refine ⟨?_, contributions.2⟩
      rw [contributions.1]
      change (pieces.map (fun piece => piece.2 * meaning piece.1)).sum = Symbolic.weighted meaning pieces
      induction pieces with
      | nil => rfl
      | cons piece rest ih => simp [Symbolic.weighted, ih]

/-- Overlapping alternatives contribute each accepted candidate once to the actual source fold. -/
theorem countUnion_distinct [DecidableEq Symbol] (graph : Graph Symbol)
    (member : Edge Symbol → Value → Bool) (exactMeet : Symbolic.ExactMeet member (intersectEdge graph))
    (candidates : List Value) (action : Edge Symbol → CountM Symbol Int)
    (invariant : Counts Symbol → Prop)
    (correct : ∀ edge before count after, invariant before → action edge before = .ok (count, after) →
      count = Symbolic.totalOver candidates (fun value => Lattice.indicator (member edge value)) ∧ invariant after)
    (edges : List (Edge Symbol)) (before after : Counts Symbol) (count : Int)
    (starts : invariant before) (success : countUnion graph action edges before = .ok (count, after)) :
    count = Symbolic.totalOver candidates (fun value => Lattice.indicator (edges.any fun edge => member edge value)) ∧
      invariant after := by
  have result := countUnion_correct graph action
    (fun edge => Symbolic.totalOver candidates (fun value => Lattice.indicator (member edge value)))
    invariant correct edges before after count starts success
  rw [Symbolic.union_count member (intersectEdge graph) exactMeet edges candidates] at result
  exact result

/-- Summing Boolean indicators counts exactly the selected candidate entries. -/
theorem totalOver_indicator (candidates : List Value) (member : Value → Bool) :
    Symbolic.totalOver candidates (fun value => Lattice.indicator (member value)) =
      ((candidates.filter member).length : Int) := by
  induction candidates with
  | nil => rfl
  | cons first rest ih =>
      cases selected : member first <;> simp [Symbolic.totalOver, Lattice.indicator, selected] at ih ⊢ <;> omega

/-- A duplicate-free candidate language yields a distinct-term count through the actual monadic fold. -/
theorem countUnion_distinct_terms [DecidableEq Symbol] (graph : Graph Symbol)
    (member : Edge Symbol → Value → Bool) (exactMeet : Symbolic.ExactMeet member (intersectEdge graph))
    (candidates : List Value) (distinct : candidates.Nodup) (action : Edge Symbol → CountM Symbol Int)
    (invariant : Counts Symbol → Prop)
    (correct : ∀ edge before count after, invariant before → action edge before = .ok (count, after) →
      count = Symbolic.totalOver candidates (fun value => Lattice.indicator (member edge value)) ∧ invariant after)
    (edges : List (Edge Symbol)) (before after : Counts Symbol) (count : Int)
    (starts : invariant before) (success : countUnion graph action edges before = .ok (count, after)) :
    count = ((candidates.filter fun value => edges.any fun edge => member edge value).length : Int) ∧
      (candidates.filter fun value => edges.any fun edge => member edge value).Nodup ∧ invariant after := by
  have result := countUnion_distinct graph member exactMeet candidates action invariant correct edges before after count starts success
  rw [totalOver_indicator] at result
  exact ⟨result.1, distinct.filter _, result.2⟩

/-- The actual node-count cache-hit branch returns its stored value and leaves both caches unchanged. -/
theorem countNode_cached [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (fuel node : Nat) (counts : Counts Symbol) (count : Int)
    (nonempty : (graph.edges node).isEmpty = false) (found : lookup counts.graphs node = some count) :
    countNode graph (fuel + 1) node counts = .ok (count, counts) := by
  simp only [countNode, nonempty, Bool.false_eq_true, ↓reduceIte]
  simp [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, Except.bind,
    Pure.pure, StateT.pure, Except.pure, found]

/-- A source node-cache hit is semantically safe under the stored graph-count invariant. -/
theorem countNode_cached_correct [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (meaning : Nat → Int) (counts : Counts Symbol) (correct : GraphCacheCorrect meaning counts)
    (fuel node : Nat) (count : Int) (nonempty : (graph.edges node).isEmpty = false)
    (found : lookup counts.graphs node = some count) :
    countNode graph (fuel + 1) node counts = .ok (meaning node, counts) := by
  rw [countNode_cached graph fuel node counts count nonempty found]
  rw [graph_cache_hit meaning counts correct node count found]

/-- The independent-domain branch multiplies semantic node counts and preserves its cache invariant. -/
theorem solveStep_independent [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol)
    (meaning : Nat → Int) (invariant : Counts Symbol → Prop) (fuel : Nat)
    (correct : ∀ node before count after, invariant before →
      countNode graph fuel node before = .ok (count, after) → count = meaning node ∧ invariant after)
    (problem : Problem Symbol) (independent : problem.obligations = [])
    (before after : Counts Symbol) (count : Int) (starts : invariant before)
    (success : solveStep graph (fuel + 1) problem before = .ok (count, after)) :
    count = (problem.domains.map fun entry => meaning entry.2).prod ∧ invariant after := by
  simp only [solveStep, independent] at success
  change Except.bind ((problem.domains.mapM (fun entry => countNode graph fuel entry.2) : CountM Symbol (List Int)) before)
    (fun (values, finalState) => .ok (values.prod, finalState)) = .ok (count, after) at success
  cases counted : (problem.domains.mapM (fun entry => countNode graph fuel entry.2) : CountM Symbol (List Int)) before with
  | error error => simp only [counted] at success; cases success
  | ok pair =>
      rcases pair with ⟨values, state⟩
      have valuesCorrect := state_mapM_correct (fun entry => countNode graph fuel entry.2)
        (fun entry => meaning entry.2) invariant (fun entry => correct entry.2)
        problem.domains before state values starts counted
      simp only [counted, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨by rw [valuesCorrect.1], valuesCorrect.2⟩

end MicroCFTA.SymbolicDriver
