import MicroCFTA.SourceCurrentConjunctionEmptinessTable

/-!
# Tuple-charged conjunction admission after PR 193

Empty, budget, free-reference, and repeated-key tests precede sampling.
The sample includes one extra tuple to detect overflow.
The charge counts tuples before equality rejection.
The old conjunction-charged worklist remains a separate definition.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleBudget
open EqualityNormalize SourceCurrentConjunctionEmptinessRows
open SourceCurrentConjunctionEmptinessTable (Entry skip)
variable {Node Symbol : Type}

/-- The current Haskell tuple budget is separate from the older admission budget. -/
def currentTupleBudget : Nat := 10000

/-- The extra tuple detects a product that does not fit the remaining budget. -/
def sample (budget : Nat) (tuples : List A) : List A := tuples.take (budget + 1)

/-- A fitting sample contains every tuple in the original source order. -/
theorem sample_eq_of_fits (budget : Nat) (tuples : List A)
    (fits : (sample budget tuples).length ≤ budget) : sample budget tuples = tuples := by
  have count : min (budget + 1) tuples.length ≤ budget := by
    simpa only [sample, List.length_take] using fits
  apply List.take_of_length_le
  omega

/-- Overflow is detected exactly when the complete tuple list exceeds the budget. -/
theorem sample_overflow_iff (budget : Nat) (tuples : List A) :
    budget < (sample budget tuples).length ↔ budget < tuples.length := by
  simp only [sample, List.length_take]
  omega

/-- Equality rejection follows sampling and does not reduce its charge. -/
noncomputable def sampledRows [DecidableEq Symbol] [DecidableEq Node]
    (empty : Node) (key : Node → Int) (edges : Node → List (Edge Node Symbol))
    (project : List Node → Path → Node) (budget : Nat) (nodes : List Node) : List (List (List Node)) :=
  (sample budget (edgeTuples edges nodes)).filterMap fun tuple => (combined tuple).map fun classes =>
    requirements empty key project ((tuple.head?).map (fun edge => edge.children.length) |>.getD 0) classes (tuple.map Edge.children)

/-- Every admitted sample has exactly the full source tuple rows. -/
theorem sampledRows_eq [DecidableEq Symbol] [DecidableEq Node]
    (empty : Node) (key : Node → Int) (edges : Node → List (Edge Node Symbol))
    (project : List Node → Path → Node) (budget : Nat) (nodes : List Node)
    (fits : (sample budget (edgeTuples edges nodes)).length ≤ budget) :
    sampledRows empty key edges project budget nodes = tupleRows empty key edges project nodes := by
  unfold sampledRows tupleRows
  rw [sample_eq_of_fits budget (edgeTuples edges nodes) fits]

/-- Contradictory tuples still count toward the sample charge. -/
theorem sampledRows_length_le [DecidableEq Symbol] [DecidableEq Node]
    (empty : Node) (key : Node → Int) (edges : Node → List (Edge Node Symbol))
    (project : List Node → Path → Node) (budget : Nat) (nodes : List Node) :
    (sampledRows empty key edges project budget nodes).length ≤
      (sample budget (edgeTuples edges nodes)).length := List.length_filterMap_le _ _

/-- A zero-tuple product has zero charge and an empty stored row list. -/
theorem no_tuples [DecidableEq Symbol] [DecidableEq Node]
    (empty : Node) (key : Node → Int) (edges : Node → List (Edge Node Symbol))
    (project : List Node → Path → Node) (budget : Nat) (nodes : List Node)
    (none : edgeTuples edges nodes = []) :
    (sample budget (edgeTuples edges nodes)).length = 0 ∧ sampledRows empty key edges project budget nodes = [] := by
  simp only [sample, sampledRows, none, List.take_nil, List.length_nil, List.filterMap_nil, and_self]

/-- The source branch order retains exact sampled rows and remaining tuple budget. -/
inductive Run [DecidableEq Symbol] [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (edges : Node → List (Edge Node Symbol)) (project : List Node → Path → Node) :
    Nat → List (Entry Node) → List (List Node) → List (Entry Node) → Prop where
  /-- An empty pending list returns the current table. -/
  | done {budget table} : Run empty key closed edges project budget table [] table
  /-- An empty operand removes the pending head. -/
  | empty {budget table nodes pending final}
      (impossible : empty ∈ nodes) (rest : Run empty key closed edges project budget table pending final) :
      Run empty key closed edges project budget table (nodes :: pending) final
  /-- An exhausted, open, or repeated conjunction removes the pending head. -/
  | skip {budget table nodes pending final}
      (nonempty : empty ∉ nodes) (skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = true)
      (rest : Run empty key closed edges project budget table pending final) :
      Run empty key closed edges project budget table (nodes :: pending) final
  /-- An overflowing sample adds no entry and sets the remaining budget to zero. -/
  | overflow {budget table nodes pending final}
      (nonempty : empty ∉ nodes) (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
      (tooMany : budget < (sample budget (edgeTuples edges nodes)).length)
      (rest : Run empty key closed edges project 0 table pending final) :
      Run empty key closed edges project budget table (nodes :: pending) final
  /-- A fitting complete sample inserts its rows and subtracts its raw tuple count. -/
  | admit {budget table nodes pending final}
      (nonempty : empty ∉ nodes) (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
      (fits : (sample budget (edgeTuples edges nodes)).length ≤ budget)
      (rest : Run empty key closed edges project (budget - (sample budget (edgeTuples edges nodes)).length)
        (⟨nodes, sampledRows empty key edges project budget nodes⟩ :: table)
        ((sampledRows empty key edges project budget nodes).flatten ++ pending) final) :
      Run empty key closed edges project budget table (nodes :: pending) final

/-- Once the remaining tuple budget is zero, the table cannot change. -/
theorem Run.zero_table [DecidableEq Symbol] [DecidableEq Node]
    {empty : Node} {key : Node → Int} {closed : Node → Bool}
    {edges : Node → List (Edge Node Symbol)} {project : List Node → Path → Node}
    {budget : Nat} {table final : List (Entry Node)} {pending : List (List Node)}
    (actual : Run empty key closed edges project budget table pending final) (zero : budget = 0) : final = table := by
  induction actual with
  | done => rfl
  | empty _ _ ih => exact ih zero
  | skip _ _ _ ih => exact ih zero
  | overflow _ _ _ _ ih => exact ih rfl
  | admit _ fresh _ _ _ =>
      have positive := (SourceCurrentConjunctionEmptinessTable.admitted _ _ _ _ _ fresh).1
      omega

/-- An overflowing fresh conjunction stays absent after the remaining queue is drained. -/
theorem overflow_absent [DecidableEq Symbol] [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (edges : Node → List (Edge Node Symbol)) (project : List Node → Path → Node)
    (budget : Nat) (table final : List (Entry Node)) (nodes : List Node) (pending : List (List Node))
    (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
    (rest : Run empty key closed edges project 0 table pending final) :
    SourceCurrentConjunctionEmptinessTable.lookup key (SourceCurrentConjunctionEmptinessTable.keys key nodes) final = none := by
  rw [rest.zero_table rfl]
  exact (SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes fresh).2.2


/-- An overflowing fresh nonempty conjunction remains conservatively outside the table. -/
theorem overflow_outside [DecidableEq Symbol] [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (edges : Node → List (Edge Node Symbol)) (project : List Node → Path → Node)
    (budget : Nat) (table final : List (Entry Node)) (nodes : List Node) (pending : List (List Node))
    (nonempty : empty ∉ nodes)
    (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
    (rest : Run empty key closed edges project 0 table pending final) :
    SourceCurrentConjunctionEmptinessTable.classify empty key closed final nodes = .outside := by
  have absent := overflow_absent empty key closed edges project budget table final nodes pending fresh rest
  have missing := (SourceCurrentConjunctionEmptinessTable.lookup_none_iff key _ final).mp absent
  cases allClosed : nodes.all closed <;>
    simp only [SourceCurrentConjunctionEmptinessTable.classify, nonempty, ite_false, allClosed,
      Bool.false_eq_true, missing, dite_false, ite_true]

end MicroCFTA.SourceCurrentConjunctionTupleBudget
