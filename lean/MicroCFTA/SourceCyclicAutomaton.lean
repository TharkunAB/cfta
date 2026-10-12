import MicroCFTA.RecursiveUnambiguous
import MicroCFTA.SourceFiniteAutomaton

/-!
# Source cyclic automaton prechecks and distinct size indexes

The source rejects open roots, constrained reachable edges, and ambiguous
rows, in that order. A successful row table keeps its source edge order after
canonical sorting. These checks derive distinct size-class ranks.
-/
namespace MicroCFTA.SourceCyclicAutomaton
open Language SourceGuards SourceObservations SourceSymbolicIndex
open RecursiveSize SizedRank RecursiveUnambiguous SymbolicGraphView

/-- One source constructor row before its equality constraints are erased. -/
structure Row (State Formula : Type) where
  symbol : Label Formula
  children : List State
  constraint : Constraint Formula

/-- Retain the complete source guard in the independent accepted language. -/
noncomputable def guarded [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (edge : Row State Formula) : Language.Edge State (Label Formula) :=
  ⟨edge.symbol, edge.children, acceptsConstraint formulas solver edge.constraint⟩

/-- The source unconstrainedEdge test reads normalized equalities and residual syntax. -/
noncomputable def unconstrained (edge : Row State Formula) : Bool :=
  decide (SourceCompactGuards.sourceEqualities edge.constraint = some []) &&
    (SourceCompactGuards.positiveNormalized edge.constraint.guard).isSome

/-- Passing the actual source edge precheck derives a guard that always accepts. -/
theorem unconstrained_plain [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (edge : Row State Formula) (active : SourceCompactGuards.ActiveOption edge.constraint.equalities)
    (checked : unconstrained edge = true) (term : Term (Label Formula)) :
    (guarded formulas solver edge).guard term = true := by
  have parts : SourceCompactGuards.sourceEqualities edge.constraint = some [] ∧
      (SourceCompactGuards.positive edge.constraint.guard).isSome = true := by
    simpa only [unconstrained, Bool.and_eq_true, decide_eq_true_eq,
      SourceCompactGuards.positiveNormalized_support] using checked
  change acceptsConstraint formulas solver edge.constraint term = true
  rw [SourceCompactGuards.sourceEqualities_exact formulas solver edge.constraint active parts.2 term, parts.1]
  rfl

/-- The finite source row snapshot and its actual canonical sorting result. -/
structure Input (State Formula : Type) where
  root : State
  emptyRoot : Bool
  freeVariables : List Nat
  nodes : List State
  rows : State → List (Row State Formula)
  ordered : State → List (Row State Formula)
  permutation : ∀ state, (ordered state).Perm (rows state)
  complete : ∀ state edge, edge ∈ rows state → state ∈ nodes
  emptyRows : emptyRoot = true → rows root = []
  active : ∀ state edge, edge ∈ rows state → SourceCompactGuards.ActiveOption edge.constraint.equalities

/-- The original graph keeps every source guard until its precheck is proved. -/
noncomputable def original [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (input : Input State Formula) : Automaton State (Label Formula) :=
  fun state => (input.rows state).map (guarded formulas solver)

/-- The compiled ordinary table retains the complete sorted row view. -/
noncomputable def ordered [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (input : Input State Formula) : Automaton State (Label Formula) :=
  fun state => (input.ordered state).map (guarded formulas solver)

/-- The source constrained-row scan follows reachable snapshot order. -/
noncomputable def hasConstraints (input : Input State Formula) : Bool :=
  input.nodes.any fun state => (input.rows state).any fun edge => !unconstrained edge

/-- The source overlap scan uses its computed minimum-size intersection test. -/
noncomputable def hasAmbiguity [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs) : Bool :=
  input.nodes.any fun state => AutomatonAmbiguity.ambiguous (fun left right =>
    AutomatonAmbiguity.productiveRows (Language.intersect (original formulas solver input) (original formulas solver input))
      pairs complete (left, right)) (original formulas solver input state)

/-- The public cyclic import reports the first failed source precheck. -/
inductive Error where
  | openAutomaton
  | constrainedEdges
  | ambiguousAutomaton
  deriving DecidableEq, Repr

/-- The automatonRows precheck order, including the EmptyNode shortcut. -/
noncomputable def compile [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs) : Except Error (Automaton State (Label Formula)) :=
  if input.emptyRoot then .ok (fun _ => [])
  else if !input.freeVariables.isEmpty then .error .openAutomaton
  else if hasConstraints input then .error .constrainedEdges
  else if hasAmbiguity formulas solver input pairs complete then .error .ambiguousAutomaton
  else .ok (ordered formulas solver input)

/-- Source empty roots bypass every later validation check. -/
theorem compile_empty [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs) (empty : input.emptyRoot = true) :
    compile formulas solver input pairs complete = .ok (fun _ => []) := by simp [compile, empty]

/-- A nonempty open root reports OpenAutomaton before any row check. -/
theorem compile_open [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (nonempty : input.emptyRoot = false) (openRoot : input.freeVariables.isEmpty = false) :
    compile formulas solver input pairs complete = .error .openAutomaton := by simp [compile, nonempty, openRoot]

/-- Constraint rejection precedes ambiguity rejection. -/
theorem compile_constrained [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (nonempty : input.emptyRoot = false) (closed : input.freeVariables.isEmpty = true)
    (constrained : hasConstraints input = true) :
    compile formulas solver input pairs complete = .error .constrainedEdges := by simp [compile, nonempty, closed, constrained]

/-- Ambiguity rejection occurs only after the root and constraint checks pass. -/
theorem compile_ambiguous [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (nonempty : input.emptyRoot = false) (closed : input.freeVariables.isEmpty = true)
    (plain : hasConstraints input = false) (ambiguous : hasAmbiguity formulas solver input pairs complete = true) :
    compile formulas solver input pairs complete = .error .ambiguousAutomaton := by simp [compile, nonempty, closed, plain, ambiguous]

/-- A successful constraint precheck derives plainness for every represented row. -/
theorem checked_plain [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (input : Input State Formula) (checked : hasConstraints input = false) :
    Decoder.Plain (original formulas solver input) := by
  intro state edge member term
  obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
  have nodeChecked := List.any_eq_false.mp checked state (input.complete state record present)
  have edgeChecked := List.any_eq_false.mp (show ((input.rows state).any fun edge => !unconstrained edge) = false by simpa using nodeChecked)
    record present
  exact unconstrained_plain formulas solver record (input.active state record present) (by simpa using edgeChecked) term

/-- Every represented row passes when the finite ambiguity scan passes. -/
theorem checked_gate [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (checked : hasAmbiguity formulas solver input pairs complete = false) (state : State) :
    AutomatonAmbiguity.ambiguous (fun left right =>
      AutomatonAmbiguity.productiveRows (Language.intersect (original formulas solver input) (original formulas solver input))
        pairs complete (left, right)) (original formulas solver input state) = false := by
  by_cases present : state ∈ input.nodes
  · simpa [hasAmbiguity] using List.any_eq_false.mp checked state present
  · have empty : input.rows state = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro edge member
      exact present (input.complete state edge member)
    simp [original, empty, AutomatonAmbiguity.ambiguous]

/-- Row permutations preserve the independent accepted language without a rank-order claim. -/
theorem permutation_language (first second : Automaton State Symbol)
    (permutation : ∀ state, (second state).Perm (first state)) (state : State) (term : Term Symbol) :
    Accepts second state term ↔ Accepts first state term := by
  apply rowsCorrespond_exact first second id ?_ state term
  intro node edge
  constructor
  · intro member
    exact ⟨edge, (permutation node).mem_iff.mp member, by simp [renameEdge]⟩
  · rintro ⟨edge, member, rfl⟩
    simpa [renameEdge] using (permutation node).mem_iff.mpr member

/-- Edge languages transfer along the already-proved permutation of constructor rows. -/
theorem permutation_edge (first second : Automaton State Symbol)
    (permutation : ∀ state, (second state).Perm (first state)) (edge : Language.Edge State Symbol) (term : Term Symbol) :
    AutomatonAmbiguity.EdgeLanguage (Accepts second) edge term ↔
      AutomatonAmbiguity.EdgeLanguage (Accepts first) edge term := by
  constructor
  · rintro ⟨terms, shape, runs, checked⟩
    exact ⟨terms, shape, runs.imp (fun state term => (permutation_language first second permutation state term).mp), checked⟩
  · rintro ⟨terms, shape, runs, checked⟩
    exact ⟨terms, shape, runs.imp (fun state term => (permutation_language first second permutation state term).mpr), checked⟩

/-- Sorting keeps plain guards and the gate-derived disjoint languages. -/
theorem ordered_facts [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (plainCheck : hasConstraints input = false)
    (ambiguityCheck : hasAmbiguity formulas solver input pairs complete = false) :
    Decoder.Plain (ordered formulas solver input) ∧
      (∀ state, DisjointRows (ordered formulas solver input) state) ∧
      (∀ state term, Accepts (ordered formulas solver input) state term ↔ Accepts (original formulas solver input) state term) := by
  let first := original formulas solver input
  let second := ordered formulas solver input
  have permutation : ∀ state, (second state).Perm (first state) := fun state => (input.permutation state).map _
  refine ⟨?_, ?_, permutation_language first second permutation⟩
  · intro state edge member term
    exact checked_plain formulas solver input plainCheck state edge ((permutation state).mem_iff.mp member) term
  · intro state
    have disjoint := AutomatonAmbiguity.table_gate_disjoint first pairs complete (first state)
      (checked_gate formulas solver input pairs complete ambiguityCheck state)
    have reordered := (permutation state).symm.pairwise disjoint (fun separate term a b => separate term b a)
    apply reordered.imp
    intro left right separate term a b
    exact separate term ((permutation_edge first second permutation left term).mp a)
      ((permutation_edge first second permutation right term).mp b)

/-- Successful source compilation derives global class uniqueness and exact root language. -/
theorem compile_exact [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (output : Automaton State (Label Formula)) (success : compile formulas solver input pairs complete = .ok output) :
    Decoder.Plain output ∧ SizedRank.Unambiguous output ∧
      ∀ term, Accepts output input.root term ↔ Accepts (original formulas solver input) input.root term := by
  unfold compile at success
  split at success
  · rename_i empty
    have same := Except.ok.inj success
    subst output
    refine ⟨?_, ?_, ?_⟩
    · intro state edge member
      cases member
    · intro state size
      cases size <;> simp [RecursiveSize.enumerate]
    · intro term
      have noOriginal : original formulas solver input input.root = [] := by simp [original, input.emptyRows empty]
      constructor
      · intro accepted
        cases accepted with
        | node edge terms member => cases member
      · intro accepted
        cases accepted with
        | node edge terms member => rw [noOriginal] at member; cases member
  · split at success
    · cases success
    · split at success
      · cases success
      · rename_i plainCheck
        split at success
        · cases success
        · rename_i ambiguityCheck
          have same := Except.ok.inj success
          subst output
          have facts := ordered_facts formulas solver input pairs complete (by simpa using plainCheck) (by simpa using ambiguityCheck)
          refine ⟨facts.1, ?_, facts.2.2 input.root⟩
          intro state size
          exact enumerate_nodup _ facts.1 (fun _ => True) (by simp) (fun state _ => facts.2.1 state) size state trivial

/-- The source cyclic API has exact class inverses and contiguous distinct bounded ranks. -/
theorem exact_index_api [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (output : Automaton State (Label Formula)) (success : compile formulas solver input pairs complete = .ok output) :
    (∀ position term, TablePosition.positionsOf output term input.root = some position ↔ replayPosition output input.root position = some term) ∧
    (∀ bound rank, (∃ term, selectAtMost output input.root bound rank = some term) ↔ rank < countAtMost output bound input.root) ∧
    (∀ bound rank term, rankAtMost output input.root bound term = some rank ↔ selectAtMost output input.root bound rank = some term) ∧
    (∀ bound term, rankAtMost output input.root bound term = none ↔
      ¬(Accepts (original formulas solver input) input.root term ∧ nodeSize term ≤ bound)) := by
  obtain ⟨plain, unique, language⟩ := compile_exact formulas solver input pairs complete output success
  refine ⟨positionsOf_inverse output plain input.root (unique input.root), selectAtMost_total output input.root,
    fun bound => rankAtMost_inverse output plain input.root bound (fun size _ => unique input.root size), ?_⟩
  intro bound term
  rw [rankAtMost_reject output plain input.root bound (fun size _ => unique input.root size), language term]

/-- Successful cyclic imports reject exactly terms outside the original unbounded finite-term language. -/
theorem inverse_reject [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (output : Automaton State (Label Formula)) (success : compile formulas solver input pairs complete = .ok output)
    (term : Term (Label Formula)) :
    TablePosition.positionsOf output term input.root = none ↔ ¬Accepts (original formulas solver input) input.root term := by
  obtain ⟨plain, _, language⟩ := compile_exact formulas solver input pairs complete output success
  rw [positionsOf_reject output plain input.root term, language term]

/-- Successful cyclic imports have one distinct bounded rank for each accepted bounded term. -/
theorem distinct_ranks [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (output : Automaton State (Label Formula)) (success : compile formulas solver input pairs complete = .ok output)
    (bound first second : Nat) (term : Term (Label Formula))
    (a : selectAtMost output input.root bound first = some term)
    (b : selectAtMost output input.root bound second = some term) : first = second := by
  obtain ⟨plain, unique, _⟩ := compile_exact formulas solver input pairs complete output success
  exact selectAtMost_injective output plain input.root bound (fun size _ => unique input.root size) first second term a b

/-- Successful source output counts enumerate every exact-size member exactly once. -/
theorem class_count [DecidableEq State] [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula) (input : Input State Formula)
    (pairs : List (State × State)) (complete : ∀ pair, pair ∈ pairs)
    (output : Automaton State (Label Formula)) (success : compile formulas solver input pairs complete = .ok output)
    (size : Nat) :
    ∃ index : DistinctRank.Index (fun term => Accepts (original formulas solver input) input.root term ∧ nodeSize term = size),
      index.count = countAt output size input.root := by
  obtain ⟨plain, unique, language⟩ := compile_exact formulas solver input pairs complete output success
  refine ⟨⟨RecursiveSize.enumerate output size input.root, unique input.root size, ?_⟩,
    (countAt_correct output size input.root).symm⟩
  intro term
  rw [mem_enumerate_iff output plain size input.root term, language term]

end MicroCFTA.SourceCyclicAutomaton
