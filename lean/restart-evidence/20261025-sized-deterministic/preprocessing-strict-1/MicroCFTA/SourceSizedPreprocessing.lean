import MicroCFTA.SourceSizedDispatcher
import MicroCFTA.SourceSizedRows

/-!
# Original-row scans and canonical worker rows

Canonical sorting changes row order only. Structural productivity,
reachability, and the two source constraint scans retain their results.
The public dispatcher scans the original rows and reads the sorted rows.
-/
namespace MicroCFTA.SourceSizedPreprocessing
open Language Productivity SourceSizedDecided SourceSizedDispatcher Std
open SourceObservations SourceSymbolicIndex
attribute [local instance] lexOrd

/-- Permuting rows preserves every structural productivity round. -/
theorem productive_perm (first second : Automaton State Symbol)
    (permutation : ∀ state, (first state).Perm (second state)) (states : List State) :
    productive states first = productive states second := by
  have step : productiveStep first = productiveStep second := by
    funext known state
    exact (permutation state).any_eq
  simp only [productive, step]

/-- Structural live-row filtering commutes with a permutation of original rows. -/
theorem live_perm (first second : Automaton State Symbol)
    (permutation : ∀ state, (first state).Perm (second state)) (states : List State) (state : State) :
    (GraphTrim.live states first state).Perm (GraphTrim.live states second state) := by
  unfold GraphTrim.live
  rw [productive_perm first second permutation states]
  split
  · exact (permutation state).filter _
  · exact .nil

/-- The live successor lists retain all multiplicities under row permutations. -/
theorem live_successors_perm (first second : Automaton State Symbol)
    (permutation : ∀ state, (first state).Perm (second state)) (states : List State) (state : State) :
    (successors (GraphTrim.live states first) state).Perm
      (successors (GraphTrim.live states second) state) :=
  List.Perm.flatMap_right Edge.children (live_perm first second permutation states state)

/-- Reachability rounds depend on successor membership, not successor order. -/
theorem reachClosure_membership [DecidableEq State]
    (first second : State → List State) (same : ∀ state child, child ∈ first state ↔ child ∈ second state)
    (states seeds : List State) : reachClosure states first seeds = reachClosure states second seeds := by
  have step : reachStep states first = reachStep states second := by
    funext known target
    unfold reachStep
    congr 1
    apply congrArg (fun predicate => states.any predicate)
    funext source
    simp only [same source target]
  simp only [reachClosure, step]

/-- Structural trimming retains the same raw constraints after canonical row sorting. -/
theorem trimmedRows_perm [DecidableEq State]
    (first second : State → List (Row State Symbol Annotation))
    (permutation : ∀ state, (first state).Perm (second state)) (states : List State) (root state : State) :
    (SourceSizedTrimGuards.trimmedRows first states root state).Perm
      (SourceSizedTrimGuards.trimmedRows second states root state) := by
  let firstShape := automaton first (fun _ _ => true)
  let secondShape := automaton second (fun _ _ => true)
  have shape : ∀ state, (firstShape state).Perm (secondShape state) := fun state => (permutation state).map _
  have marked := productive_perm firstShape secondShape shape states
  have reached := reachClosure_membership (successors (GraphTrim.live states firstShape))
    (successors (GraphTrim.live states secondShape))
    (fun state _ => (live_successors_perm firstShape secondShape shape states state).mem_iff) states [root]
  change (if reachClosure states (successors (GraphTrim.live states firstShape)) [root] state &&
      productive states firstShape state then (first state).filter (fun row => row.children.all (productive states firstShape)) else []).Perm
    (if reachClosure states (successors (GraphTrim.live states secondShape)) [root] state &&
      productive states secondShape state then (second state).filter (fun row => row.children.all (productive states secondShape)) else [])
  rw [reached, marked]
  split
  · exact (permutation state).filter _
  · exact .nil

/-- The all-row noConstraint precheck is unchanged by canonical sorting. -/
theorem plainCheck_perm
    (first second : State → List (Row State (Label Formula) (Constraint Formula)))
    (permutation : ∀ state, (first state).Perm (second state)) (states : List State) :
    plainCheck first states = plainCheck second states := by
  classical
  unfold plainCheck
  congr 1
  funext state
  exact (permutation state).all_eq

/-- The trimmed residual precheck is unchanged by canonical sorting. -/
theorem residualCheck_perm [DecidableEq State]
    (first second : State → List (Row State (Label Formula) (Constraint Formula)))
    (permutation : ∀ state, (first state).Perm (second state)) (states : List State) (root : State) :
    residualCheck first states root = residualCheck second states root := by
  unfold residualCheck
  congr 1
  funext state
  exact (trimmedRows_perm first second permutation states root state).all_eq

/-- The source any-residual scan retains its exact failed or successful result. -/
theorem residualScan_perm [DecidableEq State]
    (first second : State → List (Row State Symbol (Constraint Formula)))
    (permutation : ∀ state, (first state).Perm (second state)) (states : List State) (root : State) :
    SourceSizedTrimGuards.residualScan first states root =
      SourceSizedTrimGuards.residualScan second states root := by
  unfold SourceSizedTrimGuards.residualScan
  congr 1
  funext state
  exact (trimmedRows_perm first second permutation states root state).any_eq

/-- A validated original graph has a complete finite state domain and raw constraints. -/
structure Input (State Symbol Annotation : Type) where
  root : State
  states : List State
  complete : ∀ state, state ∈ states
  distinct : states.Nodup
  rows : State → List (Row State Symbol Annotation)

/-- Canonical refinement sees every original row before any trim or guard check. -/
def graph (input : Input State Symbol Annotation) : CanonicalClasses.Graph State (Nat × Symbol) where
  nodes := input.states
  complete := input.complete
  distinct := input.distinct
  rows state := (input.rows state).map fun row => ((row.children.length, row.label), row.children)

/-- Raw row keys keep the arity, symbol, and ordered canonical child classes. -/
def rowKey (classes : State → Nat) (row : Row State Symbol Annotation) : (Nat × Symbol) × List Nat :=
  ((row.children.length, row.label), row.children.map classes)

/-- Stable canonical sorting retains each raw annotation in its row. -/
def sortRows [Ord Symbol] (input : Input State Symbol Annotation) (classes : State → Nat) :
    State → List (Row State Symbol Annotation) :=
  fun state => (input.rows state).mergeSort fun first second =>
    (compare (rowKey classes first) (rowKey classes second)).isLE

/-- Compute the canonical classes and sort the original raw rows. -/
def sortedRows [DecidableEq Symbol] [Ord Symbol] (input : Input State Symbol Annotation) :
    State → List (Row State Symbol Annotation) :=
  sortRows input ((CanonicalClasses.canonical (graph input)).getD (fun _ => 0))

/-- The source canonical loop completes, so sortedRows never uses its default table. -/
theorem sortedRows_completed [DecidableEq Symbol] [Ord Symbol] (input : Input State Symbol Annotation) :
    ∃ classes, CanonicalClasses.canonical (graph input) = some classes ∧
      sortedRows input = sortRows input classes := by
  obtain ⟨classes, completed⟩ := CanonicalClasses.canonical_terminates (graph input)
  exact ⟨classes, completed, by simp [sortedRows, completed]⟩

/-- The actual computed canonical row order is a permutation of the original rows. -/
theorem sortedRows_perm [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Annotation) (state : State) :
    (sortedRows input state).Perm (input.rows state) := List.mergeSort_perm _ _

/-- Interpretation commutes with stable raw canonical sorting. -/
theorem sortRows_interpretation [Ord Symbol]
    (input : Input State Symbol Annotation) (classes : State → Nat)
    (holds : Annotation → Term Symbol → Bool) :
    automaton (sortRows input classes) holds =
      SourceSizedRows.sortedRows
        ⟨input.states, input.complete, input.distinct, automaton input.rows holds⟩ classes := by
  funext state
  apply List.map_mergeSort
  intro first _ second _
  rfl

/-- The source reference scans original rows and reads canonically sorted classes. -/
noncomputable def publicReference [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula)) : Except Unit (Api (Label Formula)) :=
  if residualCheck input.rows input.states input.root then
    .ok (referenceApi (equalityRows (sortedRows input)) input.root)
  else .error ()

/-- The source dispatcher scans original annotations before selecting either sorted worker. -/
noncomputable def publicSized [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula)) : Except Unit (Api (Label Formula)) :=
  if plainCheck input.rows input.states &&
      (SourceSizedDeterministic.bottomUpDeterministic (ordinaryRows (sortedRows input)) input.states ||
        SourceSizedDispatchGraph.unambiguousRows (ordinaryRows (sortedRows input)) input.states input.complete) then
    .ok (optimizedApi (ordinaryRows (sortedRows input)) input.root)
  else publicReference input

/-- The original residual scan and sorted worker compose to the proved reference interface. -/
theorem publicReference_eq_sorted [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula)) :
    publicReference input = SourceSizedDispatcher.reference (sortedRows input) input.states input.root := by
  unfold publicReference SourceSizedDispatcher.reference
  rw [residualCheck_perm input.rows (sortedRows input) (fun state => (sortedRows_perm input state).symm)]

/-- The actual original-row scans compose to the proved sorted-row dispatcher. -/
theorem publicSized_eq_sorted [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula)) :
    publicSized input = SourceSizedDispatcher.sized (sortedRows input) input.states input.complete input.root := by
  unfold publicSized SourceSizedDispatcher.sized
  rw [plainCheck_perm input.rows (sortedRows input) (fun state => (sortedRows_perm input state).symm),
    publicReference_eq_sorted]

/-- Public optimized dispatch and public reference have identical complete query records and errors. -/
theorem publicSized_eq_reference [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula)) :
    publicSized input = publicReference input := by
  rw [publicSized_eq_sorted, SourceSizedDispatcher.sized_eq_reference, publicReference_eq_sorted]

/-- Every successful public result uses the actual canonically sorted first-occurrence sequence. -/
theorem publicSized_success [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula))
    (api : Api (Label Formula)) (success : publicSized input = .ok api) :
    residualCheck input.rows input.states input.root = true ∧
      api = referenceApi (equalityRows (sortedRows input)) input.root := by
  rw [publicSized_eq_reference, publicReference] at success
  split at success
  · rename_i passed
    exact ⟨passed, (Except.ok.inj success).symm⟩
  · cases success

/-- The all-positive reference condition is exactly the complement of the source any-residual scan. -/
theorem residualCheck_eq_not_scan [DecidableEq State]
    (rows : State → List (Row State (Label Formula) (Constraint Formula)))
    (states : List State) (root : State) :
    residualCheck rows states root = !SourceSizedTrimGuards.residualScan rows states root := by
  simp [residualCheck, SourceSizedTrimGuards.residualScan, List.not_any_eq_all_not]

/-- The only failed reference result is exactly a residual guard in the original trimmed rows. -/
theorem publicSized_error [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula)) :
    publicSized input = .error () ↔
      SourceSizedTrimGuards.residualScan input.rows input.states input.root = true := by
  rw [publicSized_eq_reference, publicReference, residualCheck_eq_not_scan]
  cases SourceSizedTrimGuards.residualScan input.rows input.states input.root <;> simp

/-- Successful source queries accept exactly the original guarded terms at each node-count size. -/
theorem publicSized_terms_exact [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (formulas : SourceGuards.Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (input : Input State (Label Formula) (Constraint Formula))
    (active : ∀ state row,
      row ∈ SourceSizedTrimGuards.trimmedRows input.rows input.states input.root state →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (api : Api (Label Formula)) (success : publicSized input = .ok api)
    (size : Nat) (term : Term (Label Formula)) :
    term ∈ api.terms (Int.ofNat size) ↔
      Accepts (automaton input.rows (acceptsConstraint formulas solver)) input.root term ∧
        RecursiveSize.nodeSize term = size := by
  have activeSorted : ∀ state row,
      row ∈ SourceSizedTrimGuards.trimmedRows (sortedRows input) input.states input.root state →
      SourceCompactGuards.ActiveOption row.constraint.equalities := by
    intro state row member
    exact active state row
      ((trimmedRows_perm (sortedRows input) input.rows (sortedRows_perm input) input.states input.root state).mem_iff.mp member)
  have exact := SourceSizedDispatcher.sized_terms_exact formulas solver (sortedRows input)
    input.states input.complete input.root activeSorted api (publicSized_eq_sorted input ▸ success) size term
  rw [SourceCyclicAutomaton.permutation_language
    (automaton input.rows (acceptsConstraint formulas solver))
    (automaton (sortedRows input) (acceptsConstraint formulas solver))
    (fun state => (sortedRows_perm input state).map _) input.root term] at exact
  exact exact

/-- The complete source preprocessing path retains both signed distinct-term rank inverse laws. -/
theorem publicSized_signed_inverses [DecidableEq State] [DecidableEq Formula] [Ord (Label Formula)]
    (input : Input State (Label Formula) (Constraint Formula))
    (api : Api (Label Formula)) (success : publicSized input = .ok api)
    (size rank : Int) (term : Term (Label Formula)) :
    (api.rank term).map (fun position => (Int.ofNat position.size, Int.ofNat position.rank)) = some (size, rank) ↔
      api.unrank size rank = some term :=
  SourceSizedDispatcher.sized_signed_inverses (sortedRows input) input.states input.complete input.root
    api (publicSized_eq_sorted input ▸ success) size rank term

end MicroCFTA.SourceSizedPreprocessing
