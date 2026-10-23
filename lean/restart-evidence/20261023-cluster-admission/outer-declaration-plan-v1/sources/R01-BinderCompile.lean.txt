import MicroCFTA.BinderGraph

/-!
# Exact conversion from finite graphs to recursive syntax

The compiler assigns one reference name to each state. It removes the selected
state from the active component before it builds the binder body. Repeated
states then refer to the enclosing binder. The active set decreases, so the
construction terminates even when the input graph has cycles.
-/

namespace MicroCFTA.BinderCompile
open Language Binding BinderLanguage BinderGraph

/-- Copy each original transition with its symbol, guard, and ordered children. -/
def rows (graph : Automaton Nat Symbol) (state : Nat)
    (children : Nat → Shape (Payload Symbol)) : Shape (Payload Symbol) :=
  .alternatives ((graph state).map fun edge =>
    .branch ⟨edge.label, fun term => edge.guard term = true⟩ (edge.children.map children))

/-- A copied child list has exactly the corresponding ordered child languages. -/
theorem forest_map_exact (environment : Env Symbol) (shapes : Nat → Shape (Payload Symbol))
    (languages : Env Symbol) (exact : ∀ state, meaning environment (shapes state) = languages state)
    (states : List Nat) (terms : List (Term Symbol)) :
    forest environment (states.map shapes) terms ↔ All₂ languages states terms := by
  induction states generalizing terms with
  | nil => cases terms <;> simp only [List.map, forest] <;> constructor <;> intro h <;> first | exact .nil | trivial | cases h
  | cons state rest ih =>
    cases terms with
    | nil => simp only [List.map, forest]; constructor <;> intro h <;> cases h
    | cons term terms =>
      simp only [List.map, forest, exact, ih]
      constructor
      · rintro ⟨head, tail⟩; exact .cons head tail
      · intro accepted; cases accepted with | cons head tail => exact ⟨head, tail⟩

/-- Copied syntax rows denote the original graph body exactly. -/
theorem rows_exact (graph : Automaton Nat Symbol) (state : Nat) (environment : Env Symbol)
    (shapes : Nat → Shape (Payload Symbol)) (languages : Env Symbol)
    (exact : ∀ child, meaning environment (shapes child) = languages child) :
    meaning environment (rows graph state shapes) = body graph state languages := by
  funext term
  apply propext
  simp only [rows, meaning, body]
  constructor
  · rintro ⟨⟨shape, present⟩, accepted⟩
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    simp only [meaning] at accepted
    obtain ⟨terms, same, children, guard⟩ := accepted
    exact ⟨edge, member, terms, same, (forest_map_exact environment shapes languages exact _ _).mp children, guard⟩
  · rintro ⟨edge, member, terms, same, children, guard⟩
    refine ⟨⟨_, List.mem_map.mpr ⟨edge, member, rfl⟩⟩, ?_⟩
    simp only [meaning]
    exact ⟨terms, same, (forest_map_exact environment shapes languages exact _ _).mpr children, guard⟩

/-- Construct finite nested binder syntax from an active state set. -/
def compile (graph : Automaton Nat Symbol) (active : List Nat) (state : Nat) : Shape (Payload Symbol) :=
  if _present : state ∈ active then
    .binder state (rows graph state (compile graph (active.erase state)))
  else .ref state
termination_by active.length
decreasing_by
  rw [List.length_erase_of_mem _present]
  have positive := List.length_pos_of_mem _present
  omega

/-- The complete nested binder construction has exactly the open graph language. -/
theorem compile_exact (graph : Automaton Nat Symbol) (active : List Nat) (unique : active.Nodup)
    (environment : Env Symbol) (state : Nat) :
    meaning environment (compile graph active state) = Run graph active environment state := by
  induction count : active.length using Nat.strongRecOn generalizing active environment state with
  | ind size ih =>
    by_cases present : state ∈ active
    · rw [compile, dite_eq_left present]
      simp only [meaning]
      have smaller : (active.erase state).length < size := by
        rw [List.length_erase_of_mem present]
        have positive := List.length_pos_of_mem present
        omega
      have bodyExact : ∀ value,
          meaning (BinderLanguage.bind environment state value)
              (rows graph state (compile graph (active.erase state))) =
            step graph active environment state value := by
        intro value
        apply rows_exact
        intro child
        exact ih _ smaller _ (unique.erase state) _ child rfl
      rw [least_congr _ _ (fun value term => by rw [bodyExact value])]
      funext term
      exact propext (least_exact graph active environment state unique present term)
    · rw [compile, dite_eq_right present]
      simp only [meaning]
      funext term
      exact propext (external_exact graph active environment state present term).symm

/-- No external language can create a term in a closed graph conversion. -/
theorem run_sound (graph : Automaton Nat Symbol) (active : List Nat) {state term}
    (accepted : Run graph active (fun _ _ => False) state term) : Accepts graph state term := by
  induction accepted using Run.rec
    (motive_2 := fun states terms _ => All₂ (Accepts graph) states terms) with
  | external _ impossible => exact False.elim impossible
  | node edge children _ member runs guard ih => exact .node edge children member ih guard
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

/-- A finite state set is closed under every declared transition child. -/
def Closed (graph : Automaton Nat Symbol) (states : List Nat) : Prop :=
  ∀ state ∈ states, ∀ edge ∈ graph state, ∀ child ∈ edge.children, child ∈ states

/-- A complete original run stays inside any closed active state set. -/
theorem run_complete (graph : Automaton Nat Symbol) (active : List Nat) (closed : Closed graph active)
    (environment : Env Symbol) {state term} (accepted : Accepts graph state term) :
    state ∈ active → Run graph active environment state term := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => (∀ state ∈ states, state ∈ active) →
      All₂ (Run graph active environment) states terms) with
  | @node state edge children member runs guard ih =>
    intro present
    exact .node edge children present member (ih (closed state present edge member)) guard
  | nil => exact .nil
  | @cons state term states terms _ _ head tail =>
    rename_i present
    exact .cons (head (present state (by simp))) (tail (fun child member => present child (by simp [member])))

/-- Finite cyclic graph conversion neither drops nor introduces an accepted term. -/
theorem closed_compile_exact (graph : Automaton Nat Symbol) (states : List Nat)
    (unique : states.Nodup) (closed : Closed graph states) (root : Nat) (present : root ∈ states)
    (term : Term Symbol) :
    meaning (fun _ _ => False) (compile graph states root) term ↔ Accepts graph root term := by
  rw [compile_exact graph states unique]
  exact ⟨run_sound graph states, fun accepted => run_complete graph states closed _ accepted present⟩

/-- Use the source binder smart constructor at every recursive construction step. -/
def compileClean (graph : Automaton Nat Symbol) (active : List Nat) (state : Nat) : Shape (Payload Symbol) :=
  if _present : state ∈ active then
    cleanup (.binder state (rows graph state (compileClean graph (active.erase state))))
  else .ref state
termination_by active.length
decreasing_by
  rw [List.length_erase_of_mem _present]
  have positive := List.length_pos_of_mem _present
  omega

/-- Applying binder cleanup during construction preserves every open graph language. -/
theorem compileClean_exact (graph : Automaton Nat Symbol) (active : List Nat) (unique : active.Nodup)
    (environment : Env Symbol) (state : Nat) :
    meaning environment (compileClean graph active state) = Run graph active environment state := by
  induction count : active.length using Nat.strongRecOn generalizing active environment state with
  | ind size ih =>
    by_cases present : state ∈ active
    · rw [compileClean, dite_eq_left present, cleanup_exact]
      simp only [meaning]
      have smaller : (active.erase state).length < size := by
        rw [List.length_erase_of_mem present]
        have positive := List.length_pos_of_mem present
        omega
      have bodyExact : ∀ value,
          meaning (BinderLanguage.bind environment state value)
              (rows graph state (compileClean graph (active.erase state))) =
            step graph active environment state value := by
        intro value
        apply rows_exact
        intro child
        exact ih _ smaller _ (unique.erase state) _ child rfl
      rw [least_congr _ _ (fun value term => by rw [bodyExact value])]
      funext term
      exact propext (least_exact graph active environment state unique present term)
    · rw [compileClean, dite_eq_right present]
      simp only [meaning]
      funext term
      exact propext (external_exact graph active environment state present term).symm

/-- Cleaned cyclic import accepts every original root term exactly. -/
theorem closed_clean_exact (graph : Automaton Nat Symbol) (states : List Nat)
    (unique : states.Nodup) (closed : Closed graph states) (root : Nat) (present : root ∈ states)
    (term : Term Symbol) :
    meaning (fun _ _ => False) (compileClean graph states root) term ↔ Accepts graph root term := by
  rw [compileClean_exact graph states unique]
  exact ⟨run_sound graph states, fun accepted => run_complete graph states closed _ accepted present⟩

end MicroCFTA.BinderCompile
