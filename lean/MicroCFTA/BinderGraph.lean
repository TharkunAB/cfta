import MicroCFTA.BinderLanguage

/-!
# Finite graph equations with bound states

An active state expands its original constructor rows. Every other state is
an external language parameter. Removing one active state and binding it by
its least language preserves every finite run. This is the semantic step
used when a cyclic graph becomes nested recursive binders.
-/

namespace MicroCFTA.BinderGraph
open Language BinderLanguage

/-- Finite runs stop at states already represented by enclosing binders. -/
inductive Run (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol) :
    Nat → Term Symbol → Prop where
  | external {state term} : state ∉ active → environment state term → Run graph active environment state term
  | node {state} (edge : Edge Nat Symbol) (children : List (Term Symbol)) :
      state ∈ active → edge ∈ graph state → All₂ (Run graph active environment) edge.children children →
      edge.guard (.node edge.label children) = true → Run graph active environment state (.node edge.label children)

/-- Increasing external languages preserves every finite run. -/
theorem run_mono (graph : Automaton Nat Symbol) (active : List Nat) (left right : Env Symbol)
    (included : ∀ state, Included (left state) (right state)) {state term}
    (accepted : Run graph active left state term) : Run graph active right state term := by
  induction accepted using Run.rec
    (motive_2 := fun states terms _ => All₂ (Run graph active right) states terms) with
  | external outside accepted => exact .external outside (included _ _ accepted)
  | node edge children present member runs guard ih => exact .node edge children present member ih guard
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

/-- A state outside the active graph has exactly its supplied language. -/
theorem external_exact (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (state : Nat) (outside : state ∉ active) (term : Term Symbol) :
    Run graph active environment state term ↔ environment state term := by
  constructor
  · intro accepted
    cases accepted with
    | external _ value => exact value
    | node edge children present => exact False.elim (outside present)
  · exact .external outside

/-- One state body keeps the original symbol, child order, and complete guard. -/
def body (graph : Automaton Nat Symbol) (state : Nat) (languages : Env Symbol) : Lang Symbol :=
  fun term => ∃ edge ∈ graph state, ∃ children,
    term = .node edge.label children ∧ All₂ languages edge.children children ∧ edge.guard term = true

/-- Constructor bodies are monotone in every child language. -/
theorem body_mono (graph : Automaton Nat Symbol) (state : Nat) (left right : Env Symbol)
    (included : ∀ child, Included (left child) (right child)) :
    Included (body graph state left) (body graph state right) := by
  rintro term ⟨edge, member, children, same, runs, guard⟩
  exact ⟨edge, member, children, same, runs.imp included, guard⟩

/-- Expand the rest of a component while the selected state is a language parameter. -/
def cut (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (selected : Nat) (value : Lang Symbol) : Env Symbol :=
  Run graph (active.erase selected) (BinderLanguage.bind environment selected value)

/-- The selected state has this positive recursive body after the graph cut. -/
def step (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (selected : Nat) (value : Lang Symbol) : Lang Symbol := body graph selected (cut graph active environment selected value)

/-- Binding one external language makes the remaining graph monotone in it. -/
theorem cut_mono (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (selected : Nat) (left right : Lang Symbol) (included : Included left right) :
    ∀ state, Included (cut graph active environment selected left state)
      (cut graph active environment selected right state) := by
  intro state term accepted
  apply run_mono graph _ _ _ _ accepted
  intro name value before
  by_cases same : name = selected
  · simpa [BinderLanguage.bind, same] using included value (by simpa [BinderLanguage.bind, same] using before)
  · simpa [BinderLanguage.bind, same] using before

/-- The recursive state body has a least fixed point. -/
theorem step_mono (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (selected : Nat) : Monotone (step graph active environment selected) := by
  intro left right included
  exact body_mono graph selected _ _ (cut_mono graph active environment selected left right included)

/-- Replacing a cut reference by its original graph language expands to an original run. -/
theorem cut_lift (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (selected : Nat) {state term}
    (accepted : cut graph active environment selected (Run graph active environment selected) state term) :
    Run graph active environment state term := by
  induction accepted using Run.rec
    (motive_2 := fun states terms _ => All₂ (Run graph active environment) states terms) with
  | @external state term outside value =>
    by_cases same : state = selected
    · simpa [BinderLanguage.bind, same] using value
    · have absent : state ∉ active := fun present => outside ((List.mem_erase_of_ne same).mpr present)
      exact .external absent (by simpa [BinderLanguage.bind, same] using value)
  | node edge children present member runs guard ih =>
    exact .node edge children (List.mem_of_mem_erase present) member ih guard
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

/-- The least cut solution cannot introduce a term absent from the original state. -/
theorem least_sound (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (selected : Nat) (present : selected ∈ active) :
    Included (least (step graph active environment selected)) (Run graph active environment selected) := by
  apply least_le
  rintro term ⟨edge, member, children, rfl, runs, guard⟩
  exact .node edge children present member
    (runs.imp (fun _ _ accepted => cut_lift graph active environment selected accepted)) guard

/-- Every original run survives a cut whose reference uses the least cut solution. -/
theorem cut_complete (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (selected : Nat) (unique : active.Nodup) (present : selected ∈ active) {state term}
    (accepted : Run graph active environment state term) :
    cut graph active environment selected (least (step graph active environment selected)) state term := by
  induction accepted using Run.rec
    (motive_2 := fun states terms _ =>
      All₂ (cut graph active environment selected (least (step graph active environment selected))) states terms) with
  | @external state term outside value =>
    have different : state ≠ selected := fun same => outside (same ▸ present)
    exact .external (fun member => outside (List.mem_of_mem_erase member)) (by simpa [BinderLanguage.bind, different] using value)
  | @node state edge children atState member runs guard ih =>
    by_cases same : state = selected
    · subst state
      apply Run.external (unique.not_mem_erase)
      simp only [BinderLanguage.bind]
      exact least_closed _ (step_mono graph active environment selected) _ ⟨edge, member, children, rfl, ih, guard⟩
    · exact .node edge children ((unique.mem_erase_iff).mpr ⟨same, atState⟩) member ih guard
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

/-- Removing a graph state and adding its recursive binder preserves its exact language. -/
theorem least_exact (graph : Automaton Nat Symbol) (active : List Nat) (environment : Env Symbol)
    (selected : Nat) (unique : active.Nodup) (present : selected ∈ active) (term : Term Symbol) :
    least (step graph active environment selected) term ↔ Run graph active environment selected term := by
  constructor
  · exact least_sound graph active environment selected present term
  · intro accepted
    have after := cut_complete graph active environment selected unique present accepted
    have value := (external_exact graph (active.erase selected) _ selected unique.not_mem_erase term).mp after
    simpa [BinderLanguage.bind] using value

end MicroCFTA.BinderGraph
