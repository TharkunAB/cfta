import MicroCFTA.BinderSchedule

/-!
# Sufficient bounds for optional graph binders

Marked states reduce the active context. Unmarked active states follow a
strict structural rank. These two facts give one finite execution bound for
the entire constructor. Every greater bound returns the same finite syntax.
-/

namespace MicroCFTA.BinderSchedule
open Language Binding BinderLanguage BinderGraph BinderCompile

/-- One stable successful result exists at every sufficiently large bound. -/
def Eventually (action : Nat → Option α) : Prop :=
  ∃ bound value, ∀ fuel, bound ≤ fuel → action fuel = some value

/-- A finite ordered traversal combines every child's sufficient bound. -/
theorem walk_eventual (action : Nat → α → Option β) (input : List α)
    (total : ∀ item ∈ input, Eventually (fun fuel => action fuel item)) :
    Eventually (fun fuel => walk (action fuel) input) := by
  induction input with
  | nil => exact ⟨0, [], fun _ _ => rfl⟩
  | cons head tail ih =>
    obtain ⟨headBound, first, firstResult⟩ := total head (by simp)
    obtain ⟨tailBound, rest, restResult⟩ := ih (fun item member => total item (by simp [member]))
    refine ⟨max headBound tailBound, first :: rest, ?_⟩
    intro fuel enough
    simp [walk, firstResult fuel (by omega), restResult fuel (by omega)]

/-- Mapping a completed finite construction preserves its stable bound. -/
theorem map_eventual (action : Nat → Option α) (f : α → β) (total : Eventually action) :
    Eventually (fun fuel => (action fuel).map f) := by
  obtain ⟨bound, value, result⟩ := total
  exact ⟨bound, f value, fun fuel enough => by simp [result fuel enough]⟩

/-- Every constructor and child in the graph body is included in one common bound. -/
theorem buildRows_eventual (graph : Automaton Nat Symbol) (state : Nat)
    (children : Nat → Nat → Option (Shape (Payload Symbol)))
    (total : ∀ edge ∈ graph state, ∀ child ∈ edge.children, Eventually (fun fuel => children fuel child)) :
    Eventually (fun fuel => buildRows graph state (children fuel)) := by
  apply map_eventual
  apply walk_eventual
  intro edge member
  exact map_eventual _ _ (walk_eventual children edge.children (total edge member))

/-- One outer source call frame adds one to the sufficient bound. -/
theorem successor_eventual (action body : Nat → Option α)
    (equation : ∀ fuel, action (fuel + 1) = body fuel) (total : Eventually body) : Eventually action := by
  obtain ⟨bound, value, result⟩ := total
  refine ⟨bound + 1, value, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => rw [equation fuel]; exact result fuel (by omega)

/-- An already bound state returns its reference without traversing graph rows. -/
theorem external_eventual (graph : Automaton Nat Symbol) (cyclic : List Nat → Nat → Bool)
    (active : List Nat) (state : Nat) (outside : state ∉ active) :
    Eventually (fun fuel => build graph cyclic fuel active state) := by
  refine ⟨1, .ref state, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => simp [build, outside]

/-- A rank decreases along active edges from every state for which the cycle test omits a binder. -/
def Ranked (graph : Automaton Nat Symbol) (cyclic : List Nat → Nat → Bool)
    (rank : List Nat → Nat → Nat) : Prop :=
  ∀ active state, state ∈ active → cyclic active state = false →
    ∀ edge ∈ graph state, ∀ child ∈ edge.children, child ∈ active → rank active child < rank active state

/-- The complete optional-binder constructor terminates from its two structural decreases. -/
theorem build_eventual (graph : Automaton Nat Symbol) (cyclic : List Nat → Nat → Bool)
    (rank : List Nat → Nat → Nat) (ranked : Ranked graph cyclic rank)
    (active : List Nat) (state : Nat) : Eventually (fun fuel => build graph cyclic fuel active state) := by
  by_cases present : state ∈ active
  · cases chosen : cyclic active state with
    | false =>
      apply successor_eventual _ (fun fuel => buildRows graph state (build graph cyclic fuel active))
      · intro fuel; simp [build, present, chosen]
      · apply buildRows_eventual
        intro edge member child belongs
        by_cases inside : child ∈ active
        · exact build_eventual graph cyclic rank ranked active child
        · exact external_eventual graph cyclic active child inside
    | true =>
      apply successor_eventual _ (fun fuel =>
        (buildRows graph state (build graph cyclic fuel (active.erase state))).map
          (fun body => cleanup (.binder state body)))
      · intro fuel; simp [build, present, chosen]
      · apply map_eventual
        apply buildRows_eventual
        intro edge member child belongs
        exact build_eventual graph cyclic rank ranked (active.erase state) child
  · exact external_eventual graph cyclic active state present
termination_by (active.length, rank active state)
decreasing_by
  · apply Prod.Lex.right
    exact ranked active state present chosen edge member child belongs inside
  · apply Prod.Lex.left
    rw [List.length_erase_of_mem present]
    have positive := List.length_pos_of_mem present
    omega

/-- A closed finite graph has one stable, exact imported syntax at every sufficient bound. -/
theorem closed_build_total (graph : Automaton Nat Symbol) (cyclic : List Nat → Nat → Bool)
    (rank : List Nat → Nat → Nat) (ranked : Ranked graph cyclic rank)
    (states : List Nat) (unique : states.Nodup) (closed : Closed graph states)
    (root : Nat) (present : root ∈ states) :
    ∃ bound shape, (∀ fuel, bound ≤ fuel → build graph cyclic fuel states root = some shape) ∧
      ∀ term, meaning (fun _ _ => False) shape term ↔ Accepts graph root term := by
  obtain ⟨bound, shape, result⟩ := build_eventual graph cyclic rank ranked states root
  refine ⟨bound, shape, result, ?_⟩
  intro term
  rw [build_exact graph cyclic bound states unique root shape (result bound (by omega))]
  exact ⟨run_sound graph states, fun accepted => run_complete graph states closed _ accepted present⟩

end MicroCFTA.BinderSchedule
