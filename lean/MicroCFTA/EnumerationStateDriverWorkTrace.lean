import MicroCFTA.EnumerationStateWorkTrace

/-!
# Retained states and total branch work in the enumeration driver

The driver executes the current state algorithm with traced primitives.
Erasure retains the exact ordered result list, including errors and rejection.
The trace retains intermediate states which the result list discards.
Work counts traced transitions and sums alternative work. It does not yet
bound native primitive costs or derive sufficient driver fuel from input.
-/
namespace MicroCFTA.EnumerationStateDriverWorkTrace

open EnumerationStateWorkTrace
variable {Symbol Guard OracleState α β : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem list_lawful : LawfulMonad List := by
  exact LawfulMonad.mk' (m := List)
    (id_map := by intros; simp [Functor.map])
    (bind_pure_comp := by
      intro α β f values
      induction values with
      | nil => rfl
      | cons first rest ih => simp_all [Bind.bind, Functor.map, Pure.pure, List.flatMap])
    (pure_bind := by intros; simp [Bind.bind, Pure.pure])
    (bind_assoc := by intros; simp [Bind.bind, List.flatMap_assoc])

attribute [local instance] list_lawful



/-- Fold the actual ordered scheduler inputs in the traced state computation. -/
def fold (action : α → β → M Symbol Guard α) : List β → α → M Symbol Guard α
  | [], initial => EnumerationStateWorkTrace.pure initial
  | value :: rest, initial => do
      let next ← action initial value
      fold action rest next

/-- Erasure commutes with every ordered state fold, including failed prefixes. -/
theorem erase_fold (action : α → β → M Symbol Guard α) (values : List β) (initial : α) :
    erase (fold action values initial) =
      values.foldlM (fun current value => erase (action current value)) initial := by
  induction values generalizing initial with
  | nil => simpa only [fold, List.foldlM] using erase_pure initial
  | cons value rest ih =>
      simp only [fold, erase_bind, ih, List.foldlM]

/-- Resolve the suspended variables of one slot before recording its readiness. -/
def scan (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (current : List Nat × List Nat) (entry : EnumerationState.UVarValue Symbol × Nat) :
    M Symbol Guard (List Nat × List Nat) := do
  match entry.1 with
  | .unenumerated _ constraints =>
      let blocked ← fold (fun (blocked : List Nat) (constraint : EnumerationState.Suspended) => do
        let root ← representative fuel constraint.var
        EnumerationStateWorkTrace.pure (root :: blocked)) constraints current.2
      EnumerationStateWorkTrace.pure (if EnumerationState.candidate graph entry.1 then current.1 ++ [entry.2] else current.1,
        blocked)
  | _ => EnumerationStateWorkTrace.pure current

/-- The slot scan erases to the current scheduler action at that same slot. -/
theorem erase_scan (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (current : List Nat × List Nat) (entry : EnumerationState.UVarValue Symbol × Nat) :
    erase (scan graph fuel current entry) =
      (do match entry.1 with
          | .unenumerated _ constraints =>
              let blocked ← constraints.foldlM (fun (blocked : List Nat) (constraint : EnumerationState.Suspended) => do
                Pure.pure ((← EnumerationState.representative fuel constraint.var) :: blocked)) current.2
              Pure.pure (if EnumerationState.candidate graph entry.1 then current.1 ++ [entry.2] else current.1,
                blocked)
          | _ => Pure.pure current) := by
  rcases entry with ⟨value, index⟩
  cases value <;>
    simp only [scan, erase_fold, erase_bind, erase_representative, erase_pure]

private theorem erase_if (condition : Prop) [Decidable condition]
    (first second : M Symbol Guard α) :
    erase (if condition then first else second) =
      if condition then erase first else erase second := by
  split <;> rfl

/-- Execute every representative lookup in the source scheduler scan. -/
def findExpandable (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat) :
    M Symbol Guard (Option (List Nat)) := do
  let values := (← get).values
  let current ← fold (scan graph fuel) values.zipIdx ([], [])
  if current.1.isEmpty then EnumerationStateWorkTrace.pure none
  else EnumerationStateWorkTrace.pure (some (current.1.filter fun uv => !(uv ∈ current.2)))

/-- Scheduler erasure holds without a successful lookup or validity premise. -/
theorem erase_findExpandable (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat) :
    erase (findExpandable graph fuel) = EnumerationState.findExpandable graph fuel := by
  simp only [findExpandable, EnumerationState.findExpandable, erase_bind, erase_get,
    erase_fold, erase_scan, erase_if, erase_pure]
  rfl

/-- A callback returns its exact execution tree at the current branch state. -/
abbrev Oracle (Symbol Guard OracleState : Type) := OracleState → Nat →
  Sum (Fragments.Fragment Symbol) Nat → M Symbol Guard (Bool × OracleState)

/-- Follow the complete source loop and retain every discarded branch state. -/
def enumerateFully (graph : EnumerationState.Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState) :
    Nat → OracleState → M Symbol Guard Unit
  | 0, _ => failure .fuelExhausted
  | fuel + 1, oracleState => do
      let next := EnumerationState.pickNext (order oracleState) (← findExpandable graph (fuel + 1))
      match next with
      | .done => EnumerationStateWorkTrace.pure ()
      | .stuck => reject
      | .expand uv =>
          match ← getValue (fuel + 1) uv with
          | .unenumerated (some node) constraints =>
              let repeated ← match graph.node node with
                | .recursive _ => do
                    let root ← representative (fuel + 1) uv
                    let current ← get
                    if EnumerationState.recursionKey node constraints ∈ current.recursionAncestry root then
                      setValue root (.unenumerated (some node) [])
                      EnumerationStateWorkTrace.pure true
                    else EnumerationStateWorkTrace.pure false
                | _ => EnumerationStateWorkTrace.pure false
              if repeated then enumerateFully graph order oracle fuel oracleState
              else
                let before ← oracle oracleState uv (.inr node)
                require (!before.1)
                let fragment ← EnumerationStateWorkTrace.enumerateOut graph (fuel + 1) uv
                let after ← oracle before.2 uv (.inl fragment)
                require (!after.1)
                enumerateFully graph order oracle fuel after.2
          | _ => reject

/-- The full traced driver erases to the same source callback and ordered outcomes. -/
theorem erase_enumerateFully (graph : EnumerationState.Graph Symbol Guard)
    (order : OracleState → List Nat → Option Nat) (oracle : Oracle Symbol Guard OracleState)
    (fuel : Nat) (oracleState : OracleState) :
    erase (enumerateFully graph order oracle fuel oracleState) =
      EnumerationState.enumerateFully graph order
        (fun current uv observed => erase (oracle current uv observed)) fuel oracleState := by
  induction fuel generalizing oracleState with
  | zero => exact erase_failure .fuelExhausted
  | succ fuel ih =>
      unfold enumerateFully EnumerationState.enumerateFully
      rw [erase_bind, erase_findExpandable]
      congr 1
      funext offered
      cases chosen : EnumerationState.pickNext (order oracleState) offered with
      | done => exact erase_pure ()
      | stuck => exact erase_reject
      | expand uv =>
          dsimp only
          rw [erase_bind, erase_getValue]
          congr 1
          funext slot
          cases slot with
          | enumerated _ | eliminated => exact erase_reject
          | unenumerated node constraints =>
              cases node with
              | none => exact erase_reject
              | some node =>
                  cases view : graph.node node <;>
                    simp [view, erase_bind, erase_representative, erase_get, erase_if,
                      erase_setValue, erase_pure, erase_require, erase_enumerateOut, ih]

/-- The actual default callback performs no pruning and no state change. -/
def noPruning : Oracle Symbol Guard Unit := fun current _ _ => EnumerationStateWorkTrace.pure (false, current)

/-- The traced default callback erases to the actual default callback. -/
theorem erase_noPruning (current : Unit) (uv : Nat)
    (observed : Sum (Fragments.Fragment Symbol) Nat) :
    erase (noPruning current uv observed : M Symbol Guard (Bool × Unit)) =
      EnumerationState.noPruning current uv observed := erase_pure _

/-- The complete driver retains the source behavior with the actual default callback. -/
theorem noPruning_driver (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat) :
    erase (enumerateFully graph (fun _ _ => none) noPruning fuel ()) =
      EnumerationState.enumerateFully graph (fun _ _ => none) EnumerationState.noPruning fuel () := by
  rw [erase_enumerateFully]
  simp only [erase_noPruning]

/-- Every actual default-driver error retains the state reached before that error. -/
theorem noPruning_error_state (graph : EnumerationState.Graph Symbol Guard) (fuel : Nat)
    (before : EnumerationState.State Symbol Guard) (error : EnumerationState.Error)
    (observed : .error error ∈ ExceptT.run
      (EnumerationState.enumerateFully graph (fun _ _ => none) EnumerationState.noPruning fuel () before)) :
    ∃ reached, (error, reached) ∈
        (enumerateFully graph (fun _ _ => none) noPruning fuel () before).failures ∧
      reached ∈ (enumerateFully graph (fun _ _ => none) noPruning fuel () before).states := by
  have erased : .error error ∈
      (enumerateFully graph (fun _ _ => none) noPruning fuel () before).erase := by
    simpa only [← noPruning_driver, erase, ExceptT.run] using observed
  obtain ⟨reached, retained⟩ := (Tree.error_iff _ error).mp erased
  exact ⟨reached, retained, Tree.failure_state_mem _ error reached retained⟩

end MicroCFTA.EnumerationStateDriverWorkTrace
