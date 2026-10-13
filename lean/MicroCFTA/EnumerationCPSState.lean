import MicroCFTA.EnumerationCPSChecked

/-!
# The CPS interface and the existing finite state machine

The translation commutes with the actual StateT/ExceptT/List operations.
Finite list traversals retain their full ordered state transitions. The
translation laws apply compositionally to the enumeration workers; they do
not replace a failed execution bound by an empty branch list.
-/

namespace MicroCFTA.EnumerationCPSState

open EnumerationCPSChecked

variable {Symbol Guard α β : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, Pure.pure]
  bind_pure_comp := by intros; simp [Bind.bind, Pure.pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [Pure.pure, Bind.bind]
  bind_assoc := by intros; exact List.flatMap_assoc

/-- The checked source interface at the existing enumeration state and error types. -/
abbrev Action (Symbol Guard α : Type) :=
  Computation (EnumerationState.State Symbol Guard) EnumerationState.Error α

/-- Interpret one existing bounded state-machine action in the checked CPS interface. -/
def lift (action : EnumerationState.EnumerateM Symbol Guard α) : Action Symbol Guard α := encode action

/-- Every lifted worker preserves every branch, error, and final state. -/
theorem lift_exact (action : EnumerationState.EnumerateM Symbol Guard α) :
    Represents (lift action) action := rfl

/-- The exact model return operation agrees with CPS pure. -/
theorem pure_exact (value : α) :
    Represents (EnumerationCPSChecked.pure value : Action Symbol Guard α)
      (Pure.pure value : EnumerationState.EnumerateM Symbol Guard α) := rfl

/-- Source failed alternatives agree with rejection in the finite model. -/
theorem reject_exact : Represents (reject : Action Symbol Guard α)
    (EnumerationState.reject : EnumerationState.EnumerateM Symbol Guard α) := rfl

/-- The finite model's explicit errors remain errors in the checked interface. -/
theorem failure_exact (error : EnumerationState.Error) :
    Represents (failure error : Action Symbol Guard α) (EnumerationState.failure error) := rfl

/-- A model state read agrees with the source CPS state primitive. -/
theorem get_exact : Represents (get : Action Symbol Guard (EnumerationState.State Symbol Guard))
    (MonadStateOf.get : EnumerationState.EnumerateM Symbol Guard (EnumerationState.State Symbol Guard)) := rfl

/-- A model state replacement agrees with the source CPS state primitive. -/
theorem put_exact (after : EnumerationState.State Symbol Guard) :
    Represents (put after : Action Symbol Guard Unit)
      (set after : EnumerationState.EnumerateM Symbol Guard Unit) := rfl

/-- A model state update agrees with the source CPS state primitive. -/
theorem modify_exact (change : EnumerationState.State Symbol Guard → EnumerationState.State Symbol Guard) :
    Represents (EnumerationCPSChecked.modify change : Action Symbol Guard Unit)
      (_root_.modify change : EnumerationState.EnumerateM Symbol Guard Unit) := rfl

/-- Source branches replaces the old choose worker without changing its rows. -/
theorem branches_exact (values : List α) :
    Represents (branches values : Action Symbol Guard α) (EnumerationState.choose values) :=
  branches_represents values

/-- Replacing both sides of an actual model bind preserves its full result list. -/
theorem bind_exact (action : Action Symbol Guard α) (next : α → Action Symbol Guard β)
    (first : EnumerationState.EnumerateM Symbol Guard α)
    (second : α → EnumerationState.EnumerateM Symbol Guard β)
    (initial : Represents action first) (following : ∀ value, Represents (next value) (second value)) :
    Represents (bind action next) (Bind.bind (m := EnumerationState.EnumerateM Symbol Guard) first second) := by
  have same : (Bind.bind (m := EnumerationState.EnumerateM Symbol Guard) first second) =
      bindRows first second := by
    funext before
    simp only [Bind.bind, StateT.bind, ExceptT.bind, ExceptT.mk, bindRows]
    congr 1
    funext result
    cases result with
    | error error => rfl
    | ok pair => cases pair; rfl
  rw [same]
  exact bind_represents action next first second initial following

/-- The source traversal visits each action before the remaining inputs. -/
def mapM (action : α → Action Symbol Guard β) : List α → Action Symbol Guard (List β)
  | [] => EnumerationCPSChecked.pure []
  | first :: rest => bind (action first) fun value =>
      bind (mapM action rest) fun values => EnumerationCPSChecked.pure (value :: values)

/-- CPS list traversal agrees with the existing state-monad traversal in order. -/
theorem mapM_exact (action : α → Action Symbol Guard β)
    (model : α → EnumerationState.EnumerateM Symbol Guard β)
    (represented : ∀ value, Represents (action value) (model value)) (values : List α) :
    Represents (mapM action values) (List.mapM (m := EnumerationState.EnumerateM Symbol Guard) model values) := by
  induction values with
  | nil => exact pure_exact []
  | cons first rest ih =>
      simp only [mapM, List.mapM_cons]
      apply bind_exact _ _ _ _ (represented first)
      intro value
      apply bind_exact _ _ _ _ ih
      intro values
      exact pure_exact (value :: values)

/-- Fold a branch-local accumulator through finite inputs in source order. -/
def foldlM (action : α → β → Action Symbol Guard α) : α → List β → Action Symbol Guard α
  | accumulator, [] => EnumerationCPSChecked.pure accumulator
  | accumulator, first :: rest => bind (action accumulator first) fun next => foldlM action next rest

/-- CPS accumulator traversal agrees with the actual state-monad fold. -/
theorem foldlM_exact (action : α → β → Action Symbol Guard α)
    (model : α → β → EnumerationState.EnumerateM Symbol Guard α)
    (represented : ∀ accumulator value, Represents (action accumulator value) (model accumulator value))
    (accumulator : α) (values : List β) :
    Represents (foldlM action accumulator values) (List.foldlM (m := EnumerationState.EnumerateM Symbol Guard) model accumulator values) := by
  induction values generalizing accumulator with
  | nil => exact pure_exact accumulator
  | cons first rest ih =>
      simp only [foldlM, List.foldlM_cons]
      exact bind_exact _ _ _ _ (represented accumulator first) ih

/-- Update one raw UVar slot through the actual source state primitive. -/
def setValue (uv : Nat) (value : EnumerationState.UVarValue Symbol) : Action Symbol Guard Unit :=
  EnumerationCPSChecked.modify fun state => {state with values := state.values.set uv value}

/-- The CPS raw-slot write is exactly the established finite machine operation. -/
theorem setValue_exact (uv : Nat) (value : EnumerationState.UVarValue Symbol) :
    Represents (setValue (Guard := Guard) uv value) (EnumerationState.setValue uv value) := rfl

/-- A Boolean guard either returns unit or rejects only its current branch. -/
def require (condition : Bool) : Action Symbol Guard Unit :=
  if condition then EnumerationCPSChecked.pure () else reject

/-- The CPS require operation matches the current finite branch guard. -/
theorem require_exact (condition : Bool) :
    Represents (require (Symbol := Symbol) (Guard := Guard) condition) (EnumerationState.require condition) := by
  cases condition <;> rfl

end MicroCFTA.EnumerationCPSState
