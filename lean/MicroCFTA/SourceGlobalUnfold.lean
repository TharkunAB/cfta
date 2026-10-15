import MicroCFTA.InternedFreshOrdinaryUnfoldMemo

/-!
# Physical primitives and global unfolding events

The primitive interpreter executes actual constructor operations. Its global
unfolding alternative runs the completed unfolding memo. Every primitive
emits one event. A finite operational trace that has no global unfolding
event retains its original unfolding table. Source compilers must derive
their traces from the actual constructor schedule.
-/
namespace MicroCFTA.SourceGlobalUnfold
open Cache InternedConstructorTemplates InternedBinderProtocol

/-- Events distinguish physical constructor work from a global unfolding call. -/
inductive Event (Symbol Guard : Type) where
  | edgeRequest (key : EdgeKey Symbol Guard)
  | nodeRequest (key : NodeKey)
  | muLookup (key : NodeKey)
  | muReserve (key : NodeKey) (identity : Nat)
  | muPublish (key : NodeKey)
  | globalUnfold (input : NodeRef)

/-- Only the actual global unfolding alternative marks a global call. -/
def Event.isGlobal : Event Symbol Guard → Bool
  | .globalUnfold _ => true
  | _ => false

/-- A finite event list contains no global unfolding call. -/
def NoGlobal (events : List (Event Symbol Guard)) : Prop :=
  ∀ event ∈ events, event.isGlobal = false

/-- An empty trace has no global unfolding call. -/
theorem NoGlobal.nil : NoGlobal ([] : List (Event Symbol Guard)) := by
  intro event impossible
  cases impossible

/-- A silent primitive can precede a silent trace. -/
theorem NoGlobal.cons {event : Event Symbol Guard} {events : List (Event Symbol Guard)}
    (first : event.isGlobal = false) (rest : NoGlobal events) : NoGlobal (event :: events) := by
  intro current member
  rcases List.mem_cons.mp member with rfl | member
  · exact first
  · exact rest current member

/-- Consecutive traces retain the absence of global unfolding calls. -/
theorem NoGlobal.append {first second : List (Event Symbol Guard)}
    (left : NoGlobal first) (right : NoGlobal second) : NoGlobal (first ++ second) := by
  intro event member
  rcases List.mem_append.mp member with member | member
  · exact left event member
  · exact right event member

@[simp] theorem noGlobal_nil : NoGlobal ([] : List (Event Symbol Guard)) := NoGlobal.nil

@[simp] theorem noGlobal_cons {event : Event Symbol Guard} {events : List (Event Symbol Guard)} :
    NoGlobal (event :: events) ↔ event.isGlobal = false ∧ NoGlobal events := by
  constructor
  · intro silent
    exact ⟨silent event List.mem_cons_self, fun current member => silent current (List.mem_cons_of_mem _ member)⟩
  · rintro ⟨first, rest⟩
    exact NoGlobal.cons first rest

@[simp] theorem noGlobal_append {first second : List (Event Symbol Guard)} :
    NoGlobal (first ++ second) ↔ NoGlobal first ∧ NoGlobal second := by
  constructor
  · intro silent
    exact ⟨fun event member => silent event (List.mem_append_left _ member),
      fun event member => silent event (List.mem_append_right _ member)⟩
  · rintro ⟨left, right⟩
    exact left.append right

/-- The operational state retains the actual heap and completed unfolding table. -/
structure State (Symbol Guard : Type) where
  heap : InternedConstructorTemplates.State Symbol Guard
  unfolding : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard

/-- Mu lookup distinguishes an absent key from an unfinished or completed reservation. -/
inductive MuLookup (Symbol Guard : Type) where
  | missing
  | pending
  | ready (value : Value Symbol Guard)

/-- Read the same key and record slots as the actual Mu request. -/
def lookupMu (key : NodeKey) (heap : InternedConstructorTemplates.State Symbol Guard) : MuLookup Symbol Guard :=
  match heap.nodes.table key with
  | none => .missing
  | some _ => match heap.nodeRecords key with
    | none => .pending
    | some value => .ready value

/-- Each primitive names its actual operation instead of accepting an arbitrary outcome. -/
inductive Primitive (Symbol Guard : Type) : Type → Type 1 where
  | edge (key : EdgeKey Symbol Guard) (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard) :
      Primitive Symbol Guard (EdgeValue Symbol Guard)
  | node (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard) : Primitive Symbol Guard (Value Symbol Guard)
  | muLookup (key : NodeKey) : Primitive Symbol Guard (MuLookup Symbol Guard)
  | muReserve (key : NodeKey) : Primitive Symbol Guard (Interned NodeKey)
  | muPublish (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Primitive Symbol Guard (Value Symbol Guard)
  | globalUnfold (input : Value Symbol Guard) : Primitive Symbol Guard (Value Symbol Guard)

/-- Every primitive outcome retains its exact state and emitted event. -/
inductive Outcome (Symbol Guard A : Type) where
  | done (value : A) (state : State Symbol Guard) (event : Event Symbol Guard)
  | pending (key : NodeKey) (state : State Symbol Guard) (event : Event Symbol Guard)

/-- Read the state after a complete or pending primitive. -/
def Outcome.state : Outcome Symbol Guard A → State Symbol Guard
  | .done _ state _ | .pending _ state _ => state

/-- Read the actual primitive event, including global memo hits. -/
def Outcome.event : Outcome Symbol Guard A → Event Symbol Guard
  | .done _ _ event | .pending _ _ event => event

/-- Execute actual interning, Mu reservation/publication, or the real unfolding memo alternative. -/
def perform [DecidableEq (EdgeKey Symbol Guard)] (primitive : Primitive Symbol Guard A) (before : State Symbol Guard) :
    Outcome Symbol Guard A :=
  match primitive with
  | .edge key identify =>
      let actual := edgeStep key identify before.heap
      .done actual.1 ⟨actual.2, before.unfolding⟩ (.edgeRequest key)
  | .node key identify =>
      let actual := nodeStep key identify before.heap
      .done actual.1 ⟨actual.2, before.unfolding⟩ (.nodeRequest key)
  | .muLookup key => .done (lookupMu key before.heap) before (.muLookup key)
  | .muReserve key =>
      let actual := Cache.intern before.heap.nodes key
      .done actual.1 ⟨{before.heap with nodes := actual.2}, before.unfolding⟩ (.muReserve key actual.1.identity)
  | .muPublish entry body depth ordinary =>
      let key := muKey depth ordinary
      let candidate := Value.mu entry body depth ordinary
      let records := keepFirst before.heap.nodeRecords key candidate
      .done ((records key).getD candidate) ⟨{before.heap with nodeRecords := records}, before.unfolding⟩ (.muPublish key)
  | .globalUnfold input =>
      match InternedFreshOrdinaryUnfoldMemo.run input before.unfolding before.heap with
      | .done (output, saved) after => .done output ⟨after, saved⟩ (.globalUnfold input.referenceOf)
      | .pending key after => .pending key ⟨after, before.unfolding⟩ (.globalUnfold input.referenceOf)

/-- One operational observation executes a named primitive and retains its actual event. -/
inductive Step [DecidableEq (EdgeKey Symbol Guard)] : State Symbol Guard → State Symbol Guard → Event Symbol Guard → Prop where
  | actual (primitive : Primitive Symbol Guard A) (before : State Symbol Guard) :
      Step before (perform primitive before).state (perform primitive before).event

/-- An edge primitive performs the actual edge interning operation. -/
theorem Step.edge [DecidableEq (EdgeKey Symbol Guard)] (key : EdgeKey Symbol Guard)
    (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard) (before : State Symbol Guard) :
    Step before ⟨(edgeStep key identify before.heap).2, before.unfolding⟩ (.edgeRequest key) :=
  .actual (.edge key identify) before

/-- A node primitive performs the actual node interning operation. -/
theorem Step.node [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey)
    (identify : Interned NodeKey → Value Symbol Guard) (before : State Symbol Guard) :
    Step before ⟨(nodeStep key identify before.heap).2, before.unfolding⟩ (.nodeRequest key) :=
  .actual (.node key identify) before

/-- Mu lookup observes its actual table slots without changing either operational field. -/
theorem Step.muLookup [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (before : State Symbol Guard) :
    Step before before (.muLookup key) := .actual (.muLookup key) before

/-- Mu reservation uses the actual node-cache interner and its returned identity. -/
theorem Step.muReserve [DecidableEq (EdgeKey Symbol Guard)] (key : NodeKey) (before : State Symbol Guard) :
    Step before ⟨{before.heap with nodes := (Cache.intern before.heap.nodes key).2}, before.unfolding⟩
      (.muReserve key (Cache.intern before.heap.nodes key).1.identity) := .actual (.muReserve key) before

/-- Mu publication preserves the actual first complete record at its requested key. -/
theorem Step.muPublish [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (before : State Symbol Guard) :
    Step before ⟨{before.heap with nodeRecords :=
      (keepFirst before.heap.nodeRecords (muKey depth ordinary) (.mu entry body depth ordinary))},
      before.unfolding⟩ (.muPublish (muKey depth ordinary)) :=
  .actual (.muPublish entry body depth ordinary) before

/-- A completed real unfolding call retains its actual returned output table and heap. -/
theorem Step.global_done [DecidableEq (EdgeKey Symbol Guard)] (input output : Value Symbol Guard)
    (before : State Symbol Guard) (after : InternedConstructorTemplates.State Symbol Guard)
    (saved : InternedFreshOrdinaryUnfoldMemo.Memo Symbol Guard)
    (actual : InternedFreshOrdinaryUnfoldMemo.run input before.unfolding before.heap = .done (output, saved) after) :
    Step before ⟨after, saved⟩ (.globalUnfold input.referenceOf) := by
  simpa only [perform, actual, Outcome.state, Outcome.event] using Step.actual (.globalUnfold input) before

/-- A pending real unfolding call retains its actual heap and emits the same call event. -/
theorem Step.global_pending [DecidableEq (EdgeKey Symbol Guard)] (input : Value Symbol Guard)
    (before : State Symbol Guard) (key : NodeKey) (after : InternedConstructorTemplates.State Symbol Guard)
    (actual : InternedFreshOrdinaryUnfoldMemo.run input before.unfolding before.heap = .pending key after) :
    Step before ⟨after, before.unfolding⟩ (.globalUnfold input.referenceOf) := by
  simpa only [perform, actual, Outcome.state, Outcome.event] using Step.actual (.globalUnfold input) before

/-- Finite primitive traces retain exact physical states and event order. -/
inductive Runs [DecidableEq (EdgeKey Symbol Guard)] : State Symbol Guard → State Symbol Guard → List (Event Symbol Guard) → Prop where
  | nil (state : State Symbol Guard) : Runs state state []
  | cons (first : Step before middle event) (rest : Runs middle after events) : Runs before after (event :: events)

/-- One actual primitive forms a finite singleton trace. -/
theorem Runs.single [DecidableEq (EdgeKey Symbol Guard)] {before after : State Symbol Guard} {event : Event Symbol Guard}
    (step : Step before after event) : Runs before after [event] := .cons step (.nil after)

/-- Consecutive primitive traces concatenate their actual event lists. -/
theorem Runs.append [DecidableEq (EdgeKey Symbol Guard)] {before middle after : State Symbol Guard}
    {first second : List (Event Symbol Guard)} (left : Runs before middle first) (right : Runs middle after second) :
    Runs before after (first ++ second) := by
  induction left with
  | nil => exact right
  | cons first rest ih => exact .cons first (ih right)

/-- A primitive without a global unfolding event retains its original unfolding table. -/
theorem Step.noGlobal [DecidableEq (EdgeKey Symbol Guard)] {before after : State Symbol Guard} {event : Event Symbol Guard}
    (step : Step before after event) (silent : event.isGlobal = false) : after.unfolding = before.unfolding := by
  cases step with
  | actual primitive before =>
      cases primitive with
      | edge | node | muLookup | muReserve | muPublish => rfl
      | globalUnfold input =>
          cases actual : InternedFreshOrdinaryUnfoldMemo.run input before.unfolding before.heap <;>
            simp only [perform, actual, Outcome.event, Event.isGlobal, Bool.true_eq_false] at silent

/-- The absence of global events derives table retention for an actual finite primitive execution. -/
theorem Runs.noGlobal [DecidableEq (EdgeKey Symbol Guard)] {before after : State Symbol Guard} {events : List (Event Symbol Guard)}
    (runs : Runs before after events) (silent : NoGlobal events) : after.unfolding = before.unfolding := by
  induction runs with
  | nil => rfl
  | cons first rest ih =>
      have split := noGlobal_cons.mp silent
      exact (ih split.2).trans (first.noGlobal split.1)

/-- The real unfolding alternative emits a call event even when its memo lookup hits. -/
theorem globalUnfold_event [DecidableEq (EdgeKey Symbol Guard)] (input : Value Symbol Guard) (before : State Symbol Guard) :
    (perform (.globalUnfold input) before).event = .globalUnfold input.referenceOf := by
  cases actual : InternedFreshOrdinaryUnfoldMemo.run input before.unfolding before.heap <;>
    simp only [perform, actual, Outcome.event]

end MicroCFTA.SourceGlobalUnfold
