import MicroCFTA.EnumerationWaitingIndex

/-!
# Maintained enumeration indexes

The cached set uses the same slot predicate as the source scan. The sparse
waiting map counts every suspended reference. Initialization, allocation,
and each valid raw-slot write establish both invariants. Reachable index
states derive the invariants from these actual mutation operations.
-/
namespace MicroCFTA.EnumerationExpandableIndex
open EnumerationState EnumerationSchedule EnumerationCorrectness

/-- The source state adds an expandable set and a sparse waiting-count map. -/
structure Cached (Symbol Guard : Type) where
  core : State Symbol Guard
  expandable : Nat → Bool
  waiting : EnumerationWaitingIndex.Waiting

/-- Both cached indexes agree with the complete value-slot scan. -/
structure Correct (graph : Graph Symbol Guard) (state : Cached Symbol Guard) : Prop where
  aligned : state.core.counter = state.core.values.length
  expandable : ∀ uv, state.expandable uv = ((state.core.values[uv]?).map (candidate graph)).getD false
  waiting : EnumerationWaitingIndex.Correct state.core.values state.waiting

/-- Initialize the same root slot and its exact expandable flag. -/
def initial (graph : Graph Symbol Guard) (root : Nat) : Cached Symbol Guard :=
  ⟨EnumerationState.initial root,
    fun uv => if uv = 0 then candidate graph (.unenumerated (some root) []) else false,
    fun _ => none⟩

/-- Allocation adds the fresh slot only when the source predicate accepts it. -/
def allocate (graph : Graph Symbol Guard) (node : Option Nat) (state : Cached Symbol Guard) : Cached Symbol Guard :=
  ⟨allocated node state.core,
    fun uv => if candidate graph (.unenumerated node []) && uv == state.core.counter then true else state.expandable uv,
    state.waiting⟩

/-- One raw-slot write removes old suspended counts before adding the new counts. -/
def write (graph : Graph Symbol Guard) (uv : Nat) (value : UVarValue Symbol) (state : Cached Symbol Guard) :
    Option (Cached Symbol Guard) := do
  let old ← state.core.values[uv]?
  pure ⟨{state.core with values := state.core.values.set uv value},
    fun other => if other = uv then candidate graph value else state.expandable other,
    EnumerationWaitingIndex.replace old value state.waiting⟩

/-- Other source effects update the original state without changing either index. -/
def frame (core : State Symbol Guard) (state : Cached Symbol Guard) : Cached Symbol Guard :=
  {state with core := core}

/-- Initialization derives both indexes and their slot-domain bound. -/
theorem initial_correct (graph : Graph Symbol Guard) (root : Nat) : Correct graph (initial graph root) := by
  refine ⟨rfl, ?_, EnumerationWaitingIndex.initial_correct root⟩
  intro uv
  cases uv <;> simp [initial, EnumerationState.initial]

/-- Fresh allocation preserves the exact expandable slots and waiting multiplicities. -/
theorem allocate_correct (graph : Graph Symbol Guard) (node : Option Nat) (state : Cached Symbol Guard)
    (correct : Correct graph state) : Correct graph (allocate graph node state) := by
  refine ⟨allocated_supply node state.core correct.aligned, ?_, EnumerationWaitingIndex.allocate_correct _ node _ correct.waiting⟩
  intro uv
  by_cases before : uv < state.core.values.length
  · have different : uv ≠ state.core.counter := by rw [correct.aligned]; omega
    simp only [allocate, allocated, List.getElem?_append_left before]
    simp [different, correct.expandable uv]
  · by_cases same : uv = state.core.counter
    · simp [allocate, allocated, correct.aligned, same, correct.expandable]
    · have after : state.core.values.length < uv := by rw [correct.aligned] at same; omega
      have absent : state.core.values[uv]? = none := List.getElem?_eq_none (by omega)
      have wholeAbsent : (state.core.values ++ [.unenumerated node []])[uv]? = none :=
        List.getElem?_eq_none (by simp; omega)
      simp [allocate, allocated, same, wholeAbsent, correct.expandable, absent]

/-- Successful raw-slot writes preserve both indexes without resolving the written UVar. -/
theorem write_correct (graph : Graph Symbol Guard) (uv : Nat) (value : UVarValue Symbol)
    (before after : Cached Symbol Guard) (correct : Correct graph before)
    (done : write graph uv value before = some after) : Correct graph after := by
  cases stored : before.core.values[uv]? with
  | none => simp [write, stored] at done
  | some old =>
      simp [write, stored] at done
      subst after
      refine ⟨by simpa using correct.aligned, ?_, EnumerationWaitingIndex.replace_correct _ uv old value stored _ correct.waiting⟩
      intro other
      by_cases same : other = uv
      · subst other
        have bound := (List.getElem?_eq_some_iff.mp stored).1
        simp [bound]
      · simp [same, Ne.symm same, correct.expandable other]

/-- State effects that keep the slots and supply keep both cached indexes correct. -/
theorem frame_correct (graph : Graph Symbol Guard) (state : Cached Symbol Guard) (core : State Symbol Guard)
    (correct : Correct graph state) (values : core.values = state.core.values) (counter : core.counter = state.core.counter) :
    Correct graph (frame core state) := by
  refine ⟨counter.trans (correct.aligned.trans (congrArg List.length values.symm)), ?_, ?_⟩
  · intro uv; simpa [frame, values] using correct.expandable uv
  · simpa [frame, values] using correct.waiting

/-- Reachability records every authorized slot mutation and every slot-preserving source effect. -/
inductive Reachable (graph : Graph Symbol Guard) : Cached Symbol Guard → Prop where
  | initial (root : Nat) : Reachable graph (initial graph root)
  | allocate {state} (node : Option Nat) (before : Reachable graph state) : Reachable graph (allocate graph node state)
  | write {before after} (uv : Nat) (value : UVarValue Symbol) (reached : Reachable graph before)
      (done : write graph uv value before = some after) : Reachable graph after
  | frame {state} (core : State Symbol Guard) (reached : Reachable graph state)
      (values : core.values = state.core.values) (counter : core.counter = state.core.counter) : Reachable graph (frame core state)

/-- Every reachable cached state derives both maintained invariants from initialization. -/
theorem Reachable.correct {graph : Graph Symbol Guard} {state : Cached Symbol Guard} (reached : Reachable graph state) :
    Correct graph state := by
  induction reached with
  | initial root => exact initial_correct graph root
  | allocate node reached ih => exact allocate_correct graph node _ ih
  | write uv value reached done ih => exact write_correct graph uv value _ _ ih done
  | frame core reached values counter ih => exact frame_correct graph _ core ih values counter

/-- The successful assimilation branch performs the two source writes in order. -/
def assimilate (graph : Graph Symbol Guard) (target source : Nat) (merged : UVarValue Symbol)
    (state : Cached Symbol Guard) : Option (Cached Symbol Guard) := do
  let first ← write graph target merged state
  let second ← write graph source .eliminated first
  pure (frame (assimilated state.core target source merged) second)

/-- A successful write has the exact old raw-slot effect and leaves the name supply unchanged. -/
theorem write_core (graph : Graph Symbol Guard) (uv : Nat) (value : UVarValue Symbol)
    (before after : Cached Symbol Guard) (done : write graph uv value before = some after) :
    after.core = {before.core with values := before.core.values.set uv value} := by
  cases stored : before.core.values[uv]? <;> simp [write, stored] at done
  subst after
  rfl

/-- Actual successful assimilation derives both maintained indexes from its two source writes. -/
theorem assimilate_reachable (graph : Graph Symbol Guard) (target source : Nat) (merged : UVarValue Symbol)
    (before after : Cached Symbol Guard) (reached : Reachable graph before)
    (done : assimilate graph target source merged before = some after) : Reachable graph after := by
  unfold assimilate at done
  cases firstDone : write graph target merged before with
  | none => simp [firstDone] at done
  | some first =>
      cases secondDone : write graph source .eliminated first with
      | none => simp [firstDone, secondDone] at done
      | some second =>
          simp [firstDone, secondDone] at done
          subst after
          have firstCore := write_core graph target merged before first firstDone
          have secondCore := write_core graph source .eliminated first second secondDone
          apply Reachable.frame _ (Reachable.write source .eliminated (Reachable.write target merged reached firstDone) secondDone)
          · simp [assimilated, firstCore, secondCore]
          · simp [assimilated, firstCore, secondCore]

/-- Assimilation changes the original state exactly as in the existing source model. -/
theorem assimilate_core (graph : Graph Symbol Guard) (target source : Nat) (merged : UVarValue Symbol)
    (before after : Cached Symbol Guard) (done : assimilate graph target source merged before = some after) :
    after.core = assimilated before.core target source merged := by
  unfold assimilate at done
  cases firstDone : write graph target merged before <;> simp [firstDone] at done
  rename_i first
  cases secondDone : write graph source .eliminated first <;> simp [secondDone] at done
  subst after
  rfl

/-- Every successful nontrivial source assimilation branch has the same indexed update and derives both indexes. -/
theorem assimilate_source (graph : Graph Symbol Guard) (before : Cached Symbol Guard)
    (target source : Nat) (sourceNode targetNode : Option Nat) (sourceScs targetScs : List Suspended)
    (merged : UVarValue Symbol) (reached : Reachable graph before) (different : target ≠ source)
    (sourceRead : before.core.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetRead : before.core.values[target]? = some (.unenumerated targetNode targetScs))
    (intersection : intersectValues graph (.unenumerated sourceNode sourceScs) (.unenumerated targetNode targetScs) = some merged)
    (notEmpty : hasEmptyContents graph merged = false) :
    ∃ after, assimilate graph target source merged before = some after ∧ Reachable graph after ∧
      EnumerationState.assimilate graph target source before.core = [.ok ((), after.core)] := by
  cases done : assimilate graph target source merged before with
  | none => simp [assimilate, write, targetRead, different, sourceRead] at done
  | some after =>
      refine ⟨after, rfl, assimilate_reachable graph target source merged before after reached done, ?_⟩
      rw [assimilate_core graph target source merged before after done]
      exact assimilate_exact graph before.core target source sourceNode targetNode sourceScs targetScs merged
        different sourceRead targetRead intersection notEmpty

end MicroCFTA.EnumerationExpandableIndex
