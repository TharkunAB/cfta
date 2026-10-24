import MicroCFTA.EnumerationCanonicalWaiting
import MicroCFTA.EnumerationCompressionFrame
import MicroCFTA.EnumerationIndexSelection
import MicroCFTA.EnumerationUntil
import MicroCFTA.EnumerationCPS

/-!
# Pure selection from canonical enumeration indexes

The waiting keys are representatives, as in the current Haskell source.
Selection reads the indexes and changes no forest. The older slot scan
returns the same offered list and preserves the complete compression frame.
-/
namespace MicroCFTA.EnumerationPureSelection

open EnumerationState EnumerationSchedule EnumerationCorrectness
open EnumerationExpandableIndex (Cached)

/-- Candidate flags and canonical waiting counts describe the stored slots. -/
structure Correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard) : Prop where
  /-- The dense slot domain agrees with the allocation supply. -/
  aligned : state.core.counter = state.core.values.length
  /-- Each flag is the actual source candidate predicate. -/
  expandable : ∀ uv, state.expandable uv = ((state.core.values[uv]?).map (candidate graph)).getD false
  /-- Each waiting key counts references to its representative class. -/
  waiting : EnumerationCanonicalWaiting.Correct roots state.core.values state.waiting

/-- Replace one raw slot and update its candidate flag and canonical counts. -/
def write (graph : Graph Symbol Guard) (roots : Nat → Nat) (uv : Nat) (value : UVarValue Symbol)
    (state : Cached Symbol Guard) : Option (Cached Symbol Guard) := do
  let old ← state.core.values[uv]?
  pure ⟨{state.core with values := state.core.values.set uv value},
    fun other => if other = uv then candidate graph value else state.expandable other,
    EnumerationCanonicalWaiting.replace roots old value state.waiting⟩

/-- Transfer the old representative counters to the final union representative. -/
def transfer (target : Nat) (sources : List Nat) (state : Cached Symbol Guard) : Cached Symbol Guard :=
  {state with waiting := EnumerationCanonicalWaiting.moveMany target sources state.waiting}

/-- The actual initial candidate set and empty waiting map are correct. -/
theorem initial_correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (root : Nat) :
    Correct graph roots (EnumerationExpandableIndex.initial graph root) := by
  refine ⟨rfl, ?_, EnumerationCanonicalWaiting.initial_correct roots root⟩
  intro uv
  cases uv <;> simp [EnumerationExpandableIndex.initial, EnumerationState.initial]

/-- Fresh allocation preserves both maintained indexes. -/
theorem allocate_correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (node : Option Nat)
    (state : Cached Symbol Guard) (correct : Correct graph roots state) :
    Correct graph roots (EnumerationExpandableIndex.allocate graph node state) := by
  refine ⟨allocated_supply node state.core correct.aligned, ?_,
    EnumerationCanonicalWaiting.allocate_correct roots state.core.values node state.waiting correct.waiting⟩
  intro uv
  by_cases before : uv < state.core.values.length
  · have different : uv ≠ state.core.counter := by rw [correct.aligned]; omega
    simp only [EnumerationExpandableIndex.allocate, allocated, List.getElem?_append_left before]
    simp [different, correct.expandable uv]
  · by_cases same : uv = state.core.counter
    · simp [EnumerationExpandableIndex.allocate, allocated, correct.aligned, same, correct.expandable]
    · have after : state.core.values.length < uv := by rw [correct.aligned] at same; omega
      have absent : state.core.values[uv]? = none := List.getElem?_eq_none (by omega)
      have wholeAbsent : (state.core.values ++ [.unenumerated node []])[uv]? = none :=
        List.getElem?_eq_none (by simp; omega)
      simp [EnumerationExpandableIndex.allocate, allocated, same, wholeAbsent, correct.expandable, absent]

/-- A successful source slot write preserves the candidate and canonical-count equations. -/
theorem write_correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (uv : Nat) (value : UVarValue Symbol)
    (before after : Cached Symbol Guard) (correct : Correct graph roots before)
    (done : write graph roots uv value before = some after) : Correct graph roots after := by
  cases stored : before.core.values[uv]? with
  | none => simp [write, stored] at done
  | some old =>
      simp [write, stored] at done
      subst after
      refine ⟨by simpa using correct.aligned, ?_,
        EnumerationCanonicalWaiting.replace_correct roots before.core.values uv old value stored before.waiting correct.waiting⟩
      intro other
      by_cases same : other = uv
      · subst other
        have bound := (List.getElem?_eq_some_iff.mp stored).1
        simp [bound]
      · simp [same, Ne.symm same, correct.expandable other]

/-- Slot and supply preservation retains the index equations at a fixed root map. -/
theorem frame_correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard)
    (core : State Symbol Guard) (correct : Correct graph roots state)
    (values : core.values = state.core.values) (counter : core.counter = state.core.counter) :
    Correct graph roots (EnumerationExpandableIndex.frame core state) := by
  refine ⟨counter.trans (correct.aligned.trans (congrArg List.length values.symm)), ?_, ?_⟩
  · intro uv; simpa [EnumerationExpandableIndex.frame, values] using correct.expandable uv
  · simpa [EnumerationExpandableIndex.frame, values] using correct.waiting

/-- Counter transfer follows the partial root map through the complete transfer fold. -/
theorem transfer_correct (graph : Graph Symbol Guard) (roots : Nat → Nat) (target : Nat) (sources : List Nat)
    (state : Cached Symbol Guard) (correct : Correct graph roots state) :
    Correct graph (sources.foldl (fun partial source => EnumerationCanonicalWaiting.redirect target source partial) roots)
      (transfer target sources state) :=
  ⟨correct.aligned, correct.expandable,
    EnumerationCanonicalWaiting.moveMany_correct target sources roots state.core.values state.waiting correct.waiting⟩

/-- The cached candidate list is exactly the stop test's complete pending list. -/
theorem candidates_exact (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard)
    (correct : Correct graph roots state) :
    EnumerationIndexSelection.candidates state = EnumerationUntil.remaining graph state.core := by
  unfold EnumerationIndexSelection.candidates EnumerationUntil.remaining
  rw [correct.aligned, List.range_eq_range', ← List.zipIdx_map_snd 0 state.core.values, List.filter_map]
  congr 1
  apply List.filter_congr
  intro entry member
  have stored := List.mem_zipIdx_iff_getElem?.mp member
  simp only [Function.comp_def, correct.expandable, stored, Option.map_some, Option.getD_some]

/-- Subtract canonical waiting keys without a lookup or a compression write. -/
def find (state : Cached Symbol Guard) : Option (List Nat) :=
  let candidates := EnumerationIndexSelection.candidates state
  if candidates.isEmpty then none
  else some (candidates.filter fun uv => (state.waiting uv).isNone)

/-- Apply the source preference rule to the pure candidate-minus-waiting result. -/
def next (preference : List Nat → Option Nat) (state : Cached Symbol Guard) : Next :=
  pickNext preference (find state)

/-- Execute the pure lookup through the existing source CPS state operation. -/
def findAction : EnumerationCPS.Computation (Cached Symbol Guard) (Option (List Nat)) :=
  EnumerationCPS.state fun state => (find state, state)

/-- Pure cached lookup returns one result with the complete input state unchanged. -/
theorem findAction_represents : EnumerationCPS.Represents
    (findAction : EnumerationCPS.Computation (Cached Symbol Guard) (Option (List Nat)))
    (fun state => [(find state, state)]) :=
  EnumerationCPS.state_represents (fun state => (find state, state))

/-- Canonical cached selection equals the full slot scan's mathematical summary. -/
theorem find_exact (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard)
    (correct : Correct graph roots state) :
    find state = let summary := state.core.values.zipIdx.foldl (collectPure graph roots) ([], [])
      offered summary.1 summary.2 := by
  have candidatesSame : EnumerationIndexSelection.candidates state =
      (state.core.values.zipIdx.foldl (collectPure graph roots) ([], [])).1 := by
    rw [candidates_exact graph roots state correct, EnumerationIndexSelection.candidate_fold]
    rfl
  have blocked (uv : Nat) : state.waiting uv ≠ none ↔
      uv ∈ (state.core.values.zipIdx.foldl (collectPure graph roots) ([], [])).2 :=
    (EnumerationCanonicalWaiting.support_exact roots state.core.values state.waiting correct.waiting uv).trans
      (EnumerationIndexSelection.scan_blocked graph roots state.core.values uv).symm
  unfold find
  rw [candidatesSame]
  unfold offered
  split
  · rfl
  · congr 1
    apply List.filter_congr
    intro uv _
    cases stored : state.waiting uv with
    | none =>
        have absent : uv ∉ (state.core.values.zipIdx.foldl (collectPure graph roots) ([], [])).2 :=
          fun present => (blocked uv).mpr present stored
        simp [absent]
    | some count =>
        have present := (blocked uv).mp (by simp [stored])
        simp [present]

/-- Every successful old scan agrees with pure selection and retains the full compression frame. -/
theorem scan_agrees (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard)
    (correct : Correct graph roots state) (paths : Roots state.core.representatives roots)
    (fuel : Nat) (result : Option (List Nat)) (after : State Symbol Guard)
    (success : Success (findExpandable graph fuel) state.core result after) :
    result = find state ∧ EnumerationCompressionFrame.Frame state.core after := by
  have total : UnionFind.Total state.core.representatives := by
    intro uv
    obtain ⟨size, path⟩ := paths uv
    exact ⟨roots uv, size, path⟩
  exact ⟨(findExpandable_exact graph fuel roots state.core after result paths success).2.trans
    (find_exact graph roots state correct).symm,
    EnumerationCompressionFrame.findExpandable_frame graph fuel state.core after result total success⟩

/-- A total representative interpretation supplies a finite old scan for the same pure selection. -/
theorem scan_complete (graph : Graph Symbol Guard) (roots : Nat → Nat) (state : Cached Symbol Guard)
    (correct : Correct graph roots state) (paths : Roots state.core.representatives roots) :
    ∃ fuel after, Success (findExpandable graph fuel) state.core (find state) after ∧
      EnumerationCompressionFrame.Frame state.core after := by
  have total : UnionFind.Total state.core.representatives := by
    intro uv
    obtain ⟨size, path⟩ := paths uv
    exact ⟨roots uv, size, path⟩
  obtain ⟨fuel, result, after, success⟩ := EnumerationExecution.findExpandable_terminates graph state.core total
  obtain ⟨same, frame⟩ := scan_agrees graph roots state correct paths fuel result after success
  exact ⟨fuel, after, same ▸ success, frame⟩

end MicroCFTA.EnumerationPureSelection
