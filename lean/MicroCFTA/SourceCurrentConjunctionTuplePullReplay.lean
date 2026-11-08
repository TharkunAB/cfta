import MicroCFTA.SourceCurrentConjunctionTuplePullReadTrace

/-!
# Replay of the actual cursor demand sequence

A replayed physical exposure sequence identifies each completed singleton
read through `Read.unique`. The cursor then returns the same event, tuple,
continuation, heap, and equality state. The new read bound can be smaller.

The exposure receipt is an internal composition premise. It records only
the demands of the actual finite observation. It does not supply future
operand views or force the continuation after an overflow.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullReplay
open InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Physical Outcome exposures)
open SourceCurrentConjunctionTuplePull (Cursor Event step expose)
open SourceCurrentConjunctionTuplePullAdmission (Status advance drive)
open SourceCurrentConjunctionTuplePullReads (requested)
open SourceCurrentConjunctionTuplePullReadTrace (demands)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Only the native read demanded by this transition must agree. -/
def SameRead (h H : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula) : Prop :=
  match requested cursor with
  | none => True
  | some node =>
      MergedFreshOrdinaryExposure.nodeEdges H node before.heap =
        MergedFreshOrdinaryExposure.nodeEdges h node before.heap

variable [DecidableEq Symbol]

/-- Agreement at the current demand preserves the complete transition outcome. -/
theorem step_replay (h H : Nat) (cursor : Cursor Symbol Formula) (before : Physical Symbol Formula)
    (same : SameRead h H cursor before) : step H cursor before = step h cursor before := by
  induction cursor generalizing before with
  | empty => rfl
  | seed node =>
      simp only [SameRead, requested] at same
      simp only [step, expose, exposures, same]
  | seedRows rows => cases rows <;> rfl
  | extend node inner ih =>
      have own : SameRead h H inner before := same
      simp only [step, ih before own]
  | readOperand node inner tuple _ih =>
      cases tuple with
      | nil => rfl
      | cons first rest =>
          simp only [SameRead, requested] at same
          simp only [step, expose, exposures, same]
  | scanOperand node inner tuple rows _ih =>
      cases tuple with
      | nil => rfl
      | cons first rest =>
          cases rows with
          | nil => rfl
          | cons edge rows => rfl

omit [DecidableEq Symbol] in
private theorem exposures_cons (H : Nat) (node : Node) (tail : List Node)
    (before final : Physical Symbol Formula) (rows : List (List Edge))
    (actual : exposures H (node :: tail) before = .done rows final) :
    ∃ own heap remaining,
      MergedFreshOrdinaryExposure.nodeEdges H node before.heap = .done own heap ∧
        exposures H tail ⟨heap, before.equality⟩ = .done remaining final := by
  cases observed : MergedFreshOrdinaryExposure.nodeEdges H node before.heap with
  | pending | unresolved | exhausted =>
      simp only [exposures, observed] at actual
      cases actual
  | done own heap =>
      simp only [exposures, observed] at actual
      cases later : exposures H tail ⟨heap, before.equality⟩ with
      | failed fault reached =>
          simp only [later, Outcome.bind] at actual
          cases actual
      | done remaining reached =>
          simp only [later, Outcome.bind] at actual
          have same := (Outcome.done.inj actual).2
          exact ⟨own, heap, remaining, rfl, by simpa only [same] using later⟩

private theorem step_tape (h H : Nat) (cursor : Cursor Symbol Formula)
    (before middle final : Physical Symbol Formula) (event : Event Symbol Formula)
    (tail : List Node) (rows : List (List Edge))
    (actual : step h cursor before = .done event middle)
    (replayed : exposures H ((requested cursor).toList ++ tail) before = .done rows final) :
    step H cursor before = .done event middle ∧
      ∃ remaining, exposures H tail middle = .done remaining final := by
  have read := SourceCurrentConjunctionTuplePullReads.step_requested h cursor before middle event actual
  cases selected : requested cursor with
  | none =>
      simp only [selected] at read
      have same : SameRead h H cursor before := by simp only [SameRead, selected]
      refine ⟨(step_replay h H cursor before same).trans actual, rows, ?_⟩
      simpa only [selected, Option.toList_none, List.nil_append, read] using replayed
  | some node =>
      simp only [selected] at read
      obtain ⟨oldRows, oldRead⟩ := read
      have tape : exposures H (node :: tail) before = .done rows final := by
        simpa only [selected, Option.toList_some, List.singleton_append] using replayed
      obtain ⟨newRows, heap, remaining, newRead, later⟩ := exposures_cons H node tail before final rows tape
      have unique := SourceEqualityProjectionRead.Read.unique (.done h oldRead) (.done H newRead)
      have equality : middle.equality = before.equality := by
        simpa only [actual, Outcome.state] using
          SourceCurrentConjunctionTuplePull.step_equality h cursor before
      have stateSame : (⟨heap, before.equality⟩ : Physical Symbol Formula) = middle := by
        cases middle with
        | mk middleHeap middleEquality =>
            have heapSame : middleHeap = heap := unique.2
            change middleEquality = before.equality at equality
            change (⟨heap, before.equality⟩ : Physical Symbol Formula) = ⟨middleHeap, middleEquality⟩
            cases heapSame
            cases equality
            rfl
      have same : SameRead h H cursor before := by
        simp only [SameRead, selected]
        rw [newRead, oldRead, unique.1, unique.2]
      refine ⟨(step_replay h H cursor before same).trans actual, remaining, ?_⟩
      simpa only [stateSame] using later

private theorem advance_step (h budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before after : Physical Symbol Formula) (status : Status Symbol Formula)
    (actual : advance h budget cursor collected before = .done status after) :
    ∃ event, step h cursor before = .done event after := by
  cases observed : step h cursor before with
  | failed fault middle =>
      simp only [advance, observed, Outcome.bind] at actual
      cases actual
  | done event middle =>
      have same : middle = after := by
        cases event with
        | more next | ended =>
            simp only [advance, observed, Outcome.bind] at actual
            exact (Outcome.done.inj actual).2
        | yield tuple next =>
            simp only [advance, observed, Outcome.bind] at actual
            split at actual <;> exact (Outcome.done.inj actual).2
      exact ⟨event, by simp only [same]⟩

private theorem drive_replay_exact (steps h H budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before after : Physical Symbol Formula) (status : Status Symbol Formula)
    (rows : List (List Edge))
    (actual : drive steps h budget cursor collected before = .done status after)
    (replayed : exposures H (demands steps h budget cursor collected before) before = .done rows after) :
    drive steps H budget cursor collected before = .done status after := by
  induction steps generalizing cursor collected before after status rows with
  | zero => exact actual
  | succ steps ih =>
      cases observed : advance h budget cursor collected before with
      | failed fault middle =>
          simp only [drive, observed, Outcome.bind] at actual
          cases actual
      | done reached middle =>
          obtain ⟨event, transition⟩ := advance_step h budget cursor collected before middle reached observed
          let tail := match reached with
            | .running next sampled => demands steps h budget next sampled middle
            | _ => []
          have tape : exposures H ((requested cursor).toList ++ tail) before = .done rows after := by
            cases reached <;> simpa only [demands, observed, tail] using replayed
          obtain ⟨transitionH, remaining, later⟩ :=
            step_tape h H cursor before middle after event tail rows transition tape
          have observedH : advance H budget cursor collected before = .done reached middle := by
            simpa only [advance, transition, transitionH] using observed
          cases reached with
          | running next sampled =>
              have recursive : drive steps h budget next sampled middle = .done status after := by
                simpa only [drive, observed, Outcome.bind] using actual
              have replayedTail :
                  exposures H (demands steps h budget next sampled middle) middle = .done remaining after := later
              have done := ih next sampled middle after status remaining recursive replayedTail
              simpa only [drive, observedH, Outcome.bind] using done
          | fit sampled =>
              simpa only [drive, observed, observedH, Outcome.bind] using actual
          | overflow sampled next =>
              simpa only [drive, observed, observedH, Outcome.bind] using actual

/-- Replaying the actual demand tape at any successful read bound preserves the full observation. -/
theorem drive_replay (steps h H budget : Nat) (cursor : Cursor Symbol Formula)
    (collected : List (List Edge)) (before after : Physical Symbol Formula) (status : Status Symbol Formula)
    (rows : List (List Edge))
    (actual : drive steps h budget cursor collected before = .done status after)
    (replayed : exposures H (demands steps h budget cursor collected before) before =
      .done rows ⟨after.heap, before.equality⟩) :
    drive steps H budget cursor collected before = .done status after := by
  have equality : after.equality = before.equality := by
    simpa only [actual, Outcome.state] using
      SourceCurrentConjunctionTuplePullAdmission.drive_equality steps h budget cursor collected before
  have stateSame : (⟨after.heap, before.equality⟩ : Physical Symbol Formula) = after := by
    cases after with
    | mk heap operations =>
        change operations = before.equality at equality
        change (⟨heap, before.equality⟩ : Physical Symbol Formula) = ⟨heap, operations⟩
        cases equality
        rfl
  exact drive_replay_exact steps h H budget cursor collected before after status rows actual
    (by simpa only [stateSame] using replayed)

end MicroCFTA.SourceCurrentConjunctionTuplePullReplay
