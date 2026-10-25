import MicroCFTA.SourcePruningEnumerationRestart

namespace MicroCFTA.SourcePruningEnumerationAfterCallback
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDriver EnumerationCompressionFrame
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {Typing : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Run the concrete fragment callback and restart only when its pruning flag is false. -/
def run (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment) (before : Cached) :
    EnumerateM Symbol Constraint (Metadata Typing × Option Next) := do
  let result ← recordTypes graph templates fuel metadata uv (.inl fragment)
  require (!result.1)
  let after ← get
  SourcePruningEnumerationRestart.run stop order result.2 (EnumerationExpandableIndex.frame after before)

/-- An accepted callback retains its actual cache and returns the source restart decision. -/
theorem run_success (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment) (before : Cached)
    (result : Bool × Metadata Typing) (after : EnumerationState.State Symbol Constraint)
    (callback : Success (recordTypes graph templates fuel metadata uv (.inl fragment)) before.core result after)
    (accepted : result.1 = false)
    (allowed : SourcePruningEnumerationRestart.decision stop order result.2
      (EnumerationExpandableIndex.frame after before) ≠ some .stuck) :
    Success (run graph templates stop order fuel metadata uv fragment before) before.core
      (result.2, SourcePruningEnumerationRestart.decision stop order result.2
        (EnumerationExpandableIndex.frame after before)) after := by
  unfold run
  apply (success_bind _ _ _ _ _).mpr
  refine ⟨result, after, callback, ?_⟩
  apply (success_bind _ _ _ _ _).mpr
  refine ⟨(), after, (require_success _ after after).mpr ⟨by simp [accepted], rfl⟩, ?_⟩
  apply (success_bind _ _ _ _ _).mpr
  refine ⟨after, after, (get_success after after after).mpr ⟨rfl, rfl⟩, ?_⟩
  simp [Success, SourcePruningEnumerationRestart.run, allowed]

/-- A known pruning result excludes every successful continuation of the same callback action. -/
theorem run_pruned (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment) (before : Cached)
    (result : Bool × Metadata Typing) (after : EnumerationState.State Symbol Constraint)
    (total : UnionFind.Total before.core.representatives)
    (callback : Success (recordTypes graph templates fuel metadata uv (.inl fragment)) before.core result after)
    (pruned : result.1 = true) (output : Metadata Typing × Option Next)
    (final : EnumerationState.State Symbol Constraint) :
    ¬Success (run graph templates stop order fuel metadata uv fragment before) before.core output final := by
  intro observed
  unfold run at observed
  obtain ⟨other, reached, otherCallback, continued⟩ := (success_bind _ _ _ _ _).mp observed
  have same := (recordTypes_agrees graph templates fuel fuel metadata uv (.inl fragment)
    before.core before.core after reached result other (.refl _) total callback otherCallback).1
  subst other
  obtain ⟨ignored, guarded, required, _continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have accepted := (require_success _ reached guarded).mp required |>.1
  simp only [pruned, Bool.not_true, Bool.false_eq_true] at accepted

/-- A known stuck restart excludes every successful continuation, including other compressed endpoints. -/
theorem run_stuck (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment) (before : Cached)
    (result : Bool × Metadata Typing) (after : EnumerationState.State Symbol Constraint)
    (total : UnionFind.Total before.core.representatives)
    (callback : Success (recordTypes graph templates fuel metadata uv (.inl fragment)) before.core result after)
    (stuck : SourcePruningEnumerationRestart.decision stop order result.2
      (EnumerationExpandableIndex.frame after before) = some .stuck)
    (output : Metadata Typing × Option Next) (final : EnumerationState.State Symbol Constraint) :
    ¬Success (run graph templates stop order fuel metadata uv fragment before) before.core output final := by
  intro observed
  unfold run at observed
  obtain ⟨other, reached, otherCallback, continued⟩ := (success_bind _ _ _ _ _).mp observed
  obtain ⟨same, frame⟩ := recordTypes_agrees graph templates fuel fuel metadata uv (.inl fragment)
    before.core before.core after reached result other (.refl _) total callback otherCallback
  subst other
  obtain ⟨ignored, guarded, required, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have guardSame := ((require_success _ reached guarded).mp required).2
  subst guarded
  obtain ⟨current, readAfter, reading, restarted⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨currentSame, readSame⟩ := (get_success reached readAfter current).mp reading
  subst current
  subst readAfter
  have stuckAfter : SourcePruningEnumerationRestart.decision stop order result.2
      (EnumerationExpandableIndex.frame reached before) = some .stuck := by
    have retained := SourcePruningEnumerationRestart.decision_frame stop order result.2
      (EnumerationExpandableIndex.frame after before) reached frame.counter
    have sameDecision : SourcePruningEnumerationRestart.decision stop order result.2
        (EnumerationExpandableIndex.frame reached before) =
        SourcePruningEnumerationRestart.decision stop order result.2
          (EnumerationExpandableIndex.frame after before) := by
      simpa only [EnumerationExpandableIndex.frame] using retained
    exact sameDecision.trans stuck
  simp [SourcePruningEnumerationRestart.run, stuckAfter, Success] at restarted

/-- The callback's actual Boolean and restart decision determine its successful continuations. -/
def Follows (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment) (before : Cached)
    (result : Bool × Metadata Typing) (after : EnumerationState.State Symbol Constraint) : Prop :=
  ∀ stop order,
    let decision := SourcePruningEnumerationRestart.decision stop order result.2
      (EnumerationExpandableIndex.frame after before)
    ((result.1 = true ∨ decision = some .stuck) →
      ∀ output final, ¬Success (run graph templates stop order fuel metadata uv fragment before)
        before.core output final) ∧
    (result.1 = false → decision ≠ some .stuck →
      Success (run graph templates stop order fuel metadata uv fragment before) before.core (result.2, decision) after)

/-- A genuine callback receipt derives rejection or restart without any future-success premise. -/
theorem follows (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment) (before : Cached)
    (result : Bool × Metadata Typing) (after : EnumerationState.State Symbol Constraint)
    (total : UnionFind.Total before.core.representatives)
    (callback : Success (recordTypes graph templates fuel metadata uv (.inl fragment)) before.core result after) :
    Follows graph templates fuel metadata uv fragment before result after := by
  intro stop order
  constructor
  · intro rejected output final
    rcases rejected with pruned | stuck
    · exact run_pruned graph templates stop order fuel metadata uv fragment before result after total callback pruned output final
    · exact run_stuck graph templates stop order fuel metadata uv fragment before result after total callback stuck output final
  · intro accepted allowed
    exact run_success graph templates stop order fuel metadata uv fragment before result after callback accepted allowed

end MicroCFTA.SourcePruningEnumerationAfterCallback
