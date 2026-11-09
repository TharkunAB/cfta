import MicroCFTA.SourcePruningEnumerationSharedEnabledEmpty

/-!
# Observers for actual enabled shared checks

A skipped check retains the checked state and fourth memo. Its conservative
answer is false. A performed check retains its actual returned state and
memo on success or failure. Only successful outcomes have a completed answer.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedEnabledEmpty
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
variable {width : Nat}

/-- Read the actual checked endpoint of either enabled-check branch. -/
def Outcome.state : Outcome width → Checked width
  | .skipped checked _ => checked
  | .performed observed => observed.state

/-- Read the actual fourth memo without adding a skipped worker observation. -/
def Outcome.memo : Outcome width → Fourth
  | .skipped _ memo => memo
  | .performed observed => observed.memo

/-- Skips complete conservatively; performed failures retain no Boolean verdict. -/
def Outcome.completed : Outcome width → Option Bool
  | .skipped _ _ => some false
  | .performed (.done answer _ _ _) => some answer
  | .performed (.failed _ _ _ _) => none

/-- An absent completed verdict retains an actual performed failure and all its returned fields. -/
theorem Outcome.completed_none_iff (outcome : Outcome width) :
    outcome.completed = none ↔
      ∃ fault checked memo snapshot, outcome = .performed (.failed fault checked memo snapshot) := by
  cases outcome with
  | skipped checked memo =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨fault, after, saved, snapshot, impossible⟩
        cases impossible
  | performed observed =>
      cases observed with
      | done answer checked memo snapshot =>
          constructor
          · intro impossible
            cases impossible
          · rintro ⟨fault, after, saved, privateState, impossible⟩
            cases impossible
      | failed fault checked memo snapshot =>
          exact ⟨fun _ => ⟨fault, checked, memo, snapshot, rfl⟩, fun _ => rfl⟩

end MicroCFTA.SourcePruningEnumerationSharedEnabledEmpty
