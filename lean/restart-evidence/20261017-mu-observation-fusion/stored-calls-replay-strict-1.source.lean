import MicroCFTA.SourceCurrentStoredSubstitutionCalls
import MicroCFTA.InternedFreshOrdinaryReplay

/-!
# Exact replay of actual ordered stored substitutions

Every completed child sequence retains cache validity and four-table growth.
Its individual calls replay at one common later heap. Repeated sequences
of the same originals therefore return identical ordered value lists.
No future per-child completion is supplied.
-/
namespace MicroCFTA.SourceCurrentStoredCallsReplay
open InternedConstructorTemplates
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentStoredSubstitutionCalls (Calls)
open Language

private theorem execute_correct [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (valid : Valid state) :
    Valid (execute value environment state).state ∧ Grows state (execute value environment state).state :=
  InternedFreshOrdinaryGrowth.build_correct (encode (leaves value) [] value)
    ((leaves value).map (input environment)) state valid

/-- An actual completed child sequence preserves validity and all earlier table entries. -/
theorem correct [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {originals outputs : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (calls : Calls environment originals before outputs after) (valid : Valid before) :
    Valid after ∧ Grows before after := by
  induction calls with
  | nil => exact ⟨valid, grows_refl _⟩
  | cons original originals before middle after output outputs called rest ih =>
      have first : Valid middle ∧ Grows before middle := by
        simpa only [called, Outcome.state] using execute_correct original environment before valid
      have later := ih first.1
      exact ⟨later.1, grows_trans first.2 later.2⟩

/-- Every original occurrence replays its own exact result at one common later heap. -/
theorem replay [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {originals outputs : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (calls : Calls environment originals before outputs after) (common : State Symbol Guard)
    (valid : Valid before) (growth : Grows after common) :
    All₂ (fun original output => execute original environment common = .done output common) originals outputs := by
  induction calls with
  | nil => exact .nil
  | cons original originals before middle after output outputs called rest ih =>
      have first : Valid middle ∧ Grows before middle := by
        simpa only [called, Outcome.state] using execute_correct original environment before valid
      have later := correct rest first.1
      refine .cons ?_ (ih first.1 growth)
      exact InternedFreshOrdinaryReplay.build_replay (encode (leaves original) [] original)
        ((leaves original).map (input environment)) before common output middle valid called
        (grows_trans later.2 growth)

private theorem paired_equal [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    {originals left right : List (Value Symbol Guard)}
    (first : All₂ (fun original output => execute original environment common = .done output common) originals left)
    (second : All₂ (fun original output => execute original environment common = .done output common) originals right) :
    left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons called rest ih =>
      cases second with
      | cons other remaining =>
          have head := (Outcome.done.inj (called.symm.trans other)).1
          exact congr (congrArg List.cons head) (ih remaining)

/-- Two actual sequences of the same originals agree after their final heaps reach one common cache. -/
theorem same [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {originals left right : List (Value Symbol Guard)} {before after later final : State Symbol Guard}
    (first : Calls environment originals before left after) (second : Calls environment originals later right final)
    (common : State Symbol Guard) (firstValid : Valid before) (secondValid : Valid later)
    (firstGrowth : Grows after common) (secondGrowth : Grows final common) : left = right :=
  paired_equal environment common (replay first common firstValid firstGrowth) (replay second common secondValid secondGrowth)

end MicroCFTA.SourceCurrentStoredCallsReplay
