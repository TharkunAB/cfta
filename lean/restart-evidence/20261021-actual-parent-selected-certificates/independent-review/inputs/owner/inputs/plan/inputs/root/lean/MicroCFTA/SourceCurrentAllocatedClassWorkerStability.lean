import MicroCFTA.SourceCurrentAllocatedClassWorker
import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability

/-!
# Successful current class execution under larger bounds

Increasing the six bounds preserves each successful class, right fold,
and propagated pass. Equality includes the ordered forest, full checked
state, and completed merge memo. The proof follows actual worker returns.
It requires no physical invariant or completed body callback.
-/
namespace MicroCFTA.SourceCurrentAllocatedClassWorkerStability
open InternedConstructorTemplates
open SourceCurrentAllocatedClassWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Larger bounds retain a successful class return at its exact checked state and merge memo. -/
theorem runClass_done_stable
    {e p h m s n largerE largerP largerH largerM largerS largerN : Nat}
    {record : Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo}
    (actual : runClass e p h m s n record values before memo = .done results after saved)
    (enoughE : e ≤ largerE) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH)
    (enoughM : m ≤ largerM) (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    runClass largerE largerP largerH largerM largerS largerN record values before memo = .done results after saved := by
  cases executed : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit record values e p h m s n)
      (SourceCurrentAllocatedClassEditPlan.compiled record) values
      (SourceCurrentAllocatedSharedTargetState.initial before memo) with
  | done outputs shared =>
      have stable := SourceCurrentAllocatedSharedEditWorkerStability.editList_done_stable executed
        enoughE enoughP enoughH enoughM enoughS enoughN
      simp only [runClass, executed] at actual
      simpa only [runClass, stable] using actual
  | failed =>
      simp only [runClass, executed] at actual
      cases actual

/-- Actual tail success precedes head success under the same larger six bounds. -/
theorem fold_done_stable
    {e p h m s n largerE largerP largerH largerM largerS largerN : Nat}
    {records : List Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo}
    (actual : fold e p h m s n records values before memo = .done results after saved)
    (enoughE : e ≤ largerE) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH)
    (enoughM : m ≤ largerM) (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    fold largerE largerP largerH largerM largerS largerN records values before memo = .done results after saved := by
  induction records generalizing values before memo results after saved with
  | nil => exact actual
  | cons record records ih =>
      cases rest : fold e p h m s n records values before memo with
      | failed =>
          simp only [fold, rest, Outcome.bind] at actual
          cases actual
      | done middle checked current =>
          have stable := ih rest
          have head : runClass e p h m s n record middle checked current = .done results after saved := by
            simpa only [fold, rest, Outcome.bind] using actual
          simp only [fold, stable, Outcome.bind]
          exact runClass_done_stable head enoughE enoughP enoughH enoughM enoughS enoughN

/-- Empty propagation follows the same successful fold and changes no returned state. -/
theorem pass_done_stable
    {e p h m s n largerE largerP largerH largerM largerS largerN : Nat}
    {records : List Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo}
    (actual : pass e p h m s n records values before memo = .done results after saved)
    (enoughE : e ≤ largerE) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH)
    (enoughM : m ≤ largerM) (enoughS : s ≤ largerS) (enoughN : n ≤ largerN) :
    pass largerE largerP largerH largerM largerS largerN records values before memo = .done results after saved := by
  cases executed : fold e p h m s n records values before memo with
  | failed =>
      simp only [pass, executed, Outcome.bind] at actual
      cases actual
  | done outputs checked current =>
      have stable := fold_done_stable executed enoughE enoughP enoughH enoughM enoughS enoughN
      simp only [pass, executed, Outcome.bind] at actual
      simpa only [pass, stable, Outcome.bind] using actual

/-- Two successful class bounds identify the ordered forest, full checked state, and merge memo. -/
theorem runClass_done_unique
    {e p h m s n otherE otherP otherH otherM otherS otherN : Nat}
    {record : Record} {values first second : List (Value Symbol Guard)}
    {before after later : Checked width} {memo saved current : Memo}
    (one : runClass e p h m s n record values before memo = .done first after saved)
    (two : runClass otherE otherP otherH otherM otherS otherN record values before memo = .done second later current) :
    first = second ∧ after = later ∧ saved = current := by
  have firstStable := runClass_done_stable one (Nat.le_max_left e otherE) (Nat.le_max_left p otherP)
    (Nat.le_max_left h otherH) (Nat.le_max_left m otherM) (Nat.le_max_left s otherS) (Nat.le_max_left n otherN)
  have secondStable := runClass_done_stable two (Nat.le_max_right e otherE) (Nat.le_max_right p otherP)
    (Nat.le_max_right h otherH) (Nat.le_max_right m otherM) (Nat.le_max_right s otherS) (Nat.le_max_right n otherN)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

/-- Two successful fold bounds identify the same returned forest and both state components. -/
theorem fold_done_unique
    {e p h m s n otherE otherP otherH otherM otherS otherN : Nat}
    {records : List Record} {values first second : List (Value Symbol Guard)}
    {before after later : Checked width} {memo saved current : Memo}
    (one : fold e p h m s n records values before memo = .done first after saved)
    (two : fold otherE otherP otherH otherM otherS otherN records values before memo = .done second later current) :
    first = second ∧ after = later ∧ saved = current := by
  have firstStable := fold_done_stable one (Nat.le_max_left e otherE) (Nat.le_max_left p otherP)
    (Nat.le_max_left h otherH) (Nat.le_max_left m otherM) (Nat.le_max_left s otherS) (Nat.le_max_left n otherN)
  have secondStable := fold_done_stable two (Nat.le_max_right e otherE) (Nat.le_max_right p otherP)
    (Nat.le_max_right h otherH) (Nat.le_max_right m otherM) (Nat.le_max_right s otherS) (Nat.le_max_right n otherN)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

/-- Two successful pass bounds identify the propagated forest, checked state, and merge memo. -/
theorem pass_done_unique
    {e p h m s n otherE otherP otherH otherM otherS otherN : Nat}
    {records : List Record} {values first second : List (Value Symbol Guard)}
    {before after later : Checked width} {memo saved current : Memo}
    (one : pass e p h m s n records values before memo = .done first after saved)
    (two : pass otherE otherP otherH otherM otherS otherN records values before memo = .done second later current) :
    first = second ∧ after = later ∧ saved = current := by
  have firstStable := pass_done_stable one (Nat.le_max_left e otherE) (Nat.le_max_left p otherP)
    (Nat.le_max_left h otherH) (Nat.le_max_left m otherM) (Nat.le_max_left s otherS) (Nat.le_max_left n otherN)
  have secondStable := pass_done_stable two (Nat.le_max_right e otherE) (Nat.le_max_right p otherP)
    (Nat.le_max_right h otherH) (Nat.le_max_right m otherM) (Nat.le_max_right s otherS) (Nat.le_max_right n otherN)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

end MicroCFTA.SourceCurrentAllocatedClassWorkerStability
