import MicroCFTA.SourceCurrentSharedOuterExecutionAncestry

/-!
# Exact completed indexed prefixes in the shared child walk

The split retains the actual intermediate caller, original child order
and next index. It does not assume the remaining walk completes.
-/
namespace MicroCFTA.SourceCurrentSharedOuterWalkPrefix
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedSharedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentSharedOuterExecutionAncestry (Step Reached)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "descend" => SourceCurrentAllocatedSharedPartialGraph.descend

private theorem bind_done {A B : Type} (first : Outcome A width)
    (next : A → Caller width → Outcome B width) {result : B} {after : Caller width}
    (actual : first.bind next = .done result after) :
    ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value middle => exact ⟨value,middle,rfl,actual⟩
  | failed => cases actual

section Workers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {width : Nat}

/-- Completed earlier siblings derive the exact indexed dispatch without an enclosing return. -/
theorem walk_prefix {fuel g s r e p h m c n budget offset slot : Nat}
    {combined : EqValue} {values outputs : List Node} {value : Node} {before start : Caller width}
    (earlierCalls : walk (fuel + slot + 1) g s r e p h m c n budget combined offset
      (values.take slot) before = .done outputs start)
    (selected : values[slot]? = some value) :
    Reached g s r e p h m c n budget
      (.walk (fuel + slot + 1) combined offset values before)
      (.node fuel ⟨(descend start combined (offset + slot)).1,value⟩
        (descend start combined (offset + slot)).2) := by
  induction slot generalizing offset values outputs before with
  | zero =>
    have same : before = start := by
      simpa only [List.take_zero,walk,Outcome.state] using (congrArg Outcome.state earlierCalls)
    subst start
    cases values with
    | nil => cases selected
    | cons first rest =>
      cases Option.some.inj selected
      simpa only [Nat.add_zero] using (Reached.snoc (Reached.refl _) Step.walk_head)
  | succ slot ih =>
    cases values with
    | nil => cases selected
    | cons first rest =>
      have count : fuel + (slot + 1) + 1 = (fuel + slot + 1) + 1 := by omega
      obtain ⟨returned,middle,called,later⟩ := bind_done _ _
        (by simpa only [count,List.take_succ_cons,walk] using earlierCalls)
      obtain ⟨tail,final,remaining,done⟩ := bind_done _ _ later
      cases done
      have child := ih remaining (by simpa only [List.getElem?_cons_succ] using selected)
      have firstStep : Reached g s r e p h m c n budget
          (.walk ((fuel + slot + 1) + 1) combined offset (first :: rest) before)
          (.walk (fuel + slot + 1) combined (offset + 1) rest middle) :=
        .snoc (.refl _) (.walk_tail called)
      simpa only [count,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using firstStep.trans child

end Workers
end MicroCFTA.SourceCurrentSharedOuterWalkPrefix
