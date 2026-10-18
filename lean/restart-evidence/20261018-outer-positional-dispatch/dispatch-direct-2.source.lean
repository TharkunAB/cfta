import MicroCFTA.SourceCurrentOuterExecutionAncestry
import MicroCFTA.SourceCurrentPositionalOriginChain

/-!
# Indexed literal outer dispatch and positional anchors

The completed walk supplies the exact earlier calls, inherited descent,
node dispatch, and suffix. No execution graph or future link is supplied.
Positional origin composition uses the returned Parent children as the
actual dispatched values. It does not identify every worker dispatch with
a consecutive step of the conditional continuation-chain relation.
-/
namespace MicroCFTA.SourceCurrentOuterPositionalDispatch
open Cache InternedConstructorTemplates InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached Step)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
variable {width : Nat}

private theorem bind_done {A B : Type} (first : Outcome A width)
    (next : A → Caller width → Outcome B width) {result : B} {after : Caller width}
    (actual : first.bind next = .done result after) :
    ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value middle => exact ⟨value,middle,rfl,actual⟩
  | failed => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Every present walk input has an exact indexed node call, literal prefix, and returned suffix. -/
theorem walk_indexed {fuel g s r e p h m c n budget : Nat} {combined : EqValue} {offset : Nat}
    {values results : List Node} {before after : Caller width}
    (actual : walk fuel g s r e p h m c n budget combined offset values before = .done results after)
    {slot : Nat} {value : Node} (input : values[slot]? = some value) :
    ∃ (start finish : Caller width) (childFuel : Nat) (returned : Node),
      fuel = childFuel + slot + 1 ∧ results[slot]? = some returned ∧
      walk fuel g s r e p h m c n budget combined offset (values.take slot) before =
        .done (results.take slot) start ∧
      nodeCall childFuel g s r e p h m c n budget
        ⟨(descend start combined (offset + slot)).1,value⟩
        (descend start combined (offset + slot)).2 = .done returned finish ∧
      walk childFuel g s r e p h m c n budget combined (offset + slot + 1)
        (values.drop (slot + 1)) finish = .done (results.drop (slot + 1)) after ∧
      Reached g s r e p h m c n budget (.walk fuel combined offset values before)
        (.node childFuel ⟨(descend start combined (offset + slot)).1,value⟩
          (descend start combined (offset + slot)).2) := by
  induction slot generalizing fuel offset values results before with
  | zero =>
    cases values with
    | nil => cases input
    | cons first rest =>
      cases fuel with
      | zero => simp only [walk] at actual; cases actual
      | succ fuel =>
        obtain ⟨returned,middle,called,later⟩ := bind_done _ _ (by simpa only [walk] using actual)
        obtain ⟨outputs,final,tail,done⟩ := bind_done _ _ later
        cases done
        cases Option.some.inj input
        refine ⟨before,middle,fuel,returned,by omega,rfl,(by simp only [List.take_zero,walk]),?_,?_,?_⟩
        · simpa only [Nat.add_zero] using called
        · simpa only [List.drop_succ_cons,List.drop_zero,Nat.add_zero] using tail
        · simpa only [Nat.add_zero] using (Reached.snoc (.refl _) Step.walk_head)
  | succ slot ih =>
    cases values with
    | nil => cases input
    | cons first rest =>
      cases fuel with
      | zero => simp only [walk] at actual; cases actual
      | succ fuel =>
        obtain ⟨returned,middle,called,later⟩ := bind_done _ _ (by simpa only [walk] using actual)
        obtain ⟨outputs,final,tail,done⟩ := bind_done _ _ later
        cases done
        obtain ⟨start,finish,childFuel,output,count,selected,earlier,child,suffix,reached⟩ :=
          ih tail input
        refine ⟨start,finish,childFuel,output,by omega,selected,?_,?_,?_,?_⟩
        · simp only [List.take_succ_cons,walk,called,Outcome.bind,earlier]
        · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using child
        · simpa only [List.drop_succ_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using suffix
        · have firstStep := Reached.snoc (Reached.refl _) (Step.walk_tail called)
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using firstStep.trans reached

end MicroCFTA.SourceCurrentOuterPositionalDispatch
