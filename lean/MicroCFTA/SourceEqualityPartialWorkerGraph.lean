import MicroCFTA.SourceEqualityPartialLiftRows

/-!
# Successful bounded recursive execution derives its complete graph

Traversal-bound induction supplies each actual smaller child graph. The
reached plan checks the native prefix at its real warm state. No global
callback law, binder law, or completed outer graph is an input premise.
Errors and incomplete observations cannot satisfy the successful receipt.
-/
namespace MicroCFTA.SourceEqualityPartialWorkerGraph
open Cache InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityPartialGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual checked bounded success supplies every recursive graph receipt by traversal induction. -/
theorem graph {width : Nat} (g e p h c n fuel : Nat)
    {inherited : SourceEqualityPrecheck.Constraint} {value result : Value Symbol Guard}
    {before after : NativeState width Symbol Guard}
    (plan : SourceEqualityPartialChecks.Checked g e p h c n fuel inherited value before)
    (done : SourceEqualityPartialWorker.run g e p h c n fuel inherited value before = .done (.ok result) after) :
    ReduceNode inherited value before result after := by
  induction fuel generalizing inherited value before result after with
  | zero => cases done
  | succ fuel ih =>
      cases value with
      | empty => cases done; exact .empty
      | reference => cases done
      | union => cases done; exact .union
      | mu entry body depth ordinary =>
          cases actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.machine.heap with
          | pending => simp only [SourceEqualityPartialWorker.run, SourceEqualityPartialWorker.step, actual] at done; cases done
          | done built heap =>
              simp only [SourceEqualityPartialWorker.run, SourceEqualityPartialWorker.step, actual,
                SourceEqualityInheritedChildren.Result.done.injEq, Except.ok.injEq] at done
              rcases done with ⟨rfl, rfl⟩
              exact .binder actual
      | node entry edges depth free =>
          cases actual : SourceEqualityInheritedRows.walk (SourceEqualityPartialWorker.run g e p h c n fuel)
              g e p h c n inherited edges before with
          | incomplete => simp only [SourceEqualityPartialWorker.run, SourceEqualityPartialWorker.step, actual] at done; cases done
          | done answer middle =>
              cases answer with
              | error => simp only [SourceEqualityPartialWorker.run, SourceEqualityPartialWorker.step, actual] at done; cases done
              | ok results =>
                  simp only [SourceEqualityPartialWorker.run, SourceEqualityPartialWorker.step, actual,
                    SourceEqualityInheritedChildren.Result.done.injEq, Except.ok.injEq] at done
                  rcases done with ⟨rfl, rfl⟩
                  exact .ordinary (SourceEqualityPartialLiftRows.rows
                    (fun _ _ _ _ _ checked receipt => ih checked receipt) g e p h c n plan actual)

/-- Any two checked successful bounds return the identical value and full native state. -/
theorem unique {width : Nat} (g e p h c n fuel gg ee pp hh cc nn more : Nat)
    {inherited : SourceEqualityPrecheck.Constraint} {value first second : Value Symbol Guard}
    {before firstState secondState : NativeState width Symbol Guard}
    (firstPlan : SourceEqualityPartialChecks.Checked g e p h c n fuel inherited value before)
    (firstDone : SourceEqualityPartialWorker.run g e p h c n fuel inherited value before = .done (.ok first) firstState)
    (secondPlan : SourceEqualityPartialChecks.Checked gg ee pp hh cc nn more inherited value before)
    (secondDone : SourceEqualityPartialWorker.run gg ee pp hh cc nn more inherited value before = .done (.ok second) secondState) :
    first = second ∧ firstState = secondState :=
  SourceEqualityPartialGraphExecution.node_unique (graph g e p h c n fuel firstPlan firstDone)
    (graph gg ee pp hh cc nn more secondPlan secondDone)

end MicroCFTA.SourceEqualityPartialWorkerGraph
