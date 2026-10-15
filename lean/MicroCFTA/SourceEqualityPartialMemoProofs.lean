import MicroCFTA.SourceEqualityPartialMemoCases

/-!
# Complete recursive source memo receipts from actual physical scopes

Mutual graph induction derives both source memo tables at every reached
warm native prefix. The actual completed child effects supply every later
scope. No cost heap, original gate history, or recursive memo law is assumed.
-/
namespace MicroCFTA.SourceEqualityPartialMemoProofs
open InternedConstructorTemplates InternedProbeProvenance SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityPartialScope
open SourceEqualityPartialGraph SourceEqualityPartialMemoGraph SourceEqualityPartialMemoCases
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Every completed recursive node graph derives both actual gate memo tables at all reached closed warm prefixes. -/
theorem node (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    {inherited value result} {before after : NativeState width Symbol Guard}
    (trace : ReduceNode inherited value before result after) : NodeMemos trace := by
  exact ReduceNode.rec
    (motive_1 := fun _ _ _ _ _ trace => NodeMemos trace)
    (motive_2 := fun _ _ _ _ _ trace => RowsMemos trace)
    (motive_3 := fun _ _ _ _ _ trace => ChildrenMemos trace)
    (motive_4 := fun _ _ _ _ _ _ trace => WalkMemos trace)
    (fun {_ _} _ _ _ => .empty)
    (fun {_ _ _ _ _ _} _ _ _ => .union)
    (fun {_ _ _ _ _ _ _ _} actual _ _ _ => .binder actual)
    (fun {_ _ _ _ _ _ _ _} _ ih => ordinary ih)
    (fun {_ _} _ _ _ => .nil)
    (fun {_ _ _ _ _ _ _ _ _ _ _ _} narrowed physical combined children rest childIH restIH =>
      rows_cons formulas solver ambient narrowed physical combined children rest childIH restIH)
    (fun {_ _} _ _ _ => .contradiction)
    (fun {_ _ _ _ _} _ ih scope available closed => .live (ih scope available closed))
    (fun {_ _ _} _ _ _ => .nil)
    (fun {_ _ _ _ _ _ _ _ _} head tail headIH tailIH => walk_cons formulas solver ambient head tail headIH tailIH) trace

/-- Actual checked bounded success supplies the complete recursive graph and both real source gate memo receipts. -/
theorem checked (g e p h c n fuel : Nat)
    {inherited value result} {before after : NativeState width Symbol Guard}
    (plan : SourceEqualityPartialChecks.Checked g e p h c n fuel inherited value before)
    (done : SourceEqualityPartialWorker.run g e p h c n fuel inherited value before = .done (.ok result) after)
    (scope : Scope before) (available : Available before.machine.heap value) (closed : value.free = [])
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    ∃ trace : ReduceNode inherited value before result after, NodeReads trace := by
  let trace := SourceEqualityPartialWorkerGraph.graph g e p h c n fuel plan done
  exact ⟨trace, node formulas solver ambient trace scope available closed⟩

end MicroCFTA.SourceEqualityPartialMemoProofs
