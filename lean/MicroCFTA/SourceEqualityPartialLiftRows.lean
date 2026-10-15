import MicroCFTA.SourceEqualityPartialLiftChildren

/-!
# Recursive ordered rows from actual bounded worker execution

Each successful local native prefix supplies its own physical payload and
child check plan. Recursive child graphs use the smaller-call premise.
The tail uses the actual state returned by literal edge construction.
-/
namespace MicroCFTA.SourceEqualityPartialLiftRows
open Cache InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityPartialGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Successful bounded rows give complete recursive graphs at their exact returned native states. -/
theorem rows {width : Nat}
    {call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → SourceEqualityPartialWorker.Result width}
    {check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Prop}
    (node : ∀ inherited value before result after, check inherited value before →
      call inherited value before = .done (.ok result) after → ReduceNode inherited value before result after)
    (g e p h c n : Nat) {inherited edges before results after}
    (plan : SourceEqualityPartialChecks.Rows call check g e p h c n inherited edges before)
    (done : SourceEqualityInheritedRows.walk call g e p h c n inherited edges before = .done (.ok results) after) :
    ReduceRows inherited edges before results after := by
  induction edges generalizing before results after with
  | nil => cases done; exact .nil
  | cons edge edges ih =>
      cases first : SourceEqualityInheritedEdgeWorker.run call g e p h c n edge inherited before with
      | guarded | children => simp only [SourceEqualityInheritedRows.walk, first] at done; cases done
      | done answer middle =>
          cases answer with
          | error => simp only [SourceEqualityInheritedRows.walk, first] at done; cases done
          | ok result =>
              cases rest : SourceEqualityInheritedRows.walk call g e p h c n inherited edges middle with
              | incomplete => simp only [SourceEqualityInheritedRows.walk, first, rest] at done; cases done
              | done answer final =>
                  cases answer with
                  | error => simp only [SourceEqualityInheritedRows.walk, first, rest] at done; cases done
                  | ok tail =>
                      simp only [SourceEqualityInheritedRows.walk, first, rest,
                        SourceEqualityInheritedRows.Result.done.injEq, Except.ok.injEq] at done
                      rcases done with ⟨rfl, rfl⟩
                      have tailTrace := ih (plan.2.2 result middle first) rest
                      cases localPass : SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top g e p h c n edge inherited before with
                      | children => simp only [SourceEqualityInheritedEdgeWorker.run, localPass] at first; cases first
                      | done answer localMiddle =>
                          cases answer with
                          | error => simp only [SourceEqualityInheritedEdgeWorker.run, localPass] at first; cases first
                          | ok narrowed =>
                              have native := SourceEqualityGuardedEdgeWorkerProofs.graph source top conjoin SourceMemoGate.plain top
                                g e p h c n edge inherited before plan.1 narrowed localMiddle localPass
                              have descendants := SourceEqualityInheritedEdgeWorker.descendants_graph
                                (by simpa only [SourceEqualityInheritedEdgeWorker.run, localPass] using first)
                              cases descendants with
                              | done physical combined childTrace =>
                                  exact .cons native physical combined
                                    (SourceEqualityPartialLiftChildren.children node childTrace
                                      (plan.2.1 _ _ localPass _ physical _ combined)) tailTrace

end MicroCFTA.SourceEqualityPartialLiftRows
