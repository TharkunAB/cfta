import MicroCFTA.SourceClosedSelfRequireBoundary
import MicroCFTA.MergedFreshOrdinaryExposureLanguage
import MicroCFTA.InternedGuardedExecution

/-!
# Constructor-row exposure removes the closed self-binder stutter

The source path repair uses `Node (nodeEdges node)` before it traverses a
recursive node. The existing cold reader uses a visited set. For the raw
self binder it returns no rows. Rebuilding those rows returns empty without
changing the cache. Independent least-language semantics also returns empty.
The old stutter witness remains in its original module.
-/
namespace MicroCFTA.SourceClosedSelfHeadRepair
open InternedConstructorTemplates InternedNestedConstruction
open SourceClosedSelfRequireBoundary (expression)

/-- Observe the exact cold read and the source `Node []` constructor request. -/
def Repaired : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending _ _ => False
  | .done value state =>
      MergedFreshOrdinaryExposure.nodeEdges 2 value state = .done [] state ∧
      work (makeNode ([] : List (EdgeValue Nat Unit))) state = .done .empty state

/-- Two visited-worklist steps resolve the retained raw cycle without allocation. -/
theorem actual_head : Repaired (InternedFreshOrdinaryConstruction.build expression [] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in
    cbv

/-- The raw self binder has no finite constructor term in its independent language. -/
theorem syntax_empty (holds : Unit → Language.Term Nat → Bool) (term : Language.Term Nat) :
    ¬ InternedGuardedSyntax.evaluate holds [] expression term := by
  rw [expression, InternedGuardedSyntax.evaluate]
  intro accepted
  apply accepted (fun _ => False)
  intro value impossible
  simp only [InternedGuardedSyntax.evaluate, List.getElem?_cons_zero, Option.getD_some] at impossible

/-- Replacing this actual source binder by empty preserves its complete least language. -/
theorem actual_language (value : Value Nat Unit) (state : State Nat Unit)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state)
    (holds : Unit → Language.Term Nat → Bool) (ambient : InternedGuardedLanguage.Env Nat) :
    InternedGuardedLanguage.meaning holds ambient value =
      InternedGuardedLanguage.meaning holds ambient (.empty : Value Nat Unit) := by
  rw [InternedGuardedExecution.closed_language expression value state built holds ambient]
  funext term
  apply propext
  rw [InternedGuardedLanguage.meaning]
  exact ⟨fun accepted => False.elim (syntax_empty holds term accepted), False.elim⟩

end MicroCFTA.SourceClosedSelfHeadRepair
