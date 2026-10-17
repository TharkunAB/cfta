import MicroCFTA.SourceCurrentConjunctionWorklistResources
import MicroCFTA.SourceCurrentConjunctionGuard

/-!
# Initial numeric current conjunction decisions and memo calls

The original heap supplies its own finite guard carrier. The admission
budget and scalar fix both shared worker ceilings and the final heap
forecast. Hits retain the exact state. Misses construct their own decision.
-/
namespace MicroCFTA.SourceCurrentConjunctionNumeric
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorklist (closed)
open SourceCurrentConjunctionWorklistResources (forecast workerFuel readerFuel)
open SourceCurrentConjunctionGuardUniverse (guards)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Both actual decision branches fit the original forecast and computed literal worker ceilings. -/
theorem decision_bound {budget : Nat} {start : Value Symbol Guard} {before after : Physical} {answer : Bool}
    (actual : SourceCurrentConjunctionDecision.Decision budget start before answer after)
    (resource : Nat) (ready : Ready before) (available : Available before.heap start) (fits : Fits resource before.heap) :
    Fits (forecast (guards before.heap) budget resource) after.heap ∧
      (∀ work reader, workerFuel (guards before.heap) budget resource ≤ work →
        readerFuel (guards before.heap) budget resource ≤ reader →
        SourceCurrentConjunctionWorker.decision work reader budget start before = .done answer after) := by
  cases actual with
  | open_input openInput =>
      exact ⟨fits.mono (SourceCurrentConjunctionWorklistResources.forecast_ge _ _ _),
        by intros; simp only [SourceCurrentConjunctionWorker.decision, openInput, Bool.false_eq_true, ite_false]⟩
  | closed admitted explored grown =>
      have inputs : SourceCurrentConjunctionWorklist.PendingReady before [[start]] := by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available
      have widths : ∀ nodes ∈ [[start]], nodes.length ≤ resource := by
        intro nodes member
        cases List.mem_singleton.mp member
        exact fits.stored.positive
      have numeric := SourceCurrentConjunctionWorklistResources.bound explored (guards before.heap) resource
        ready inputs fits widths (SourceCurrentConjunctionGuardUniverse.initial before.heap ready.semantic.ready.semantic.1.normal.facts)
      refine ⟨numeric.1, ?_⟩
      intro work reader enoughWork enoughRead
      simp only [SourceCurrentConjunctionWorker.decision, admitted, ite_true,
        numeric.2 work reader enoughWork enoughRead, SourceCurrentConjunctionWorker.Outcome.bind, grown]

/-- Initial physical facts construct their own complete numeric decision without a future execution premise. -/
theorem decision_complete (budget : Nat) (start : Value Symbol Guard) (before : Physical)
    (resource : Nat) (ready : Ready before) (available : Available before.heap start) (fits : Fits resource before.heap) :
    ∃ answer after, SourceCurrentConjunctionDecision.Decision budget start before answer after ∧
      Effects before after ∧ Fits (forecast (guards before.heap) budget resource) after.heap ∧
      (∀ work reader, workerFuel (guards before.heap) budget resource ≤ work →
        readerFuel (guards before.heap) budget resource ≤ reader →
        SourceCurrentConjunctionWorker.decision work reader budget start before = .done answer after) := by
  obtain ⟨answer, after, actual, effects⟩ := SourceCurrentConjunctionDecision.complete budget start before ready available
  have numeric := decision_bound actual resource ready available fits
  exact ⟨answer, after, actual, effects, numeric⟩

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteValue" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsAllocation.State ConcreteSymbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

section Concrete
variable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
  [DecidableEq ConcreteValue]

/-- The exact actual hit or miss retains the original numeric forecast and common worker replay. -/
theorem call_bound {budget : Nat} {memo saved : Memo} {query : ConcreteValue}
    {before after : ConcretePhysical} {answer : Bool}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query before answer after saved)
    (resource : Nat) (ready : Ready before) (available : Available before.heap query) (fits : Fits resource before.heap) :
    Fits (forecast (guards before.heap) budget resource) after.heap ∧
      (∀ work reader, workerFuel (guards before.heap) budget resource ≤ work →
        readerFuel (guards before.heap) budget resource ≤ reader →
        SourceCurrentConjunctionWorker.call work reader budget memo query before = .done (answer, saved) after) := by
  cases actual with
  | hit found =>
      exact ⟨fits.mono (SourceCurrentConjunctionWorklistResources.forecast_ge _ _ _),
        by intros; simp only [SourceCurrentConjunctionWorker.call, found]⟩
  | miss absent actual =>
      have numeric := decision_bound actual resource ready available fits
      exact ⟨numeric.1, by
        intro work reader enoughWork enoughRead
        simp only [SourceCurrentConjunctionWorker.call, absent, numeric.2 work reader enoughWork enoughRead,
          SourceCurrentConjunctionWorker.Outcome.bind]⟩

/-- Initial memo correctness constructs the complete numeric call with the same semantic and physical return. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (memo : Memo) (query : ConcreteValue) (before : ConcretePhysical)
    (resource : Nat) (ready : Ready before) (available : Available before.heap query) (fits : Fits resource before.heap)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.heap memo)
    (annotation : ConcreteGuard → Prop) (known : SourceCurrentConstrainedCapGuardHeap.Heap annotation before.heap) :
    ∃ answer after saved, SourceCurrentConjunctionMemo.Call budget memo query before answer after saved ∧
      Effects before after ∧ SourceCurrentEmptinessMemo.Correct formulas solver after.heap saved ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧ SourceCurrentEmptinessMemo.Extends memo saved ∧
      SourceCurrentConstrainedCapGuardHeap.Heap annotation after.heap ∧
      Fits (forecast (guards before.heap) budget resource) after.heap ∧
      (∀ work reader, workerFuel (guards before.heap) budget resource ≤ work →
        readerFuel (guards before.heap) budget resource ≤ reader →
        SourceCurrentConjunctionWorker.call work reader budget memo query before = .done (answer, saved) after) := by
  obtain ⟨answer, after, saved, actual, effects, finalCorrect, sound, retained⟩ :=
    SourceCurrentConjunctionMemo.finite formulas solver budget memo query before ready available correct
  have numeric := call_bound actual resource ready available fits
  exact ⟨answer, after, saved, actual, effects, finalCorrect, sound, retained,
    SourceCurrentConjunctionGuard.call annotation actual ready available known, numeric⟩

end Concrete
end MicroCFTA.SourceCurrentConjunctionNumeric
