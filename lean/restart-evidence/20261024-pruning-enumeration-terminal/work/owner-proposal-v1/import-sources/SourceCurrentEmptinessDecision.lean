import MicroCFTA.SourceCurrentEmptinessTable
import MicroCFTA.SourceEmptinessDecision

/-!
# Current guarded conservative emptiness decisions

The uncached source body checks the original free list first. Open inputs
return false without exploration. Closed inputs use the earlier proved
demand branches. Actual completed rows justify the current fixed-point
checks. Global memo lookup precedes this body and is a separate operation.
Agreement concerns completed resident values and task rows. Reordering the
source openness and membership tests does not prove equal GHC thunk demand.
-/
namespace MicroCFTA.SourceCurrentEmptinessDecision
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEmptinessTaskTrace
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Value" => InternedConstructorTemplates.Value Symbol Guard
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- A completed uncached body follows the initial free-list guard. -/
inductive Decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    Value → Native width Symbol Guard → Bool → Native width Symbol Guard → Prop where
  | isOpen (notClosed : query.free ≠ []) : Decision query before false before
  | closed (closed : query.free = []) (actual : SourceEmptinessDecision.Decision query before answer after) :
      Decision query before answer after

/-- Every open body returns false and retains the entire native state. -/
theorem open_no_work [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {query : Value} {before after : Native width Symbol Guard} {answer : Bool}
    (trace : Decision query before answer after) (notClosed : query.free ≠ []) :
    answer = false ∧ after = before := by
  cases trace with
  | isOpen => exact ⟨rfl, rfl⟩
  | closed closed => exact False.elim (notClosed closed)

/-- On closed resident inputs the completed task-row body has exactly the earlier branches. -/
theorem closed_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {query : Value} {before after : Native width Symbol Guard} {answer : Bool}
    (closed : query.free = []) :
    Decision query before answer after ↔ SourceEmptinessDecision.Decision query before answer after := by
  constructor
  · intro trace
    cases trace with
    | isOpen notClosed => exact False.elim (notClosed closed)
    | closed _ actual => exact actual
  · exact .closed closed

/-- EmptyNode returns true without task exploration or native work. -/
theorem empty [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (before : Native width Symbol Guard) : Decision .empty before true before :=
  .closed rfl .empty

/-- Literal current fixed-point receipts construct the actual closed present-key branch. -/
theorem known [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {query : Value} {before : Native width Symbol Guard} {known : Int → Bool}
    (nonempty : query ≠ .empty) (closed : query.free = [])
    (trace : Run top conjoin budget [] [SourceEmptinessTasks.Task.value query]
      (SourceEmptinessTasks.start before) entries after)
    (ready : IdleReady top conjoin before)
    (encoded : encode query = .resident identity flag)
    (present : ConservativeEmptinessExplore.lookup identity (table after entries) = some rows)
    (done : SourceCurrentEmptinessTable.grow (table after entries) fuel (fun _ => false) = some known)
    (answer : result = !SourceCurrentEmptinessTable.canAccept (table after entries) known (encode query)) :
    Decision query before result after.native := by
  have rowsClosed := SourceCurrentEmptinessTable.table_closed trace (SourceEmptinessTasks.start_ready before ready)
  rw [SourceCurrentEmptinessTable.grow_eq _ rowsClosed] at done
  rw [SourceCurrentEmptinessTable.canAccept_eq _ _ _ (SourceCurrentEmptinessTable.encode_closed query closed)] at answer
  exact .closed closed (.known nonempty trace encoded present done answer)

/-- Completed closed exploration supplies a current body decision. -/
theorem explored [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {query : Value} {before : Native width Symbol Guard}
    (nonempty : query ≠ .empty)
    (trace : Run top conjoin budget [] [SourceEmptinessTasks.Task.value query]
      (SourceEmptinessTasks.start before) entries after)
    (available : Available before.machine.heap query) (closed : query.free = []) :
    ∃ answer, Decision query before answer after.native := by
  obtain ⟨answer, actual⟩ := SourceEmptinessDecision.explored nonempty trace available closed
  exact ⟨answer, .closed closed actual⟩

/-- All body branches preserve the actual native invariant and normalized fields. -/
theorem effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {query : Value} {before after : Native width Symbol Guard} {answer : Bool}
    (trace : Decision query before answer after) (ready : IdleReady top conjoin before)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap) :
    IdleReady top conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      SourceEqualityNativeDemandFieldHeap.Heap after.machine.heap := by
  cases trace with
  | isOpen => exact ⟨ready, pure_keeps _ ready.semantic.ready, fields⟩
  | closed _ actual => exact SourceEmptinessDecision.effects actual ready fields

/-- A current true result excludes every term; input closedness is derived from the guard. -/
theorem sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
    {query : Value} {before after : Native width Symbol Guard}
    (trace : Decision query before true after) (ready : IdleReady top conjoin before)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap before.machine.heap)
    (available : Available before.machine.heap query) :
    ∀ term, ¬meaning (SourceEqualityPCSGuard.holds formulas solver) ambient query term := by
  cases trace with
  | closed closed actual => exact SourceEmptinessDecision.sound formulas solver ambient actual ready fields available closed

end MicroCFTA.SourceCurrentEmptinessDecision
