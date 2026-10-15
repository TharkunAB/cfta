import MicroCFTA.SourceEmptinessTaskRows

/-!
# Accepted task rows from actual source exposure

The actual completed edge read supplies an accepted retained source row.
Ordered capture then supplies its task row and exact suspended class bodies
in the actual returned state. No accepted-row oracle or future task result
is assumed. This uses the completed-row-read abstraction. It does not prove
source runtime demand order or GHC heap correspondence.
-/
namespace MicroCFTA.SourceEmptinessTaskExposureWitness
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityNativeScoped SourceEmptinessTasks SourceEmptinessTaskRows
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Row" => ConservativeEmptinessRows.Row (Value Symbol Guard)

/-- An ordered relation supplies the actual right-hand occurrence for each left-hand occurrence. -/
private theorem related_member {Left Right : Type} {relation : Left → Right → Prop}
    {left : List Left} {right : List Right} (related : All₂ relation left right) :
    ∀ value ∈ left, ∃ result ∈ right, relation value result := by
  induction related with
  | nil => intro value impossible; cases impossible
  | @cons first second left right head rest ih =>
      intro value member
      rcases List.mem_cons.mp member with same | later
      · subst value
        exact ⟨second, List.mem_cons_self, head⟩
      · obtain ⟨result, member, receipt⟩ := ih value later
        exact ⟨result, List.mem_cons_of_mem second member, receipt⟩

/-- Guarded input acceptance selects an actual retained task row with its exact final-state receipt. -/
theorem accepted [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {value : Value Symbol Guard} {before after : SourceEmptinessTasks.State width Symbol Guard}
    {taskRows : List (List (Task Symbol Guard))}
    (trace : Expose value before taskRows after) (ready : Ready emptyGuard conjoin before)
    (fields : SourceEqualityNativeDemandFieldHeap.Heap before.native.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (inputAccepted : meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term) :
    ∃ (sourceRow : Row) (taskRow : List (Task Symbol Guard)), taskRow ∈ taskRows ∧
      RowReceipt after sourceRow taskRow ∧ Active sourceRow.classes ∧ Satisfies term sourceRow.classes ∧
      ∃ symbol terms, term = .node symbol terms ∧
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) sourceRow.children terms := by
  cases trace with
  | read available closed actual =>
      rename_i edges heap
      have checked := actual.verified ready.native.semantic available closed
      have advanced := ready.advanceNative (advanceHeap before.native heap)
        (ready.native.advance heap checked.1 checked.2.1) checked.1
      have captured := captureRows_receipt (SourceEmptinessExposure.rows edges) _ advanced
        (rows_inputs heap checked.2.1 edges checked.2.2.1 checked.2.2.2)
      obtain ⟨edge, _, member, active, satisfied, terms, shape, forest⟩ :=
        SourceEmptinessExposure.read_witness actual ready.native.semantic fields available closed
          formulas solver ambient term inputAccepted
      obtain ⟨taskRow, selected, receipt⟩ := related_member captured (SourceEmptinessExposure.row edge) member
      exact ⟨SourceEmptinessExposure.row edge, taskRow, selected, receipt, active, satisfied,
        edge.entry.key.symbol, terms, shape, forest⟩

end MicroCFTA.SourceEmptinessTaskExposureWitness
