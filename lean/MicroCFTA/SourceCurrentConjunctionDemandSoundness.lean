import MicroCFTA.SourceCurrentConjunctionDemandExecution
import MicroCFTA.SourceCurrentConjunctionRowsSoundness
import MicroCFTA.SourceCurrentConjunctionTuplePullCoverage
import MicroCFTA.SourceCurrentConjunctionTuplePullClosedSample

/-!
# Conservative coverage from actual demand admission

Sampling derives readiness, resident tuples, and closed tuple children.
Zero admission excludes a common accepted term. Positive admission uses the
actual sampled accepting tuple and its ordered allocation to derive a stored
row with smaller accepted requirements. No eager row graph is assumed.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandExecution
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentConjunctionRowsAllocation (Ready Effects RowsReady)
open SourceCurrentConjunctionRowsWorker (Outcome)
open InternedGuardedLanguage (meaning)

section PhysicalProofs
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem sample_verified {h budget : Nat} {nodes : List Node} {before after : Physical}
    {result : SourceCurrentConjunctionTuplePullTotal.Result Symbol Formula}
    (actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before = .done result after)
    (ready : Ready before) (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    Effects before after ∧
      SourceCurrentConjunctionTuplePullDriveEffects.StatusInputs after.heap result.toStatus ∧
      SourceCurrentConjunctionTuplePullClosedSample.ResultClosed result := by
  obtain ⟨steps, observed⟩ := SourceCurrentConjunctionTuplePullTotal.sample_observation h budget nodes before
  have done := observed 0
  simp only [Nat.add_zero, actual, SourceCurrentConjunctionTuplePullTotal.observe] at done
  have physical := SourceCurrentConjunctionTuplePullDriveEffects.sample_effects
    steps h budget nodes before ready available
  have effects : Effects before after := by simpa only [done, Outcome.state] using physical.1
  exact ⟨effects, physical.2 result.toStatus after done,
    (SourceCurrentConjunctionTuplePullClosedSample.sample_closed h budget nodes before ready available closed).2
      result after actual⟩

/-- Every actual admission derives effects and readiness of its returned requirements. -/
theorem Admission.verified {budget : Nat} {nodes : List Node} {before after : Physical}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : Admission budget nodes before result after) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    Effects before after ∧ (match result with | .positive _ rows => RowsReady after rows | _ => True) := by
  cases actual with
  | overflow sampled => exact ⟨(sample_verified sampled ready available closed).1, trivial⟩
  | zero sampled => exact ⟨(sample_verified sampled ready available closed).1, trivial⟩
  | positive sampled allocated =>
      have own := sample_verified sampled ready available closed
      have later := SourceCurrentConjunctionRowsSoundness.tuples_verified allocated own.1.ready own.2.1 own.2.2
      exact ⟨own.1.trans later.1, later.2⟩

/-- Actual sampling and reached allocation preserve the full physical invariants. -/
theorem Admission.effects {budget : Nat} {nodes : List Node} {before after : Physical}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : Admission budget nodes before result after) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) : Effects before after :=
  (actual.verified ready available closed).1
end PhysicalProofs

section ActualMeaning
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Fitting demand admission covers common terms through its actual retained requirement rows. -/
theorem Admission.coverage {budget : Nat} {nodes : List Node} {before after : Physical}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol FullSyntax.Formula}
    (actual : Admission budget nodes before result after) (ready : Ready before)
    (available : Values before.heap nodes) (closed : ClosedValues nodes)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    match result with
    | .overflow => True
    | .zero => SourceCurrentConjunctionRowsSoundness.Coverage
        (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) nodes []
    | .positive _ rows => SourceCurrentConjunctionRowsSoundness.Coverage
        (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) nodes rows := by
  cases actual with
  | overflow sampled => trivial
  | zero sampled =>
      intro term accepted
      obtain ⟨tuple, member, _⟩ := SourceCurrentConjunctionTuplePullCoverage.sample_fit
        formulas solver ambient term _ _ _ _ _ [] sampled ready available closed accepted
      cases member
  | positive sampled allocated =>
      intro term accepted
      obtain ⟨tuple, member, nonempty, _resident, common⟩ := SourceCurrentConjunctionTuplePullCoverage.sample_fit
        formulas solver ambient term _ _ _ _ _ _ sampled ready available closed accepted
      have own := sample_verified sampled ready available closed
      exact SourceCurrentConjunctionRowsSoundness.tuples_witness allocated own.1.ready own.2.1 own.2.2
        tuple member nonempty formulas solver ambient term common
end ActualMeaning
end MicroCFTA.SourceCurrentConjunctionDemandExecution
