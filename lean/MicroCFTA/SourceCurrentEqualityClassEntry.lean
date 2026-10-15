import MicroCFTA.SourceEqualityLazyClassEntry
import MicroCFTA.SourceCurrentEqualityClassScanSoundness

/-!
# Current memoized class scans at the ordered source entry

The unchanged precheck derives the ordered active class list from coherent
original records and actual equality-accessor readback. A stopped current
scan refutes that accessor. The scan uses the current secondary gate and
actual fourth-memo calls. Physical record extraction and initial native
construction remain explicit source boundaries.
-/
namespace MicroCFTA.SourceCurrentEqualityClassEntry
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityClassOrder SourceEqualityRequiredCache SourceEqualityNativeScoped
open SourceCurrentEqualityClassScan
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap

/-- A stopped actual scan refutes the original accessor payload after deriving its exact ordered active entry. -/
theorem stopped_refutes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (constraint : Guard) (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (records : List Record) (coherent : ∀ record ∈ records, Coherent record)
    (readback : SourceCompactGuards.sourceEqualities constraint = some (records.map Record.paths))
    (inherited : SourceEqualityPrecheck.Constraint) (output : List Record)
    (live : SourceEqualityPrecheck.precheck (some records) inherited = .ok (.classes output))
    {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {selected : Constraints} {paths : Class}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {memo saved : SourceCurrentEmptinessMemo.Memo}
    (trace : Scan unconstrained reaches values (output.map Record.paths) before memo (some paths) selected after saved)
    (ready : IdleReady top conjoin before) (available : Values before.machine.heap values)
    (costs : CostHeap before.machine.heap) (fields : FieldHeap before.machine.heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.machine.heap memo)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) :
    ¬SourceEqualityGuardReadback.Sat (.node symbol terms) (SourceCompactGuards.sourceEqualities constraint) := by
  have entry := SourceEqualityLazyClassEntry.live_entry constraint cached records coherent readback inherited output live
  have excluded := SourceCurrentEqualityClassScanSoundness.stopped_refutes trace ready available costs fields entry.2.2.1
    formulas solver correct ambient symbol terms accepted
  exact fun satisfied => excluded ((entry.2.2.2 (.node symbol terms)).mpr satisfied)

end MicroCFTA.SourceCurrentEqualityClassEntry
