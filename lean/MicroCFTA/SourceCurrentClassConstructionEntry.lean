import MicroCFTA.SourceCurrentClassInitial
import MicroCFTA.SourceCurrentClassAllocatedEntry
import MicroCFTA.SourceEqualityAnnotationHeap

/-!
# Current cold scan after original construction and allocated precheck

Original source construction derives the initial native and field
invariants. A resident original edge supplies its own available children
and normalized stored constraint. The actual read-only field lookup and
allocated precheck derive the physical entry. The reached current scan
then derives all four completed global memo invariants.

This theorem starts the global gate tables and Boolean memo empty at a
cold scope. It does not reset a warm caller. Existing equality-interner
coverage, inherited storage, and completed scan execution remain explicit.
-/
namespace MicroCFTA.SourceCurrentClassConstructionEntry
open Cache Language EqualityNormalize SourceEqualityClassOrder
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityNativeInitial
open SourceCurrentEqualityClassScan SourceCurrentClassScanGlobalMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Stored" => SourceEqualityConstraintAllocation.Value
local notation "prefix" => SourceEqualityPartialPrecheckAllocation.run

/-- Actual source construction and allocated entry derive every initial invariant for the reached cold scan. -/
theorem cold_scan_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
    (operations : Operations) (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (loaded : Allocated)
    (found : SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint operations.constraints = .ok (some loaded))
    (inherited : Stored) (inheritedReady : SourceEqualityConstraintAllocation.Ready operations.constraints inherited)
    (output : List Record) (done : (prefix loaded.stored loaded.guard inherited operations).1 = .ok (.classes output))
    {selected : Constraints} {outcome : Option Class} {after : Native width Symbol Guard} {saved : Memo}
    (trace : Scan source reaches edge.children (output.map Record.paths) (cold width heap)
      SourceCurrentEmptinessMemo.empty outcome selected after saved)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceEqualityConstraintMemoAllocation.Valid (prefix loaded.stored loaded.guard inherited operations).2 ∧
      SourceEqualityConstraintMemoAllocation.Grows operations (prefix loaded.stored loaded.guard inherited operations).2 ∧
      ∃ final, ScanReads trace EndpointMemoGateTrace.empty final ∧ Valid after.machine.heap final ∧
        IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
        Keeps heap after.machine.heap ∧ Values after.machine.heap edge.children ∧
        SourceCurrentEmptinessMemo.Correct formulas solver after.machine.heap saved ∧
        SourceCurrentEmptinessMemo.Extends SourceCurrentEmptinessMemo.empty saved := by
  obtain ⟨ready, costs, fields, _, _, edges⟩ :=
    SourceCurrentClassInitial.constructed width expression allowed value heap built
  have inputs := edges edge resident
  exact SourceCurrentClassAllocatedEntry.scan_memos edge.entry.key.constraint inputs.2 operations operationsValid
    loaded found inherited inheritedReady output done trace ready inputs.1 costs fields formulas solver
      (SourceCurrentEmptinessMemo.empty_correct formulas solver heap)
      EndpointMemoGateTrace.empty (EndpointMemoGateTrace.empty_valid heap)

/-- A public accepted original edge cannot reach rejection through the actual cold allocated entry. -/
theorem cold_scan_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (allowed : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
    (operations : Operations) (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (loaded : Allocated)
    (found : SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint operations.constraints = .ok (some loaded))
    (inherited : Stored) (inheritedReady : SourceEqualityConstraintAllocation.Ready operations.constraints inherited)
    (output : List Record) (done : (prefix loaded.stored loaded.guard inherited operations).1 = .ok (.classes output))
    {selected : Constraints} {outcome : Option Class} {after : Native width Symbol Guard} {saved : Memo}
    (trace : Scan source reaches edge.children (output.map Record.paths) (cold width heap)
      SourceCurrentEmptinessMemo.empty outcome selected after saved)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : InternedGuardedLanguage.edgeMeaning (SourceSymbolicIndex.acceptsConstraint formulas solver) ambient edge term) :
    outcome = none := by
  obtain ⟨ready, costs, fields, _, _, edges⟩ :=
    SourceCurrentClassInitial.constructed width expression allowed value heap built
  have checked := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using checked.facts
  have annotations := SourceEqualityAnnotationHeap.edge
    (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) heap fields facts edge resident
  have same := SourceEqualityAnnotationLanguage.edge_public_eq formulas solver edge annotations.1 annotations.2 ambient
  have acceptedPCS : InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term := by
    rw [same]
    exact accepted
  obtain ⟨live, _, _⟩ := SourceCurrentClassAllocatedEntry.prefix_entry edge.entry.key.constraint annotations.1
    operations operationsValid loaded found inherited inheritedReady output done
  obtain ⟨records, _, readback, _, order, _⟩ := SourceEqualityPhysicalClassEntry.live_records
    edge.entry.key.constraint annotations.1 inherited.payload output live
  have active := SourceEqualityPhysicalClassEntry.live_active edge.entry.key.constraint annotations.1 inherited.payload output live
  cases edge with
  | mk entry children =>
      change SourceCompactGuards.sourceEqualities entry.key.constraint = some (records.map Record.paths) at readback
      simp only [InternedGuardedLanguage.edgeMeaning] at acceptedPCS
      obtain ⟨terms, rfl, forest, guardAccepted⟩ := acceptedPCS
      have originalAccepted : SourceSymbolicIndex.acceptsConstraint formulas solver entry.key.constraint
          (.node entry.key.symbol terms) = true := by
        rwa [SourceEqualityPCSGuard.public_eq formulas solver entry.key.constraint
          (SourceEqualityGuardReadback.active annotations.1) (.node entry.key.symbol terms)] at guardAccepted
      have originalSat := SourceEqualityGuardReadback.accepted_sat formulas solver entry.key.constraint
        (SourceEqualityGuardReadback.active annotations.1) (.node entry.key.symbol terms) originalAccepted
      have satisfied : Satisfies (.node entry.key.symbol terms) (output.map Record.paths) := by
        rw [readback] at originalSat
        change Satisfies (.node entry.key.symbol terms) (records.map Record.paths) at originalSat
        rw [order]
        intro paths member
        exact originalSat paths (((ordered_perm records).map Record.paths).mem_iff.mp member)
      exact (SourceCurrentEqualityClassScanSoundness.verified trace ready (edges _ resident).1 costs fields active
        formulas solver (SourceCurrentEmptinessMemo.empty_correct formulas solver heap) ambient entry.key.symbol terms
        ((InternedGuardedLanguage.forest_all _ _ _ _).mp forest) satisfied).1

end MicroCFTA.SourceCurrentClassConstructionEntry
