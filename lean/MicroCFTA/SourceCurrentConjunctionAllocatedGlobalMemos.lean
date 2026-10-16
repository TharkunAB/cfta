import MicroCFTA.SourceCurrentConjunctionAllocatedScanSoundness
import MicroCFTA.SourceCurrentConjunctionClassScanGlobalMemos

/-!
# Current allocated Scan with all completed memo families

The actual allocation history and live precheck derive the initial checked
state and its cold native inventory laws. The same finite Scan derives all
three returned global gate tables and the fourth conjunction memo invariant.
Original-class refutation and the final input inventory use that same Scan.
Initial global table validity and reached machine ranges remain explicit.
-/
namespace MicroCFTA.SourceCurrentConjunctionAllocatedGlobalMemos
open Cache Language EqualityNormalize SourceEqualityClassOrder
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Ready Scan)
open SourceCurrentAllocatedNativeInventoryState (At)
open SourceCurrentConjunctionAllocatedClassEntry (prefixState)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Stored" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "initialOperations" => SourceEqualityConstraintMemoAllocation.initial
local notation "precheck" => SourceEqualityPartialPrecheckAllocation.run
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {initialCache finalCache : Cache.State Key} {originals : List Guard}

/-- Original allocation and the actual live precheck construct one finite fully memoized current Scan. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (memo : Memo) (correct : SourceCurrentEmptinessMemo.Correct formulas solver heap memo)
    (memos : Memos) (globals : Valid heap memos) :
    ∃ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
      SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
      SourceEqualityConstraintAllocation.Ready finalCache loaded.stored ∧
      ∀ inherited : Stored, SourceEqualityConstraintAllocation.Ready finalCache inherited →
        ∀ output : List Record,
          (precheck loaded.stored loaded.guard inherited (initialOperations finalCache)).1 = .ok (.classes output) →
          SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches edge.children
            (output.map Record.paths) (prefixState width heap loaded inherited finalCache) memo →
          ∃ outcome selected after saved next final,
            ∃ actual : Scan budget unconstrained reaches edge.children (output.map Record.paths)
              (prefixState width heap loaded inherited finalCache) memo outcome selected after saved,
            SourceCurrentConjunctionClassScanGlobalMemos.ScanReads actual memos final ∧
            Valid after.native.machine.heap final ∧ Ready after ∧ At formulas solver next after ∧
            Effects (physical (prefixState width heap loaded inherited finalCache)) (physical after) ∧
            Values after.native.machine.heap edge.children ∧
            SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
            SourceCurrentEmptinessMemo.Extends memo saved ∧
            (∀ rejected, outcome = some rejected → rejected ∈ output.map Record.paths ∧
              ∀ ambient symbol terms,
                All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
                  edge.children terms → ¬ClassSat (.node symbol terms) rejected) := by
  obtain ⟨loaded, found, readback, storedReady, live⟩ :=
    SourceCurrentConjunctionAllocatedClassEntry.entry width history valid expression covered value heap built edge resident
  have initialFields := SourceCurrentClassHistoryEntry.constructed width history valid expression covered value heap built
  have available := (initialFields.2.2.2.2.2.2 edge resident).1
  refine ⟨loaded, found, readback, storedReady, ?_⟩
  intro inherited inheritedReady output done ranges
  have checked := live inherited inheritedReady output done
  have initialAdmission := SourceCurrentConjunctionAllocatedScanSoundness.prefix_admitted width heap
    checked.1.good.native.machine.1 loaded inherited finalCache formulas solver
  have active : ∀ paths ∈ output.map Record.paths, Nontrivial paths := by
    obtain ⟨records, own, originalClasses, order, recordsValid⟩ := checked.2.2.2.2
    intro paths member
    obtain ⟨record, present, rfl⟩ := List.mem_map.mp member
    exact (recordsValid record present).2.2
  obtain ⟨outcome, selected, after, saved, actual, _⟩ :=
    SourceCurrentConjunctionClassScanCompletion.finite formulas solver budget unconstrained reaches edge.children
      (output.map Record.paths) (prefixState width heap loaded inherited finalCache) memo checked.1 available
      checked.2.2.2.1 correct ranges
  obtain ⟨final, next, reads, finalValid, finalReady, finalAdmission, effects, finalValues, finalCorrect, retained, sound⟩ :=
    SourceCurrentConjunctionClassScanGlobalMemos.verified formulas solver _ actual checked.1 initialAdmission available
      checked.2.2.2.1 active correct ranges memos globals
  refine ⟨outcome, selected, after, saved, next, final, actual, reads, finalValid, finalReady, finalAdmission,
    effects, finalValues, finalCorrect, retained, ?_⟩
  intro rejected stopped
  have member : rejected ∈ output.map Record.paths := by
    subst outcome
    exact SourceCurrentConjunctionClassScan.stopped_member actual
  exact ⟨member, sound rejected stopped⟩

end MicroCFTA.SourceCurrentConjunctionAllocatedGlobalMemos
