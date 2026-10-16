import MicroCFTA.SourceCurrentConjunctionAllocatedGlobalMemos

#print axioms MicroCFTA.SourceCurrentConjunctionQueryGlobalMemos.query_memos
#check @MicroCFTA.SourceCurrentConjunctionQueryGlobalMemos.QueryReads
#check @MicroCFTA.SourceCurrentConjunctionQueryGlobalMemos.query_memos

#print axioms MicroCFTA.SourceCurrentConjunctionClassScanGlobalMemos.scan_memos
#print axioms MicroCFTA.SourceCurrentConjunctionClassScanGlobalMemos.verified
#check @MicroCFTA.SourceCurrentConjunctionClassScanGlobalMemos.ScanReads
#check @MicroCFTA.SourceCurrentConjunctionClassScanGlobalMemos.scan_memos
#check @MicroCFTA.SourceCurrentConjunctionClassScanGlobalMemos.verified

#print axioms MicroCFTA.SourceCurrentConjunctionAllocatedGlobalMemos.finite
#check @MicroCFTA.SourceCurrentConjunctionAllocatedGlobalMemos.finite


namespace MicroCFTA.SourceCurrentConjunctionRootGlobalIndependentProbes
open Cache Language EqualityNormalize SourceEqualityClassOrder
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan (Scan Ready advanceHeap)
open SourceCurrentAllocatedNativeInventoryState (At Inventory)
open SourceCurrentConjunctionAllocatedClassEntry (prefixState)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Stored" => SourceEqualityConstraintAllocation.Value
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches SourceMemoGate.unconstrained
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

-- A true current call completes this prefix for any unvisited suffix, with no suffix range or receipt premise.
theorem stop_before_suffix (paths : Class) (values : List (Value Symbol Guard)) (suffix : Constraints)
    (proper : ∀ path ∈ paths, path ≠ [])
    {before middle : Checked width} {heap anchor : State Symbol Guard} {later : Physical}
    {query : Value Symbol Guard} {budget : Nat} {memo saved : Memo}
    (primary : EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths before.native.machine.heap true heap)
    (secondary : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths heap false anchor)
    (seeded : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat))
      (advanceHeap (advanceHeap before heap) anchor) query middle)
    (call : SourceCurrentConjunctionMemo.Call budget memo query (physical middle) true later saved)
    (ranges : SourceCurrentAllocatedSeededQuery.SeededRanges values (paths.map (List.map Int.ofNat))
      (advanceHeap (advanceHeap before heap) anchor))
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ final,
      SourceCurrentConjunctionClassScanGlobalMemos.ScanReads
        (Scan.stopped (classes := suffix) primary secondary seeded call) memos final ∧
      Valid later.heap final ∧ Ready (advancePhysical middle later) := by
  have first := SourceCurrentConjunctionClassScan.primary_effects unconstrained reaches primary ready available
  obtain ⟨primaryMemos, primaryRead, primaryKept⟩ := EndpointMemoGateTrace.lift_class _ _ _ _ _ primary
    (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available memos valid
  have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct
  obtain ⟨final, queryRead, finalValid, finalReady, _⟩ :=
    SourceCurrentConjunctionQueryGlobalMemos.query_memos paths values proper secondary seeded call ranges
      first.1 first.2.2 formulas solver firstCorrect primaryMemos primaryKept.valid
  exact ⟨final, .stopped primaryRead queryRead, finalValid, finalReady⟩

-- The same actual warm Scan has final global receipts and refutes all original class constraints on a stop.
theorem verified_stop (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    {budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints} {outcome : Option Class}
    {before after : Checked width} {memo saved : Memo}
    (actual : Scan budget unconstrained reaches values classes before memo outcome selected after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []) (active : ∀ paths ∈ classes, Nontrivial paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes before memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ final next, SourceCurrentConjunctionClassScanGlobalMemos.ScanReads actual memos final ∧
      Valid after.native.machine.heap final ∧ At formulas solver next after ∧
      ∀ rejected, outcome = some rejected →
        ¬∃ ambient symbol terms,
          All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms ∧
          Satisfies (.node symbol terms) classes := by
  obtain ⟨final, next, reads, coherent, _, afterAt, _, _, _, _, sound⟩ :=
    SourceCurrentConjunctionClassScanGlobalMemos.verified formulas solver inventory actual ready admitted
      available proper active correct ranges memos valid
  refine ⟨final, next, reads, coherent, afterAt, ?_⟩
  intro rejected stopped witness
  obtain ⟨ambient, symbol, terms, accepted, satisfies⟩ := witness
  have member : rejected ∈ classes := by
    subst outcome
    exact SourceCurrentConjunctionClassScan.stopped_member actual
  exact sound rejected stopped ambient symbol terms accepted (satisfies rejected member)

-- The constructed cold-native entry accepts warm global tables and derives empty-fourth-memo correctness itself.
theorem constructed_empty_fourth {initialCache finalCache : Cache.State Key} {originals : List Guard}
    (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (memos : Memos) (globals : Valid heap memos) :
    ∃ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
      SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
      SourceEqualityConstraintAllocation.Ready finalCache loaded.stored ∧
      ∀ inherited : Stored, SourceEqualityConstraintAllocation.Ready finalCache inherited →
        ∀ output : List Record,
          (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited
            (SourceEqualityConstraintMemoAllocation.initial finalCache)).1 = .ok (.classes output) →
          SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches edge.children
            (output.map Record.paths) (prefixState width heap loaded inherited finalCache) SourceCurrentEmptinessMemo.empty →
          ∃ outcome selected after saved next final,
            ∃ actual : Scan budget unconstrained reaches edge.children (output.map Record.paths)
              (prefixState width heap loaded inherited finalCache) SourceCurrentEmptinessMemo.empty outcome selected after saved,
              SourceCurrentConjunctionClassScanGlobalMemos.ScanReads actual memos final ∧
              Valid after.native.machine.heap final ∧ At formulas solver next after ∧
              SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
              (∀ rejected, outcome = some rejected → rejected ∈ output.map Record.paths ∧
                ∀ ambient symbol terms,
                  All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
                    edge.children terms → ¬ClassSat (.node symbol terms) rejected) := by
  obtain ⟨loaded, found, readback, storedReady, entry⟩ :=
    SourceCurrentConjunctionAllocatedGlobalMemos.finite width history valid expression covered value heap built
      edge resident formulas solver budget SourceCurrentEmptinessMemo.empty
      (SourceCurrentEmptinessMemo.empty_correct formulas solver heap) memos globals
  refine ⟨loaded, found, readback, storedReady, ?_⟩
  intro inherited inheritedReady output checked ranges
  obtain ⟨outcome, selected, after, saved, next, final, actual, reads, coherent, _, admitted, _, _, correct, _, sound⟩ :=
    entry inherited inheritedReady output checked ranges
  exact ⟨outcome, selected, after, saved, next, final, actual, reads, coherent, admitted, correct, sound⟩

end MicroCFTA.SourceCurrentConjunctionRootGlobalIndependentProbes

#print axioms MicroCFTA.SourceCurrentConjunctionRootGlobalIndependentProbes.stop_before_suffix
#print axioms MicroCFTA.SourceCurrentConjunctionRootGlobalIndependentProbes.verified_stop
#print axioms MicroCFTA.SourceCurrentConjunctionRootGlobalIndependentProbes.constructed_empty_fourth
#check @MicroCFTA.SourceCurrentConjunctionRootGlobalIndependentProbes.stop_before_suffix
#check @MicroCFTA.SourceCurrentConjunctionRootGlobalIndependentProbes.verified_stop
#check @MicroCFTA.SourceCurrentConjunctionRootGlobalIndependentProbes.constructed_empty_fourth
