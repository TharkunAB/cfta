import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerActual

namespace MicroCFTA.AllocatedEditActualKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditWorker
open SourceCurrentAllocatedSharedEditRanges SourceCurrentAllocatedSharedEditEffects
open SourceCurrentAllocatedSharedEditWorkerActual
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "MemoValid" => EndpointMemoGateTrace.Valid
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
variable (known : Values base originals)
variable (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)
variable (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
include known domains coherent active

/-- The literal list return carries valid global tables and probe fields at its exact checked state. -/
theorem supplied_return_has_current_ready_globals_and_probes
    (inventory : Inventory) {e p h m s n : Nat} {edits values results} {before after : SharedState width}
    (ranges : ListRanges record originals edits values before)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ListSafe edits values)
    (memos : Memos) (valid : MemoValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap)
    (done : editList (edit record originals e p h m s n) edits values before = .done results after) :
    ∃ next final, Ready formulas solver next record originals base after ∧
      Values after.checked.native.machine.heap results ∧ MemoValid after.checked.native.machine.heap final ∧
      final.query = memos.query ∧ Extends memos.unfolding final.unfolding ∧
      ProbeHeap after.checked.native.machine.heap := by
  obtain ⟨next, final, _, _, receipt, afterProbes, _⟩ := list_verified formulas solver record originals base known domains coherent active
    inventory ranges populated allowed ready available safe memos valid probes done
  exact ⟨next, final, receipt.ready, receipt.available, receipt.globals.valid,
    receipt.globals.query, receipt.globals.retained, afterProbes⟩

/-- A second finite edit uses the actual first return's inventory, fields, memos, and captured forest. -/
theorem consecutive_edits_need_no_second_ready_or_model_oracle
    (inventory : Inventory) {e p h m s n : Nat} {edits secondEdits values results} {before middle : SharedState width}
    (ranges : ListRanges record originals edits values before)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ListSafe edits values)
    (memos : Memos) (valid : MemoValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap)
    (done : editList (edit record originals e p h m s n) edits values before = .done results middle)
    (secondRanges : ListRanges record originals secondEdits results middle)
    (secondPopulated : Populated secondEdits) (secondAllowed : Allowed record secondEdits)
    (secondSafe : ListSafe secondEdits results) :
    ∃ outputs after next final,
      Ready formulas solver next record originals base after ∧
      Values after.checked.native.machine.heap outputs ∧
      ProbeHeap after.checked.native.machine.heap ∧
      Extends before.memo after.memo ∧ final.query = memos.query ∧
      MemoValid after.checked.native.machine.heap final ∧
      SourceCurrentAllocatedSharedEditWorkerCompletion.StableRun
        (fun e p h m s n => editList (edit record originals e p h m s n) secondEdits results middle) outputs after := by
  obtain ⟨firstInventory, firstMemos, _, _, first, middleProbes, _⟩ :=
    list_verified formulas solver record originals base known domains coherent active inventory ranges populated allowed
      ready available safe memos valid probes done
  obtain ⟨outputs, after, next, final, _, _, second, afterProbes, stable⟩ :=
    list_finite formulas solver record originals base known domains coherent active firstInventory secondRanges secondPopulated
      secondAllowed first.ready first.available secondSafe firstMemos first.globals.valid middleProbes
  exact ⟨outputs, after, next, final, second.ready, second.available, afterProbes,
    extends_trans first.retained second.retained, second.globals.query.trans first.globals.query, second.globals.valid, stable⟩

/-- Compiled literal success receives the same checked receipt through its actual build equation. -/
theorem signed_compiled_success_retains_actual_reads
    (inventory : Inventory) {e p h m s n : Nat} {signed : List (Path × EqualityNormalize.Path)}
    {values results : List (Value Symbol Guard)} {before after : SharedState width}
    (ranges : ListRanges record originals (build signed) values before)
    (populated : Populated (build signed)) (allowed : Allowed record (build signed))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ListSafe (build signed) values)
    (memos : Memos) (valid : MemoValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap)
    (done : editAll record originals e p h m s n signed values before = .done results after) :
    ∃ next final, ∃ actual : EditList record originals (build signed) values before results after,
      ListReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final ∧
      ProbeHeap after.checked.native.machine.heap := by
  obtain ⟨next, final, actual, reads, receipt, afterProbes, _⟩ :=
    list_verified formulas solver record originals base known domains coherent active inventory ranges populated allowed
      ready available safe memos valid probes done
  exact ⟨next, final, actual, reads, receipt, afterProbes⟩

/-- The independent semantic bounds follow for the supplied executable return, not an assumed output law. -/
theorem supplied_worker_conditional_language
    (inventory : Inventory) {e p h m s n : Nat} {edits values results} {before after : SharedState width}
    (ranges : ListRanges record originals edits values before)
    (editsValid : SourceEqualityEdits.Valid edits) (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ListSafe edits values)
    (memos : Memos) (valid : MemoValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap)
    (done : editList (edit record originals e p h m s n) edits values before = .done results after)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (rootTerms terms : List (Term Symbol))
    (captured : All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) originals rootTerms)
    (satisfied : EqualityNormalize.ClassSat (.node symbol rootTerms) record.paths)
    (matched : SourceEqualityEditAPI.ListCondition
      (fun path part => Term.atPath (.node symbol rootTerms) path = some part) edits terms) :
    All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
      All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms := by
  obtain ⟨narrows, preserves⟩ := list_language formulas solver record originals base known domains coherent active inventory
    ranges editsValid populated allowed ready available safe memos valid probes done ambient symbol rootTerms terms
  exact ⟨narrows, preserves captured satisfied matched⟩

#print axioms supplied_return_has_current_ready_globals_and_probes
#print axioms consecutive_edits_need_no_second_ready_or_model_oracle
#print axioms signed_compiled_success_retains_actual_reads
#print axioms supplied_worker_conditional_language
set_option pp.explicit true
#check @supplied_return_has_current_ready_globals_and_probes
#check @consecutive_edits_need_no_second_ready_or_model_oracle
#check @signed_compiled_success_retains_actual_reads
#check @supplied_worker_conditional_language
end MicroCFTA.AllocatedEditActualKernels
