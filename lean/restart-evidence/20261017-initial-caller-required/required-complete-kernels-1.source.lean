import MicroCFTA.SourceCurrentConstrainedCapSelectedRequiredComplete

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.SelectedRequiredInitialContract
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
variable {width : Nat} [DecidableEq (EdgeKey Symbol Guard)]

/-- Own initial Required execution supplies selected domains, exact language, and stable replay on its same return. -/
theorem initial_language_domains_and_replay (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Checked width)
    (frame : Frame formulas solver inventory before) (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap false before.native.machine.heap)
    (caps : ∀ value ∈ values, Cap depth value) (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ results heap final,
      Frame formulas solver inventory (SourceCurrentConjunctionClassScan.advanceHeap before heap) ∧
      SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap heap memos final ∧
      (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
      (∀ path ∈ selected.flatten, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results) ∧
      (∀ (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (terms : List (Term Symbol)),
        All₂ (meaning holds ambient) results terms ↔ All₂ (meaning holds ambient) values terms ∧
          SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms) ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
          (SourceEqualitySelectedRequired.paths selected) values before.native.machine.heap) results heap := by
  obtain ⟨results, heap, final, _fuel, _readFuel, required, _reads, returned, globals, bounded, length, _done⟩ :=
    SourceCurrentConstrainedCapSelectedRequiredComplete.complete depth formulas solver inventory unconstrained reaches
      selected values before frame available proper primary caps memos valid
  exact ⟨results, heap, final, returned, globals, bounded, length, required.paths, required.language, required.stable⟩

end MicroCFTA.SelectedRequiredInitialContract

#check @MicroCFTA.SelectedRequiredInitialContract.initial_language_domains_and_replay
#print axioms MicroCFTA.SelectedRequiredInitialContract.initial_language_domains_and_replay
#print MicroCFTA.SelectedRequiredInitialContract.initial_language_domains_and_replay
