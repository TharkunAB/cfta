import MicroCFTA.SourceCurrentConjunctionClassScanSoundness
import MicroCFTA.SourceCurrentPrimaryReplay
import MicroCFTA.SourceCurrentRequiredLanguage
import MicroCFTA.SourceCurrentRequiredEndpoints
import MicroCFTA.SourceCurrentRequiredHeapEffects

/-!
# Current checked scans followed by actual required-path filtering

Selected primary traces replay at the actual scan return heap. Their
canonical path union supplies the required-worker domain. Finite required
execution retains loaded equality fields in the same operation cache.
Physical advancement retains both native tables, the domain cache, and
the current input inventory. Unselected original siblings can remain open.
Global gate memo receipts and later class edits are separate steps.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequired
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan
open SourceCurrentConjunctionClassScanCompletion (Ranges)
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}

/-- Every selected current primary gate has an exact false certificate at the scan's actual final heap. -/
theorem selected_primary [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {outcome : Option Class} {before after : Checked width} {memo saved : Memo}
    (actual : Scan budget unconstrained reaches values classes before memo outcome selected after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []) (active : ∀ paths ∈ classes, Nontrivial paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : Ranges budget unconstrained reaches values classes before memo) :
    ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      after.native.machine.heap false after.native.machine.heap := by
  induction actual generalizing inventory with
  | nil => intro paths member; cases member
  | @selected paths heap classes before memo outcome selected after saved primary rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      have firstAdmission := admitted.advance ⟨heap, before.operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1)
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct
      have tailProper := fun paths member => proper paths (List.mem_cons_of_mem _ member)
      have tailActive := fun paths member => active paths (List.mem_cons_of_mem _ member)
      have tailRanges := ranges.1 heap primary
      have tail := ih inventory first.1 firstAdmission first.2.2 tailProper tailActive firstCorrect tailRanges
      obtain ⟨_, _, _, remaining, _, _, _, _⟩ := SourceCurrentConjunctionClassScanSoundness.verified
        formulas solver inventory rest first.1 firstAdmission first.2.2 tailProper tailActive firstCorrect tailRanges
      intro paths member
      rcases List.mem_cons.mp member with rfl | member
      · exact (SourceCurrentPrimaryReplay.class_replay unconstrained reaches values paths
          before.native.machine.heap false heap primary ready.semantic available).2.2
          after.native.machine.heap remaining.keeps.growth
      · exact tail paths member
  | @skipped paths heap anchor classes before memo outcome selected after saved primary secondary rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      have firstAdmission := admitted.advance ⟨heap, before.operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1)
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct
      have second := secondary_effects unconstrained secondary first.1 first.2.2
      have secondAdmission := firstAdmission.advance ⟨anchor, (advanceHeap before heap).operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension _ _ second.2.1)
      have secondCorrect := SourceCurrentEmptinessMemo.grows formulas solver second.2.1.keeps memo firstCorrect
      exact ih inventory second.1 secondAdmission second.2.2
        (fun paths member => proper paths (List.mem_cons_of_mem _ member))
        (fun paths member => active paths (List.mem_cons_of_mem _ member)) secondCorrect
        (ranges.2.1 heap primary anchor secondary)
  | @continued paths heap anchor before query middle memo later savedMemo classes outcome selected after saved
      primary secondary seeded decision rest ih =>
      have first := primary_effects unconstrained reaches primary ready available
      have firstAdmission := admitted.advance ⟨heap, before.operations⟩
        (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.2.1)
      have firstCorrect := SourceCurrentEmptinessMemo.grows formulas solver first.2.1.keeps memo correct
      have reached := ranges.2.2 heap primary anchor secondary
      obtain ⟨nextInventory, queryReceipt, _⟩ := SourceCurrentAllocatedSeededLanguage.false_class_receipt
        formulas solver inventory unconstrained paths values secondary seeded first.1.good first.2.1.ready
        first.1.scopedCache first.1.idle firstAdmission first.2.2 (proper paths List.mem_cons_self) reached.1
      have queryReady : Ready middle := ⟨queryReceipt.good, queryReceipt.effects.ready.semantic,
        queryReceipt.effects.ready.costs, queryReceipt.scopes, queryReceipt.idle⟩
      have queryCorrect := SourceCurrentEmptinessMemo.grows formulas solver queryReceipt.effects.keeps memo firstCorrect
      obtain ⟨memoReady, memoEffects, memoCorrect, _, _⟩ :=
        memo_effects formulas solver decision queryReady queryReceipt.available queryCorrect
      have memoAdmission := queryReceipt.admitted.advance later
        (SourceCurrentAllocatedQueryMemo.advance_extension middle later memoEffects)
      have memoValues : Values (advancePhysical middle later).native.machine.heap values := fun value member =>
        memoEffects.keeps.available value (queryReceipt.effects.keeps.available value (first.2.2 value member))
      exact ih nextInventory memoReady memoAdmission memoValues
        (fun paths member => proper paths (List.mem_cons_of_mem _ member))
        (fun paths member => active paths (List.mem_cons_of_mem _ member)) memoCorrect
        (reached.2 query middle seeded later savedMemo decision)
  | stopped => intro paths member; cases member

/-- Required execution retains the exact checked state and every selected original path domain. -/
structure Receipt [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (selected : Constraints) (values results : List (Value Symbol Guard))
    (before after : Checked width) : Prop where
  stable : SourceEqualityRequiredWorkerComplete.StableRun
    (fun fuel readFuel => SourceEqualityRequiredExecution.requireAll fuel readFuel
      (SourceEqualitySelectedRequired.paths selected) values before.native.machine.heap) results after.native.machine.heap
  effects : Effects (physical before) (physical after)
  ready : Ready after
  admitted : At formulas solver inventory after
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine
  nodes : after.native.nodes = before.native.nodes
  edges : after.native.edges = before.native.edges
  domains : after.native.machine.domains = before.native.machine.domains
  operations : after.operations = before.operations
  originals : Values after.native.machine.heap values
  resident : Values after.native.machine.heap results
  paths : ∀ path ∈ selected.flatten, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results
  language : ∀ holds ambient terms, All₂ (meaning holds ambient) results terms ↔
    All₂ (meaning holds ambient) values terms ∧
      SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms

/-- Final primary certificates derive finite literal required execution with no whole-forest closedness premise. -/
theorem required_complete [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : Constraints) (values : List (Value Symbol Guard)) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap false before.native.machine.heap) :
    ∃ results heap, Receipt formulas solver inventory selected values results before (advanceHeap before heap) := by
  have tips := SourceCurrentRequiredTipSupport.selected_domain ready.semantic available primary
  have support := SourceCurrentRequiredTipSupport.forest_support tips
  obtain ⟨results, heap, kept, semantic, resident, stable⟩ := SourceCurrentRequiredComplete.requireAll_complete
    unconstrained before.native.machine.heap ready.semantic (SourceEqualitySelectedRequired.paths selected)
      (SourceEqualitySelectedRequired.paths_nonnegative selected) values before.native.machine.heap ready.semantic
      available (grows_refl _) support
  have stableRun := stable
  obtain ⟨fuel, readFuel, enough⟩ := stable
  have done := enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  have fields := SourceCurrentRequiredHeapEffects.requireAll
    (SourceCurrentConjunctionEquality.FieldAvailable before.operations)
    fuel readFuel (SourceEqualitySelectedRequired.paths selected) values results before.native.machine.heap heap
      done ready.semantic ready.costs ready.good.fields available
  have effects : Effects (physical before) ⟨heap, before.operations⟩ :=
    ⟨fields.1, ⟨fields.2.1, fields.2.2.1, ready.good.operations, fields.2.2.2.1⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl before.operations⟩
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before ⟨heap, before.operations⟩ effects
  refine ⟨results, heap, stableRun, effects, advance_ready before _ ready effects,
    admitted.advance ⟨heap, before.operations⟩ extension, extension, rfl, rfl, rfl, rfl,
    (fun value member => kept.available value (available value member)), resident, ?_, ?_⟩
  · intro path member
    exact SourceCurrentRequiredEndpoints.selected_paths_closed unconstrained reaches before.native.machine.heap
      ready.semantic (SourceEqualityExposureCosts.gate_ready ready.semantic ready.costs) selected values available primary
      fuel readFuel results before.native.machine.heap heap done ready.semantic available (grows_refl _)
      path member (proper path member)
  · exact SourceCurrentRequiredLanguage.requireAll_done unconstrained before.native.machine.heap ready.semantic
      fuel readFuel (SourceEqualitySelectedRequired.paths selected) values results before.native.machine.heap heap done
      (SourceEqualitySelectedRequired.paths_nonnegative selected) ready.semantic available (grows_refl _) support

/-- A successful actual current scan derives finite required execution at its same returned checked state. -/
theorem scan_required_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {before after : Checked width} {memo saved : Memo}
    (actual : Scan budget unconstrained reaches values classes before memo none selected after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []) (active : ∀ paths ∈ classes, Nontrivial paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
    (ranges : Ranges budget unconstrained reaches values classes before memo) :
    ∃ next results heap, Receipt formulas solver next selected values results after (advanceHeap after heap) ∧
      Effects (physical before) (physical (advanceHeap after heap)) ∧
      SourceCurrentEmptinessMemo.Correct formulas solver heap saved ∧ SourceCurrentEmptinessMemo.Extends memo saved := by
  obtain ⟨next, finalReady, finalAdmission, scanEffects, finalValues, finalCorrect, retained, _⟩ :=
    SourceCurrentConjunctionClassScanSoundness.verified formulas solver inventory actual ready admitted available proper active correct ranges
  have primary := selected_primary formulas solver inventory actual ready admitted available proper active correct ranges
  have selectedProper : ∀ path ∈ selected.flatten, path ≠ [] := by
    intro path member
    obtain ⟨paths, included, present⟩ := List.mem_flatten.mp member
    exact proper paths ((selected_sublist actual).subset included) path present
  obtain ⟨results, heap, receipt⟩ := required_complete formulas solver next unconstrained reaches selected values after
    finalReady finalAdmission finalValues selectedProper primary
  exact ⟨next, results, heap, receipt, scanEffects.trans receipt.effects,
    SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps saved finalCorrect, retained⟩

end MicroCFTA.SourceCurrentConjunctionRequired
