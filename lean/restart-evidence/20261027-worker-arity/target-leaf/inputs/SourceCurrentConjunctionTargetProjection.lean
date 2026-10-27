import MicroCFTA.SourceCurrentConjunctionRequired
import MicroCFTA.SourceEqualityProjectionPathComplete
import MicroCFTA.SourceEqualityProjectionAPI
import MicroCFTA.SourceEqualityProjectionCosts
import MicroCFTA.SourceEqualityQueryGlobalMemos
import MicroCFTA.SourceCurrentSubsumesQueryMemos

/-!
# Selected target projections in the current checked state

The selected path domain derives a closed projection. Other ordinary
siblings can remain open. Projection retains the equality operations and
all native tables. The same actual forest graph supplies global receipts.
Proper paths retain accepted selected subterms. Ancestor guards are not
part of the projected language. The root has exact union language.
-/
namespace MicroCFTA.SourceCurrentConjunctionTargetProjection
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionPathDomain
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}

/-- One actual projection retains the checked state and the same global reads. -/
structure Receipt [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (path : List Int) (values : List (Value Symbol Guard))
    (before : Checked width) (result : Value Symbol Guard) (after : Checked width)
    (memos final : Memos) : Prop where
  graph : Forest path values before.native.machine.heap result after.native.machine.heap
  advanced : after = advancePhysical before ⟨after.native.machine.heap, before.operations⟩
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : Effects (physical before) (physical after)
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine
  nodes : after.native.nodes = before.native.nodes
  edges : after.native.edges = before.native.edges
  domains : after.native.machine.domains = before.native.machine.domains
  operations : after.operations = before.operations
  available : Available after.native.machine.heap result
  closed : result.free = []
  stable : SourceEqualityRequiredWorkerComplete.StableRun
    (fun fuel readFuel => SourceEqualityProjectionWorker.forest fuel readFuel path values before.native.machine.heap)
    result after.native.machine.heap
  reads : SourceEqualityQueryGlobalMemos.ProjectionReads graph memos final
  globals : SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap after.native.machine.heap memos final
  included : path ≠ [] → ∀ holds ambient symbol terms part,
    All₂ (meaning holds ambient) values terms →
    SymbolicSignedPaths.lookup (.node symbol terms) path = some part → meaning holds ambient result part
  root_exact : path = [] → ∀ holds ambient term,
    meaning holds ambient result term ↔ ∃ value ∈ values, meaning holds ambient value term

/-- The actual forest graph derives every checked and global receipt at its literal return. -/
theorem verified [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    {path : List Int} {values : List (Value Symbol Guard)} {before : Checked width}
    {result : Value Symbol Guard} {heap : State Symbol Guard}
    (actual : Forest path values before.native.machine.heap result heap)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : ForestClosed path values)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ final, Receipt formulas solver inventory path values before result
      (advancePhysical before ⟨heap, before.operations⟩) memos final := by
  have selected := SourceEqualityProjectionPathDomain.forest_effects actual ready.semantic available domain
  have physicalCosts := SourceEqualityProjectionCosts.forest_effects actual ready.semantic ready.costs available
  have fields := SourceEqualityProjectionPathDomain.forest_heap
    (SourceCurrentConjunctionEquality.FieldAvailable before.operations) actual ready.semantic available domain ready.good.fields
  have effects : Effects (physical before) ⟨heap, before.operations⟩ :=
    ⟨selected.1, ⟨selected.2.1, physicalCosts.2.2.1, ready.good.operations, fields⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before ⟨heap, before.operations⟩ effects
  obtain ⟨final, reads, finalValid, retained⟩ := SourceEqualityQueryGlobalMemos.forest_memos
    actual ready.semantic ready.costs available memos valid
  refine ⟨final, actual, rfl, SourceCurrentConjunctionClassScan.advance_ready before _ ready effects,
    admitted.advance _ extension, effects, extension, rfl, rfl, rfl, rfl, selected.2.2.1, selected.2.2.2,
    SourceEqualityProjectionWorkerComplete.forest_stable actual, reads,
    ⟨selected.1, selected.2.1, physicalCosts.2.2.1, finalValid, retained, reads.2⟩, ?_, ?_⟩
  · intro nonroot holds ambient symbol terms part accepted found
    cases path with
    | nil => exact False.elim (nonroot rfl)
    | cons index path =>
      exact SourceEqualityProjectionPathDomain.forest_included
        actual ready.semantic available domain holds ambient symbol terms part accepted found
  · intro root holds ambient term
    subst path
    exact SourceEqualityProjectionAPI.forest_root actual ready.semantic available domain holds ambient term

/-- Selected path closure constructs a finite projection without a native request or a future-state premise. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (path : List Int) (values : List (Value Symbol Guard)) (before : Checked width)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : ForestClosed path values)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after final, Receipt formulas solver inventory path values before result after memos final := by
  obtain ⟨result, heap, actual, _⟩ := SourceEqualityProjectionPathComplete.forest_complete
    path values before.native.machine.heap ready.semantic available domain
  obtain ⟨final, receipt⟩ := verified formulas solver inventory actual ready admitted available domain memos valid
  exact ⟨result, _, final, receipt⟩

/-- A selected path in the current required receipt supplies the exact target projection domain. -/
theorem of_required [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {selected : Constraints} {originals values : List (Value Symbol Guard)}
    {before after : Checked width}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before after)
    (path : Path) (member : path ∈ selected.flatten)
    (memos : Memos) (valid : Valid after.native.machine.heap memos) :
    ∃ result reached final,
      Receipt formulas solver inventory (path.map Int.ofNat) values after result reached memos final :=
  complete formulas solver inventory (path.map Int.ofNat) values after required.ready required.admitted
    required.resident (required.paths path member) memos valid

end MicroCFTA.SourceCurrentConjunctionTargetProjection
