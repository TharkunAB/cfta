import MicroCFTA.SourceSizedPrefixKnownOrdinary
import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources
import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Known ordinary handles after actual native heap effects

The laws retain each old stored handle and its exact decoded value.
They keep the same enumeration cache and the same shared height bound.
The final law derives its actual completed query from current entry gates.
It does not classify the newly returned query value or later cache updates.
-/
namespace MicroCFTA.SourceSizedPrefixKnownOrdinaryHeap
open InternedConstructorTemplates InternedProbeProvenance
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width heightBound : Nat}

/-- Actual constructor Keeps retains each old decoded value and its height bound. -/
theorem keeps_known {before after : State Symbol Guard} {cached : Cached}
    (kept : SourceEqualityRequiredCache.Keeps before after)
    (known : KnownOrdinary heightBound before cached) : KnownOrdinary heightBound after cached := by
  intro handle scs member
  obtain ⟨value, present, ordinary, height⟩ := known handle scs member
  exact ⟨value, SourcePruningEnumerationNodes.lookupNode_keeps before after kept handle value present,
    ordinary, height⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual caller Post retains successful old-handle physical lookup. -/
theorem post_lookupNode
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {next : Inventory} {before after : Caller width} {final : Memos}
    (post : SourceCurrentAllocatedPartialInvariant.Post formulas solver next before after final)
    (handle : Nat) (value : Value Symbol Guard)
    (present : SourcePruningEnumerationNodes.lookupNode before.checked.native.machine.heap handle = some value) :
    SourcePruningEnumerationNodes.lookupNode after.checked.native.machine.heap handle = some value :=
  SourcePruningEnumerationNodes.lookupNode_keeps _ _ post.effects.keeps handle value present

/-- The actual caller Post retains the old cache at the literal reached native heap. -/
theorem post_known
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {next : Inventory} {before after : Caller width} {final : Memos} {cached : Cached}
    (post : SourceCurrentAllocatedPartialInvariant.Post formulas solver next before after final)
    (known : KnownOrdinary heightBound before.checked.native.machine.heap cached) :
    KnownOrdinary heightBound after.checked.native.machine.heap cached :=
  keeps_known post.effects.keeps known

/-- An actual query receipt retains the old cache at its reached heap. -/
theorem query_known
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {left right value : Value Symbol Guard} {before after : Checked width}
    {memos : Memos} {cached : Cached}
    (receipt : SourceCurrentAllocatedTargetQuery.Receipt formulas solver inventory left right before value after memos)
    (known : KnownOrdinary heightBound before.native.machine.heap cached) :
    KnownOrdinary heightBound after.native.machine.heap cached :=
  keeps_known receipt.effects.keeps known

/-- Current resource gates produce a completed query and retain the same old cache. -/
theorem finite_query_known (bits : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (left right : Value Symbol Guard) (before : Checked (bits + 2))
    (ready : SourceCurrentConjunctionClassScan.Ready before) (admitted : At formulas solver inventory before)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile before) (room : Room bits profile)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (cached : Cached) (known : KnownOrdinary heightBound before.native.machine.heap cached) :
    ∃ next : Inventory, ∃ value after,
      next.source = before.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right before value after memos ∧
      KnownOrdinary heightBound after.native.machine.heap cached := by
  have actualRoom := fits.room room
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left before.native.machine.heap
    ready.good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right before.native.machine.heap
    ready.good.native.machine.1.coherent rightAvailable rightClosed
  have ranges := (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before
    ready.good ready.semantic left right leftOriginal rightOriginal leftAvailable rightAvailable
    actualRoom.1 actualRoom.2.1 actualRoom.2.2).1
  obtain ⟨next, value, after, source, roots, receipt⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver inventory left right before ready admitted leftAvailable rightAvailable
    leftClosed rightClosed ranges memos valid
  exact ⟨next, value, after, source, roots, receipt, query_known receipt known⟩

end MicroCFTA.SourceSizedPrefixKnownOrdinaryHeap
