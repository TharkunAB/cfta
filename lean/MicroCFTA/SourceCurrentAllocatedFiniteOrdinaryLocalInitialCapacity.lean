import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalCapacity

/-!
# Initial headroom for the current local capacity plan

Only the deterministic initial precheck can select a class stage.
Its receipt derives the actual prefix state and normalized class fields.
Initial local headroom then derives that stage's universal capacity plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedLocalReduction (Reduction Receipt)
open SourceCurrentAllocatedLocalReductionActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryLocalResources (nodeBudget edgeBudget)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
local notation "LocalCapacity" => SourceCurrentAllocatedFiniteOrdinaryLocalCapacity.LocalCapacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial same-cache field facts and headroom derive every local capacity obligation. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    LocalCapacity bits budget loaded inherited values before fourth memo := by
  intro records actual
  obtain ⟨own, checked⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory
    before original loaded inherited ready admitted cached found inheritedReady actual
  obtain ⟨proper, _records, _read, _classes, _order, fields⟩ := checked.classes records rfl
  have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
    intro record member
    exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
  exact SourceCurrentAllocatedFiniteOrdinaryStageInitialCapacity.complete formulas solver inventory bits budget records
    values (prefixState before loaded inherited) fourth memo checked.ready checked.admitted available recordsProper fields
    correct physical profiles native output covered memos valid rows arity count depth bound profile lengthBound
    (pathsBound records actual) heightBound
    (by change before.native.machine.heap.nodes.next + _ ≤ _; simpa only [nodeBudget, actual] using nodes)
    (by change before.native.machine.heap.edges.next + _ ≤ _; simpa only [edgeBudget, actual] using edges)

/-- Initial local budgets derive the old reached range plan at every live prefix. -/
theorem ranges (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo := by
  exact SourceCurrentAllocatedFiniteOrdinaryLocalCapacity.ranges bits formulas solver inventory budget original loaded inherited
    values before fourth memo ready admitted cached found inheritedReady available (ChildrenShape.domain values profile)
    correct physical covered native profiles.domain (complete formulas solver inventory bits budget original loaded inherited values before fourth memo ready admitted
      cached found inheritedReady available correct physical profiles native output covered memos valid rows arity count depth bound
      profile lengthBound pathsBound heightBound nodes edges) memos valid

/-- The derived local plan constructs the existing full receipt without a supplied plan. -/
theorem finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ results after savedFourth saved next final,
      ∃ actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next original loaded inherited values results before after fourth savedFourth memo saved final ∧
        NativeStored after.native ∧ MergeStored saved ∧
        All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results := by
  exact SourceCurrentAllocatedFiniteOrdinaryLocalCapacity.finite bits formulas solver inventory budget original loaded inherited
    values before fourth memo ready admitted cached found inheritedReady available (ChildrenShape.domain values profile)
    correct physical covered native profiles.domain (complete formulas solver inventory bits budget original loaded inherited values before fourth memo ready admitted
      cached found inheritedReady available correct physical profiles native output covered memos valid rows arity count depth bound
      profile lengthBound pathsBound heightBound nodes edges) memos valid

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity
