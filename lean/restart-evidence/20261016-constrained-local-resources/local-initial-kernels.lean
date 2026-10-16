import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity

namespace MicroCFTA.LocalInitialChecks
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


/-- An unchanged actual initial precheck needs no later capacity obligation. -/
theorem early_vacuous (bits budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (unchanged : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .unchanged) :
    LocalCapacity bits budget loaded inherited values before fourth memo := by
  intro records actual
  have impossible := Except.ok.inj (unchanged.symm.trans actual)
  cases impossible

/-- The initial budgets give every actual classes prefix its exact stage capacity plan. -/
theorem reached_classes (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    (edges : before.native.machine.heap.edges.next + edgeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ (bits + 2))
    (records : List SourceEqualityClassOrder.Record)
    (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records)) :
    SourceCurrentAllocatedFiniteOrdinaryStageCapacity.StageCapacity bits budget records values
      (prefixState before loaded inherited) fourth memo := by
  exact (SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity.complete formulas solver inventory bits budget original loaded inherited
    values before fourth memo ready admitted cached found inheritedReady available correct physical profiles native output covered
    memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges) records actual

/-- The derived plan constructs the current full local return and global validity. -/
theorem ranges_and_return (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo ∧
    ∃ results after savedFourth saved next final,
      ∃ actual : Reduction budget loaded inherited values before fourth memo results after savedFourth saved,
        Reads formulas solver actual memos final ∧
        Receipt formulas solver next original loaded inherited values results before after fourth savedFourth memo saved final ∧
        At formulas solver next after ∧ Valid after.native.machine.heap final ∧
        NativeStored after.native ∧ MergeStored saved ∧
        All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results := by
  have checks := SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity.ranges formulas solver inventory bits budget original loaded inherited
    values before fourth memo ready admitted cached found inheritedReady available correct physical profiles native output covered
    memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  obtain ⟨results, after, savedFourth, saved, next, final, actual, reads, receipt, nativeAfter, merged, related⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryLocalInitialCapacity.finite formulas solver inventory bits budget original loaded inherited
      values before fourth memo ready admitted cached found inheritedReady available correct physical profiles native output covered
      memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  exact ⟨checks, results, after, savedFourth, saved, next, final, actual, reads, receipt,
    receipt.admitted, receipt.globals, nativeAfter, merged, related⟩

end MicroCFTA.LocalInitialChecks

#print axioms MicroCFTA.LocalInitialChecks.early_vacuous
#check @MicroCFTA.LocalInitialChecks.early_vacuous

#print axioms MicroCFTA.LocalInitialChecks.reached_classes
#check @MicroCFTA.LocalInitialChecks.reached_classes

#print axioms MicroCFTA.LocalInitialChecks.ranges_and_return
#check @MicroCFTA.LocalInitialChecks.ranges_and_return
