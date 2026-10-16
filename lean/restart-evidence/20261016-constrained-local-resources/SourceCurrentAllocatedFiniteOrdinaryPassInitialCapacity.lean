import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassCapacity

/-!
# Initial headroom for the current class-pass capacity plan

Each head plan uses the exact result of an earlier tail.
The initial total budget constructs that shorter tail.
Literal worker uniqueness identifies every supplied tail with this result.
The remaining budget gives the head class its capacity plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold Pass PassReads Receipt)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryPassResources (nodeBudget edgeBudget outputRows outputArity)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "PassCapacity" => SourceCurrentAllocatedFiniteOrdinaryPassCapacity.PassCapacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Two raw folds retain the same forest, full checked state, and Merge memo. -/
theorem fold_unique {width : Nat} {records values first second}
    {before after later : Checked width} {memo saved current : Memo}
    (one : Fold records values before memo first after saved)
    (two : Fold records values before memo second later current) :
    first = second ∧ after = later ∧ saved = current := by
  obtain ⟨e, p, h, m, s, n, completed⟩ := SourceCurrentAllocatedClassWorkerCompletion.fold_complete one
  obtain ⟨E, P, H, M, S, N, other⟩ := SourceCurrentAllocatedClassWorkerCompletion.fold_complete two
  exact SourceCurrentAllocatedClassWorkerStability.fold_done_unique
    (completed e p h m s n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
    (other E P H M S N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))

/-- Initial profiles and total headroom derive the universal earlier-tail capacity plan. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (records : List Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    PassCapacity bits records values before memo := by
  induction records generalizing inventory values before memo memos with
  | nil => exact .nil
  | cons record records ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have tailPaths := fun own member => pathsBound own (List.mem_cons_of_mem record member)
      change before.native.machine.heap.nodes.next + (nodeBudget records rows arity count depth bound +
        SourceCurrentAllocatedFiniteOrdinaryClassResources.nodeBudget record
          (outputRows records rows count depth bound) (outputArity records arity) count depth bound) ≤ 2 ^ bits at nodes
      change before.native.machine.heap.edges.next + (edgeBudget records rows arity count depth bound +
        SourceCurrentAllocatedFiniteOrdinaryClassResources.edgeBudget record
          (outputRows records rows count depth bound) (outputArity records arity) count depth bound) ≤ 2 ^ (bits + 2) at edges
      have tailCapacity := ih (inventory := inventory) (coherent := tailCoherent) (active := tailActive)
        (values := values) (before := before) (memo := memo) (ready := ready) (admitted := admitted)
        (available := available) (physical := physical) (profiles := profiles) (native := native) (output := output)
        (covered := covered) (memos := memos) (valid := valid) (profile := profile) (lengthBound := lengthBound)
        (pathsBound := tailPaths) (heightBound := heightBound) (nodes := by omega) (edges := by omega)
      refine .cons tailCapacity ?_
      intro supplied step current actualTail
      obtain ⟨chosen, after, saved, tailInventory, final, _requests, tailActual, _tailReads, first,
        _tailStable, tailNative, tailOutput, tailProfiles, tailProfile, _tailNarrow, tailLength, tailHeight,
        _tailTrace, _tailNodes, _tailEdges, _tailCapacity, tailNodeSupply, tailEdgeSupply⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryPassResources.fold_complete formulas solver inventory bits records
          tailCoherent tailActive values before memo ready admitted available physical profiles native output covered
          memos valid rows arity count depth bound profile lengthBound tailPaths heightBound (by omega) (by omega)
      obtain ⟨rfl, rfl, rfl⟩ := fold_unique tailActual actualTail
      exact SourceCurrentAllocatedFiniteOrdinaryClassInitialCapacity.complete formulas solver tailInventory bits record
        (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) chosen after saved first.ready first.admitted
        first.available first.stored tailProfiles tailNative tailOutput first.covered final first.globals.valid
        (outputRows records rows count depth bound) (outputArity records arity) count depth bound tailProfile
        (by omega) (pathsBound _ List.mem_cons_self) tailHeight (by omega) (by omega)

/-- Initial headroom derives the existing range plan without a supplied capacity predicate. -/
theorem ranges (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (records : List Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedClassPass.Ranges records values before memo := by
  exact SourceCurrentAllocatedFiniteOrdinaryPassCapacity.ranges bits formulas solver inventory records values before memo
    coherent active ready admitted available (ChildrenShape.domain values profile) physical covered native profiles.domain
    (complete formulas solver inventory bits records coherent active values before memo ready admitted available
      physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges) memos valid

/-- The derived plan constructs the existing full pass receipt at the same returned state. -/
theorem finite (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (records : List Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ results after saved next final, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final ∧
      NativeStored after.native ∧ MergeStored saved ∧
      All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results := by
  exact SourceCurrentAllocatedFiniteOrdinaryPassCapacity.finite bits formulas solver inventory
    (complete formulas solver inventory bits records coherent active values before memo ready admitted available
      physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges) coherent active ready admitted available
    (ChildrenShape.domain values profile) physical covered native profiles.domain memos valid

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity
