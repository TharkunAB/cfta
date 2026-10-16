import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources
import MicroCFTA.SourceCurrentAllocatedTargetWorkerCompletion

/-!
# Reached Target capacity from initial resource bounds

Stable literal workers identify every raw completed prefix uniquely.
Constructed resource returns therefore bound all actual operand and tail
prefixes in the existing universal capacity plan.
No reached capacity or completed enclosing Target is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetInitialCapacity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentMemoMergeLanguage (CacheCovers)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (height childrenHeight)
namespace Numbers
export SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers
  (operandRows targetRows nodeBudget edgeBudget targetRows_base targetRows_step nodeBudget_base nodeBudget_step edgeBudget_base edgeBudget_step)
end Numbers
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
variable {width : Nat}

open SourceCurrentAllocatedTargetWorkerCompletion (StableRun)

/-- Stable executions of one literal worker identify every returned field. -/
theorem stable_unique
    {evaluation : Nat → Nat → Nat → Nat → Nat → SourceCurrentAllocatedTargetWorker.Outcome width}
    {first second : Value Symbol Guard} {after later : Checked width} {saved current : Memo}
    (one : StableRun evaluation first after saved) (two : StableRun evaluation second later current) :
    first = second ∧ after = later ∧ saved = current := by
  obtain ⟨p, h, m, s, n, firstDone⟩ := one
  obtain ⟨q, i, k, t, o, secondDone⟩ := two
  have firstStable := firstDone (max p q) (max h i) (max m k) (max s t) (max n o)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have secondStable := secondDone (max p q) (max h i) (max m k) (max s t) (max n o)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  exact SourceCurrentAllocatedTargetWorker.Outcome.done.inj (firstStable.symm.trans secondStable)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Raw operands from one entry return the same value, complete checked state, and memo. -/
theorem operand_unique {path : List Int} {values : List (Value Symbol Guard)}
    {before after later : Checked width} {memo saved current : Memo} {first second : Value Symbol Guard}
    (one : Operand path values before memo first after saved) (two : Operand path values before memo second later current) :
    first = second ∧ after = later ∧ saved = current :=
  stable_unique (SourceCurrentAllocatedTargetWorkerCompletion.operand_complete one)
    (SourceCurrentAllocatedTargetWorkerCompletion.operand_complete two)

/-- Raw folds from one entry retain the same full returned state and completed memo. -/
theorem fold_unique {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after later : Checked width} {memo saved current : Memo} {first second : Value Symbol Guard}
    (one : Fold values seed paths before memo first after saved) (two : Fold values seed paths before memo second later current) :
    first = second ∧ after = later ∧ saved = current :=
  stable_unique (SourceCurrentAllocatedTargetWorkerCompletion.fold_complete one)
    (SourceCurrentAllocatedTargetWorkerCompletion.fold_complete two)

/-- Initial total headroom derives the existing universal plan for every actual earlier prefix. -/
theorem fold_capacity (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (before : Checked (bits + 2)) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ seed :: paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + Numbers.nodeBudget rows arity count depth bound paths.length ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + Numbers.edgeBudget rows arity count depth bound paths.length ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedFiniteOrdinaryTargetCapacity.FoldCapacity bits values seed paths before memo := by
  induction paths generalizing inventory before memo memos with
  | nil => trivial
  | cons path paths ih =>
      simp only [List.length_cons, Numbers.nodeBudget_step, Numbers.edgeBudget_step] at nodes edges
      obtain ⟨head, middle, current, currentMemos, _requests, first, firstProfiles, _headProfile, _headHeight,
        _trace, _firstNodes, _firstEdges, firstNodeSupply, firstEdgeSupply⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOperandResources.complete formulas solver inventory path values before memo
          ready admitted available physical profiles covered memos valid rows arity count depth bound profile
          lengthBound (pathsBound path (by simp)) heightBound
      have nativeMiddle := SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores.native first native output ready.idle
      have tailPaths : ∀ selected ∈ seed :: paths, selected.length ≤ depth := by
        intro selected member
        rcases List.mem_cons.mp member with rfl | member
        · exact pathsBound seed List.mem_cons_self
        · exact pathsBound selected (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
      have tailNodes : middle.native.machine.heap.nodes.next + Numbers.nodeBudget rows arity count depth bound paths.length ≤ 2 ^ bits := by omega
      have tailEdges : middle.native.machine.heap.edges.next + Numbers.edgeBudget rows arity count depth bound paths.length ≤ 2 ^ (bits + 2) := by omega
      have tailPlan := ih inventory middle current first.ready first.admitted first.originals first.stored firstProfiles
        nativeMiddle.1 nativeMiddle.2.1 first.covered currentMemos first.globals tailPaths tailNodes tailEdges
      constructor
      · intro actualHead actualMiddle actualCurrent operand
        obtain ⟨rfl, rfl, rfl⟩ := operand_unique operand (of_receipt first)
        exact tailPlan
      · intro actualHead actualMiddle actualCurrent actualTail actualLater actualSaved operand rest
        obtain ⟨rfl, rfl, rfl⟩ := operand_unique operand (of_receipt first)
        obtain ⟨result, after, saved, _next, _final, _requests, constructed, _reads, _receipt,
          _profiles, _native, _output, _profile, _height, _trace, _nodes, _edges, capacity, _nodeSupply, _edgeSupply⟩ :=
          SourceCurrentAllocatedFiniteOrdinaryTargetResources.fold_complete formulas solver inventory bits values seed paths middle current
            first.ready first.admitted first.originals first.stored firstProfiles nativeMiddle.1 nativeMiddle.2.1 first.covered
            currentMemos first.globals rows arity count depth bound profile lengthBound tailPaths heightBound tailNodes tailEdges
        obtain ⟨rfl, rfl, rfl⟩ := fold_unique rest constructed
        exact capacity

/-- Initial Target headroom discharges its old reached-prefix numeric capacity premise. -/
theorem target_capacity (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked (bits + 2)) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + SourceCurrentAllocatedFiniteOrdinaryTargetResources.nodeBudget rows arity count depth bound paths.length ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + SourceCurrentAllocatedFiniteOrdinaryTargetResources.edgeBudget rows arity count depth bound paths.length ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedFiniteOrdinaryTargetCapacity.TargetCapacity bits values paths before memo := by
  cases paths with
  | nil => trivial
  | cons seed paths => exact fold_capacity formulas solver inventory bits values seed paths before memo ready admitted available
      physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetInitialCapacity
