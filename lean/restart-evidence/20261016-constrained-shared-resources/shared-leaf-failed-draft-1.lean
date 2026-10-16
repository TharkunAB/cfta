import MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedForceResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources

/-!
# Initial constructor resources for shared leaf narrowing

The actual force return supplies the target profile and next query entry.
Initial total headroom pays for forcing and the following intersection.
Captured originals and the current edited input can have different profiles.
The returned receipt retains the exact slots, Merge table, and global reads.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedLeafResources
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedGuardedLanguage (meaning)
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (advance)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (height childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Receipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "TargetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
local notation "ForceN" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.nodeBudget
local notation "ForceE" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.edgeBudget
local notation "NativeN" => SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.nodeBudget
variable {width : Nat}

/-- A common envelope bounds the query on the actual target and current input. -/
def queryBudget (record : Record) (rows arity count depth bound inputRows inputArity inputBound : Nat) : Nat :=
  NativeN (max (TargetRows record rows count depth bound) inputRows)
    (max (max arity 1) inputArity) (max bound inputBound)

/-- Total node headroom includes a possible first force and every leaf query. -/
def nodeBudget (record : Record) (rows arity count depth bound inputRows inputArity inputBound : Nat)
    (before : Shared width) (path : Path) : Nat :=
  ForceN record rows arity count depth bound before path +
    queryBudget record rows arity count depth bound inputRows inputArity inputBound

/-- The same conservative native bound pays separately for edge requests. -/
def edgeBudget (record : Record) (rows arity count depth bound inputRows inputArity inputBound : Nat)
    (before : Shared width) (path : Path) : Nat :=
  ForceE record rows arity count depth bound before path +
    queryBudget record rows arity count depth bound inputRows inputArity inputBound

private theorem of_parts [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : Path} {input target result : Value Symbol Guard}
    {before middle : Shared width} {checked : Checked width} {memos current : Memos}
    (first : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver inventory record values base path
      before target middle memos current)
    (query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver next target input middle.checked result checked current) :
    Receipt formulas solver next record values base path input before result (advance middle checked) memos current := by
  have queryGlobal : SourceCurrentSubsumesQueryMemos.Effect middle.checked.native.machine.heap checked.native.machine.heap current current :=
    ⟨query.effects.keeps, query.ready.semantic, query.ready.costs, query.globals, extends_refl _, rfl⟩
  refine ⟨.apply first.actual query.actual,
    .apply (forced := first.actual) (step := query.actual) first query,
    first.ready.advance next checked query.ready query.admitted query.effects,
    first.effects.trans query.effects, first.extension.trans query.extension,
    query.available, query.closed, first.slots, first.retained,
    SourceCurrentMemoMergeQueryMemos.effect_trans first.globals queryGlobal, ?_, ?_⟩
  · intro ambient term accepted
    exact ((query.meaning ambient term).mp accepted).2
  · intro ambient symbol terms part accepted satisfied selected present
    exact (query.meaning ambient part).mpr ⟨first.included ambient symbol terms part accepted satisfied selected, present⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial profiles and total headroom construct the complete shared leaf and both actual Work stages. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (record : Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : Shared (bits + 2))
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (stored : Stored (TargetRows record rows count depth bound) (max arity 1) bound before)
    (input : Value Symbol Guard) (inputRows inputArity inputBound : Nat)
    (available : Available before.checked.native.machine.heap input)
    (inputProfile : NodeShape inputRows inputArity input) (inputHeight : height input ≤ inputBound)
    (nodes : before.checked.native.machine.heap.nodes.next +
      nodeBudget record rows arity count depth bound inputRows inputArity inputBound before path ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next +
      edgeBudget record rows arity count depth bound inputRows inputArity inputBound before path ≤ 2 ^ (bits + 2))
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ result after next final requests,
      Receipt formulas solver next record values base path input before result after memos final ∧
      Stored (TargetRows record rows count depth bound) (max arity 1) bound after ∧
      NodeShape ((max (TargetRows record rows count depth bound) inputRows) *
        (max (TargetRows record rows count depth bound) inputRows)) (max (max (max arity 1) inputArity) 1) result ∧
      SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow input result ∧ height result ≤ inputBound ∧
      Trace before.checked.native.machine.heap after.checked.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget record rows arity count depth bound inputRows inputArity inputBound before path ∧
      edgeRequests requests ≤ edgeBudget record rows arity count depth bound inputRows inputArity inputBound before path ∧
      Capacity bits after.checked ∧
      after.checked.native.machine.heap.nodes.next ≤ before.checked.native.machine.heap.nodes.next +
        nodeBudget record rows arity count depth bound inputRows inputArity inputBound before path ∧
      after.checked.native.machine.heap.edges.next ≤ before.checked.native.machine.heap.edges.next +
        edgeBudget record rows arity count depth bound inputRows inputArity inputBound before path := by
  have initialNodes : before.checked.native.machine.heap.nodes.next +
      ForceN record rows arity count depth bound before path ≤ 2 ^ bits := by
    unfold nodeBudget at nodes
    omega
  have initialEdges : before.checked.native.machine.heap.edges.next +
      ForceE record rows arity count depth bound before path ≤ 2 ^ (bits + 2) := by
    unfold edgeBudget at edges
    omega
  obtain ⟨target, middle, forceInventory, current, firstRequests, first, middleStored,
    targetProfile, targetHeight, firstTrace, firstNodes, firstEdges, _middleCapacity, firstNodeSupply, firstEdgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinarySharedForceResources.complete formulas solver inventory bits record values base before
      ready known coherent active path member rows arity count depth bound profile lengthBound pathsBound heightBound stored
      initialNodes initialEdges memos valid
  have queryNodes : middle.checked.native.machine.heap.nodes.next +
      queryBudget record rows arity count depth bound inputRows inputArity inputBound ≤ 2 ^ bits := by
    unfold nodeBudget at nodes
    omega
  have queryEdges : middle.checked.native.machine.heap.edges.next +
      queryBudget record rows arity count depth bound inputRows inputArity inputBound ≤ 2 ^ (bits + 2) := by
    unfold edgeBudget at edges
    omega
  have targetCommon := NodeShape.mono target targetProfile (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have inputCommon := NodeShape.mono input inputProfile (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have commonHeight : max (height target) (height input) ≤ max bound inputBound :=
    Nat.max_le.mpr ⟨Nat.le_trans targetHeight (Nat.le_max_left _ _), Nat.le_trans inputHeight (Nat.le_max_right _ _)⟩
  have inputClosed := SourceCurrentAllocatedFiniteOrdinaryFinite.closed _
    ready.checked.semantic.ready.semantic.1.normal.facts.coherent input available (NodeShape.domain input inputProfile)
  obtain ⟨next, result, checked, queryRequests, query, finalNative, finalOutput, produced,
    _targetHeight, resultHeight, queryTrace, queryCount, capacity, queryNodeSupply, queryEdgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources.finite formulas solver forceInventory bits
      (max (TargetRows record rows count depth bound) inputRows) (max (max arity 1) inputArity) (max bound inputBound)
      target input middle.checked first.ready.checked first.ready.admitted middleStored.native middleStored.output
      first.available (first.extension.available input available) first.closed inputClosed targetCommon inputCommon
      commonHeight queryNodes queryEdges current first.globals.globals
  have full := of_parts first query
  have finalStored := SourceCurrentAllocatedFiniteOrdinarySharedProfiles.advance_stored middle checked middleStored finalNative finalOutput
  have joined := firstTrace.trans queryTrace
  have finalNodes := joined.next_le
  refine ⟨result, advance middle checked, next, current, firstRequests ++ queryRequests, full, finalStored,
    produced, ⟨NodeShape.domain result produced, resultHeight⟩, Nat.le_trans resultHeight inputHeight,
    joined, ?_, ?_, capacity, ?_, ?_⟩
  · rw [nodeRequests_append]
    change nodeRequests firstRequests + nodeRequests queryRequests ≤
      ForceN record rows arity count depth bound before path +
        queryBudget record rows arity count depth bound inputRows inputArity inputBound
    change nodeRequests queryRequests + edgeRequests queryRequests ≤
      queryBudget record rows arity count depth bound inputRows inputArity inputBound at queryCount
    omega
  · rw [edgeRequests_append]
    change edgeRequests firstRequests + edgeRequests queryRequests ≤
      ForceE record rows arity count depth bound before path +
        queryBudget record rows arity count depth bound inputRows inputArity inputBound
    change nodeRequests queryRequests + edgeRequests queryRequests ≤
      queryBudget record rows arity count depth bound inputRows inputArity inputBound at queryCount
    omega
  · change checked.native.machine.heap.nodes.next ≤ _
    unfold nodeBudget
    change middle.checked.native.machine.heap.nodes.next +
      queryBudget record rows arity count depth bound inputRows inputArity inputBound ≥ checked.native.machine.heap.nodes.next at queryNodeSupply
    omega
  · change checked.native.machine.heap.edges.next ≤ _
    unfold edgeBudget
    change middle.checked.native.machine.heap.edges.next +
      queryBudget record rows arity count depth bound inputRows inputArity inputBound ≥ checked.native.machine.heap.edges.next at queryEdgeSupply
    omega

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinarySharedLeafResources
