import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualNativeWork
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetProfiles

/-!
# Constructor counts from the same supplied Target reads

Each operand records its actual projection and memo-aware Merge Work.
The fold counts its head, actual shorter tail, and checked query in order.
Profiles and returned stores come from those same actual prefixes.
No constructor headroom, future capacity, or callback count is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualTargetWork
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode (Budget)
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
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "P" => SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forestRows
local notation "N" => SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.nodeBudget
local notation "E" => SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.edgeBudget
local notation "Envelope" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.envelope
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

private theorem merge_counted {clear : Guard → Bool} {input output : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo}
    (actual : SourceCurrentAllocatedMerge.Merge clear input before memo output after saved)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (available : Available before.native.machine.heap input) (rows arity bound : Nat)
    (profile : NodeShape rows arity input) (heightBound : height input ≤ bound) :
    Profiles saved ∧ NodeShape (Envelope rows bound) arity output ∧ height output ≤ bound ∧
      Budget before.native.machine.heap after.native.machine.heap (N rows arity bound) (E rows arity bound) := by
  cases actual with
  | done call =>
      have counted := SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer.call_budget call.graph
        ready.semantic ready.costs physical profiles available
      have outputProfile := counted.2.2.2.1.2 rows arity bound profile heightBound
      exact ⟨counted.2.2.1, outputProfile.1, Nat.le_trans outputProfile.2 heightBound,
        counted.2.2.2.2 rows arity bound profile heightBound⟩

/-- A supplied complete operand retains its stores and bounds its literal projection and Merge requests. -/
theorem operand_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {path : List Int}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathBound : path.length ≤ depth) (heightBound : childrenHeight values ≤ bound) :
    Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧
      NodeShape (Numbers.operandRows rows count depth bound) arity result ∧ height result ≤ bound ∧
      ∃ requests, Trace before.native.machine.heap after.native.machine.heap requests ∧
        nodeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryOperandResources.nodeBudget rows arity count depth bound ∧
        edgeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryOperandResources.edgeBudget rows arity count depth bound := by
  have retained := SourceCurrentAllocatedFiniteOrdinaryTargetProfiles.operand_receipt receipt ready available physical profiles
    native output rows arity count depth bound profile lengthBound pathBound heightBound
  obtain ⟨projected, middle, current, projection, merged⟩ := receipt.actual
  have produced := SourceCurrentAllocatedFiniteOrdinaryProjectionProfile.forest_uniform projection.graph
    ready.semantic available profile count depth bound lengthBound pathBound heightBound
  obtain ⟨earlier, firstTrace, firstNodes, firstEdges, _nodeSupply, _edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryProjectionReservations.forest projection.graph ready.semantic available
      (ChildrenShape.domain values profile)
  obtain ⟨_finalProfiles, _finalProfile, _finalHeight, later, lastTrace, lastNodes, lastEdges⟩ :=
    merge_counted merged.actual projection.ready (physical.grows projection.effects.keeps) profiles projection.available
      (P rows count depth) arity bound produced.1 produced.2
  have originalCounts := SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.children values profile bound heightBound
  have originalNodes := Nat.le_trans originalCounts.1
    (Nat.mul_le_mul_right (SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds.nodeCount rows arity bound) lengthBound)
  refine ⟨retained.1, retained.2.1, retained.2.2.1, retained.2.2.2.1, retained.2.2.2.2,
    earlier ++ later, firstTrace.trans lastTrace, ?_, ?_⟩
  · rw [nodeRequests_append]
    unfold SourceCurrentAllocatedFiniteOrdinaryOperandResources.nodeBudget
    omega
  · rw [edgeRequests_append, firstEdges]
    simpa only [SourceCurrentAllocatedFiniteOrdinaryOperandResources.edgeBudget, Nat.zero_add] using lastEdges

/-- Supplied ordered fold reads bound the same cumulative Work without a reservation premise. -/
theorem fold
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Fold values seed paths before memo result after saved} (reads : FoldReads formulas solver actual memos final) :
    Ready before → Values before.native.machine.heap values → PhysicalStored before.native.machine.heap memo →
      Profiles memo → NativeStored before.native → OutputStored before.native →
      ∀ rows arity count depth bound, ChildrenShape rows arity values → values.length ≤ count →
      (∀ path ∈ seed :: paths, path.length ≤ depth) → childrenHeight values ≤ bound →
      Ready after ∧ Effects (physical before) (physical after) ∧ PhysicalStored after.native.machine.heap saved ∧
      Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧ Available after.native.machine.heap result ∧
      NodeShape (Numbers.targetRows rows count depth bound paths.length) (max arity 1) result ∧ height result ≤ bound ∧
      ∃ requests, Trace before.native.machine.heap after.native.machine.heap requests ∧
        nodeRequests requests ≤ Numbers.nodeBudget rows arity count depth bound paths.length ∧
        edgeRequests requests ≤ Numbers.edgeBudget rows arity count depth bound paths.length := by
  induction reads with
  | nil receipt =>
      intro ready available physical profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound
      obtain ⟨merged, nativeAfter, outputAfter, shaped, bounded, requests, work, nodes, edges⟩ :=
        operand_receipt receipt ready available physical profiles native output rows arity count depth bound profile lengthBound
          (pathsBound _ List.mem_cons_self) heightBound
      exact ⟨receipt.ready, receipt.effects, receipt.stored, merged, nativeAfter, outputAfter, receipt.available,
        NodeShape.mono _ shaped (Nat.le_refl _) (Nat.le_max_left _ _), bounded, requests, work, nodes, edges⟩
  | cons receipt remaining query ih =>
      intro ready available physical profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound
      obtain ⟨headMerged, headNative, headOutput, headShape, headHeight, firstRequests, firstTrace, firstNodes, firstEdges⟩ :=
        operand_receipt receipt ready available physical profiles native output rows arity count depth bound profile lengthBound
          (pathsBound _ (by simp)) heightBound
      obtain ⟨tailReady, tailEffects, tailPhysical, tailMerged, tailNative, tailOutput, _tailAvailable, tailShape, tailHeight,
        tailRequests, tailTrace, tailNodes, tailEdges⟩ :=
        ih receipt.ready receipt.originals receipt.stored headMerged headNative headOutput rows arity count depth bound
          profile lengthBound (tail_all pathsBound) heightBound
      obtain ⟨finalNative, finalOutput, resultShape, _leftHeight, rightHeight, queryRequests, queryTrace, queryCount,
        _nodeSupply, _edgeSupply⟩ := SourceCurrentAllocatedFiniteOrdinaryActualNativeWork.counted
          (max (Numbers.operandRows rows count depth bound) _) (max arity 1) bound query.actual tailReady tailNative tailOutput
          (NodeShape.mono _ headShape (Nat.le_max_left _ _) (Nat.le_max_left _ _))
          (NodeShape.mono _ tailShape (Nat.le_max_right _ _) (Nat.le_refl _)) (by omega)
      refine ⟨query.ready, receipt.effects.trans (tailEffects.trans query.effects), tailPhysical.grows query.effects.keeps,
        tailMerged, finalNative, finalOutput, query.available, ?_, Nat.le_trans rightHeight tailHeight,
        firstRequests ++ (tailRequests ++ queryRequests), firstTrace.trans (tailTrace.trans queryTrace), ?_, ?_⟩
      · simpa only [List.length_cons, Numbers.targetRows_step, Nat.max_assoc, Nat.max_self] using resultShape
      · rw [nodeRequests_append, nodeRequests_append, Numbers.nodeBudget_step]
        omega
      · rw [edgeRequests_append, edgeRequests_append, Numbers.edgeBudget_step]
        omega

/-- Supplied whole Target reads retain strong stores and expose their exact request bounds. -/
theorem target_reads
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Target values paths before memo result after saved} (reads : TargetReads formulas solver actual memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (pathsBound : ∀ path ∈ paths, path.length ≤ depth) (heightBound : childrenHeight values ≤ bound) :
    Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧
      NodeShape (SourceCurrentAllocatedFiniteOrdinaryTargetResources.outputRows rows count depth bound paths.length)
        (max arity 1) result ∧ height result ≤ bound ∧
      ∃ requests, Trace before.native.machine.heap after.native.machine.heap requests ∧
        nodeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryTargetResources.nodeBudget rows arity count depth bound paths.length ∧
        edgeRequests requests ≤ SourceCurrentAllocatedFiniteOrdinaryTargetResources.edgeBudget rows arity count depth bound paths.length ∧
        after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next +
          SourceCurrentAllocatedFiniteOrdinaryTargetResources.nodeBudget rows arity count depth bound paths.length ∧
        after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next +
          SourceCurrentAllocatedFiniteOrdinaryTargetResources.edgeBudget rows arity count depth bound paths.length := by
  cases reads with
  | nil => exact ⟨profiles, native, output, True.intro, Nat.zero_le _, [], .refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | cons remaining =>
      obtain ⟨_, _, _, merged, nativeAfter, outputAfter, _, shaped, bounded, requests, work, nodes, edges⟩ :=
        fold remaining ready available physical profiles native output rows arity count depth bound profile lengthBound pathsBound heightBound
      have supplies := work.next_le
      exact ⟨merged, nativeAfter, outputAfter, shaped, bounded, requests, work, nodes, edges, by omega, by omega⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualTargetWork
