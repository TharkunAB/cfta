import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetBudgetNumbers
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources

/-!
# Constructed Target folds from initial resource bounds

The proof constructs the head operand, its tail, and the actual query.
Each stage uses the preceding returned heap, memo, and input profile.
Initial cumulative headroom derives every next query capacity internally.
No completed Target or future range plan is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResources
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

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

private theorem operand_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {path : List Int}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (own : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo result after saved memos final) :
    Receipt formulas solver inventory values [path] before memo result after saved memos final := by
  have exactExtension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine :=
    ⟨own.effects.keeps.growth, own.effects.keeps.history, by
      simpa only [own.domains] using Cache.extends_refl before.native.machine.domains.table⟩
  refine ⟨own.ready, own.admitted, own.effects, exactExtension, own.stored, own.covered,
    own.available, own.closed, own.originals, own.retained,
    ⟨own.effects.keeps, own.effects.ready.semantic, own.effects.ready.costs, own.globals, own.unfolding, own.query⟩, ?_⟩
  intro _ proper ambient symbol terms part accepted selected
  exact own.included (proper path List.mem_cons_self) ambient symbol terms part accepted (selected path List.mem_cons_self)

private theorem cons_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory nextInventory finalInventory : Inventory} {values : List (Value Symbol Guard)}
    {seed path : List Int} {paths : List (List Int)} {before middle later after : Checked width}
    {memo current saved : Memo} {head tail result : Value Symbol Guard} {memos nextMemos lastMemos : Memos}
    (first : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo head middle current memos nextMemos)
    (rest : Receipt formulas solver nextInventory values (seed :: paths) middle current tail later saved nextMemos lastMemos)
    (query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver finalInventory head tail later result after lastMemos) :
    Receipt formulas solver finalInventory values (seed :: path :: paths) before memo result after saved memos lastMemos := by
  have effects := first.effects.trans (rest.effects.trans query.effects)
  have firstExtension : SourceRecursiveIntersectionKernel.Extension before.native.machine middle.native.machine :=
    ⟨first.effects.keeps.growth, first.effects.keeps.history, by simpa only [first.domains] using Cache.extends_refl before.native.machine.domains.table⟩
  have queryGlobal : SourceCurrentSubsumesQueryMemos.Effect later.native.machine.heap after.native.machine.heap lastMemos lastMemos :=
    ⟨query.effects.keeps, query.ready.semantic, query.ready.costs, query.globals, extends_refl _, rfl⟩
  have firstGlobal : SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap middle.native.machine.heap memos nextMemos :=
    ⟨first.effects.keeps, first.effects.ready.semantic, first.effects.ready.costs,
      first.globals, first.unfolding, first.query⟩
  refine ⟨query.ready, query.admitted, effects,
    firstExtension.trans (rest.extension.trans query.extension), rest.stored.grows query.effects.keeps,
    rest.covered, query.available, query.closed, ?_, extends_trans first.retained rest.retained,
    SourceCurrentMemoMergeQueryMemos.effect_trans firstGlobal
      (SourceCurrentMemoMergeQueryMemos.effect_trans rest.globals queryGlobal), ?_⟩
  · intro value member
    exact query.effects.keeps.available value (rest.originals value member)
  · intro _ proper ambient symbol terms part accepted selected
    exact (query.meaning ambient part).mpr
      ⟨first.included (proper path (by simp)) ambient symbol terms part accepted (selected path (by simp)),
        rest.included (by simp) (tail_all proper) ambient symbol terms part accepted (tail_all selected)⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Original forest limits and cumulative headroom construct the complete rotated fold. -/
theorem fold_complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    ∃ result after saved next final requests,
      ∃ actual : Fold values seed paths before memo result after saved,
        FoldReads formulas solver actual memos final ∧
        Receipt formulas solver next values (seed :: paths) before memo result after saved memos final ∧
        Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧
        NodeShape (Numbers.targetRows rows count depth bound paths.length) (max arity 1) result ∧ height result ≤ bound ∧
        Trace before.native.machine.heap after.native.machine.heap requests ∧
        nodeRequests requests ≤ Numbers.nodeBudget rows arity count depth bound paths.length ∧
        edgeRequests requests ≤ Numbers.edgeBudget rows arity count depth bound paths.length ∧ Capacity bits after ∧
        after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + Numbers.nodeBudget rows arity count depth bound paths.length ∧
        after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + Numbers.edgeBudget rows arity count depth bound paths.length := by
  induction paths generalizing inventory before memo memos with
  | nil =>
      obtain ⟨result, after, saved, final, requests, own, finalProfiles, resultProfile, resultHeight,
        trace, nodeCount, edgeCount, nodeSupply, edgeSupply⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOperandResources.complete formulas solver inventory seed values before memo
          ready admitted available physical profiles covered memos valid rows arity count depth bound profile
          lengthBound (pathsBound seed List.mem_cons_self) heightBound
      have nativeAfter := SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores.native own native output ready.idle
      have resultProfile' := NodeShape.mono result resultProfile (Nat.le_refl _) (Nat.le_max_left arity 1)
      simp only [List.length_nil, Numbers.nodeBudget_base, Numbers.edgeBudget_base] at nodes edges ⊢
      exact ⟨result, after, saved, inventory, final, requests, .nil (of_receipt own),
        .nil (operand := of_receipt own) own, operand_receipt own, finalProfiles, nativeAfter.1, nativeAfter.2.1,
        resultProfile', resultHeight, trace, nodeCount, edgeCount, ⟨by omega, by omega⟩, nodeSupply, edgeSupply⟩
  | cons path paths ih =>
      simp only [List.length_cons, Numbers.nodeBudget_step, Numbers.edgeBudget_step] at nodes edges ⊢
      obtain ⟨head, middle, current, currentMemos, firstRequests, first, firstProfiles, headProfile, headHeight,
        firstTrace, firstNodes, firstEdges, firstNodeSupply, firstEdgeSupply⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryOperandResources.complete formulas solver inventory path values before memo
          ready admitted available physical profiles covered memos valid rows arity count depth bound profile
          lengthBound (pathsBound path (by simp)) heightBound
      have nativeMiddle := SourceCurrentAllocatedFiniteOrdinaryOperandNativeStores.native first native output ready.idle
      obtain ⟨tail, later, saved, tailInventory, laterMemos, tailRequests, rest, tailReads, remaining,
        tailProfiles, nativeLater, outputLater, tailProfile, tailHeight, tailTrace, tailNodes, tailEdges,
        _tailCapacity, tailNodeSupply, tailEdgeSupply⟩ :=
        ih inventory middle current first.ready first.admitted first.originals first.stored firstProfiles
          nativeMiddle.1 nativeMiddle.2.1 first.covered currentMemos first.globals (tail_all pathsBound) (by omega) (by omega)
      have leftProfile := NodeShape.mono head headProfile
        (Nat.le_max_left (Numbers.operandRows rows count depth bound) (Numbers.targetRows rows count depth bound paths.length))
        (Nat.le_max_left arity 1)
      have rightProfile := NodeShape.mono tail tailProfile
        (Nat.le_max_right (Numbers.operandRows rows count depth bound) (Numbers.targetRows rows count depth bound paths.length))
        (Nat.le_refl (max arity 1))
      obtain ⟨next, result, after, queryRequests, query, finalNative, finalOutput, resultProfile,
        _leftHeight, rightHeight, queryTrace, queryCount, _capacity, _queryNodes, _queryEdges⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryTargetQueryResources.finite formulas solver tailInventory bits
          (max (Numbers.operandRows rows count depth bound) (Numbers.targetRows rows count depth bound paths.length))
          (max arity 1) bound head tail later remaining.ready remaining.admitted nativeLater outputLater
          (remaining.effects.keeps.available head first.available) remaining.available first.closed remaining.closed
          leftProfile rightProfile (by omega) (by omega) (by omega) laterMemos remaining.globals.valid
      have trace : Trace before.native.machine.heap after.native.machine.heap
          (firstRequests ++ (tailRequests ++ queryRequests)) := firstTrace.trans (tailTrace.trans queryTrace)
      have nodeCount : nodeRequests (firstRequests ++ (tailRequests ++ queryRequests)) ≤
          Numbers.nodeBudget rows arity count depth bound (paths.length + 1) := by
        rw [nodeRequests_append, nodeRequests_append, Numbers.nodeBudget_step]
        omega
      have edgeCount : edgeRequests (firstRequests ++ (tailRequests ++ queryRequests)) ≤
          Numbers.edgeBudget rows arity count depth bound (paths.length + 1) := by
        rw [edgeRequests_append, edgeRequests_append, Numbers.edgeBudget_step]
        omega
      have supplies := trace.next_le
      have resultProfile' : NodeShape (Numbers.targetRows rows count depth bound (paths.length + 1)) (max arity 1) result := by
        simpa only [Numbers.targetRows_step, Nat.max_assoc, Nat.max_self] using resultProfile
      exact ⟨result, after, saved, next, laterMemos, firstRequests ++ (tailRequests ++ queryRequests),
        .cons (of_receipt first) rest query.actual,
        .cons (operand := of_receipt first) (rest := rest) (step := query.actual) first tailReads query,
        cons_receipt first remaining query, tailProfiles, finalNative, finalOutput,
        resultProfile', by omega, trace, nodeCount, edgeCount, ⟨by omega, by omega⟩, by omega, by omega⟩

/-- An empty target makes no requests; a nonempty target charges its rotated fold. -/
def nodeBudget (rows arity count depth bound : Nat) : Nat → Nat
  | 0 => 0
  | paths + 1 => Numbers.nodeBudget rows arity count depth bound paths

/-- Edge headroom uses the same actual path count and zero cost for an empty target. -/
def edgeBudget (rows arity count depth bound : Nat) : Nat → Nat
  | 0 => 0
  | paths + 1 => Numbers.edgeBudget rows arity count depth bound paths

/-- Empty returns no rows; every nonempty result uses its derived fold envelope. -/
def outputRows (rows count depth bound : Nat) : Nat → Nat
  | 0 => 0
  | paths + 1 => Numbers.targetRows rows count depth bound paths

/-- Initial forest bounds construct the whole Target and every reached query receipt. -/
theorem target_complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    (nodes : before.native.machine.heap.nodes.next + nodeBudget rows arity count depth bound paths.length ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget rows arity count depth bound paths.length ≤ 2 ^ (bits + 2)) :
    ∃ result after saved next final requests,
      ∃ actual : Target values paths before memo result after saved,
        TargetReads formulas solver actual memos final ∧
        Receipt formulas solver next values paths before memo result after saved memos final ∧
        Profiles saved ∧ NativeStored after.native ∧ OutputStored after.native ∧
        NodeShape (outputRows rows count depth bound paths.length) (max arity 1) result ∧ height result ≤ bound ∧
        Trace before.native.machine.heap after.native.machine.heap requests ∧
        nodeRequests requests ≤ nodeBudget rows arity count depth bound paths.length ∧
        edgeRequests requests ≤ edgeBudget rows arity count depth bound paths.length ∧ Capacity bits after ∧
        after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget rows arity count depth bound paths.length ∧
        after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget rows arity count depth bound paths.length := by
  cases paths with
  | nil =>
      have initial : SourceCurrentConjunctionRowsAllocation.Ready (SourceCurrentAllocatedNativeEffects.physical before) :=
        ⟨ready.semantic, ready.costs, ready.good.operations, ready.good.fields⟩
      have receipt : Receipt formulas solver inventory values [] before memo .empty before memo memos memos :=
        ⟨ready, admitted, .refl _ initial, .refl _, physical, covered, empty_available _, rfl, available,
          extends_refl _, ⟨SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready,
            ready.semantic, ready.costs, valid, extends_refl _, rfl⟩,
          fun nonempty => False.elim (nonempty rfl)⟩
      simp only [List.length_nil, nodeBudget, edgeBudget, outputRows, Nat.add_zero] at nodes edges ⊢
      exact ⟨.empty, before, memo, inventory, memos, [], .nil, .nil, receipt, profiles, native, output,
        True.intro, Nat.zero_le _, .refl _, Nat.zero_le _, Nat.zero_le _, ⟨nodes, edges⟩,
        Nat.le_refl _, Nat.le_refl _⟩
  | cons seed paths =>
      simpa only [List.length_cons, nodeBudget, edgeBudget, outputRows] using
        (fold_complete formulas solver inventory bits values seed paths before memo ready admitted available physical profiles
          native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResources
