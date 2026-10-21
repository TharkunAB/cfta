import MicroCFTA.SourceCurrentOuterInitialPrefix
import MicroCFTA.SourceCurrentOuterNativeStores
import MicroCFTA.SourceCurrentOuterUnionNormalHistory

namespace MicroCFTA.SourceCurrentOuterPrefixNativeStores
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
open SourceCurrentOuterPrefixInvariants (Inputs)
open SourceCurrentOuterInitialPrefix (forecast SeedTrace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List Guard × Profile
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "NativeSupport" => SourceCurrentNativeRequestPositivePositions.Support
local notation "History" => SourceCurrentNativeMuPublication.History
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "MergeSupport" => SourceCurrentMergePositivePosition.Support
local notation "UnionNormal" => SourceCurrentRequiredUnionNormal.UnionNormal
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
namespace Schedule
export SourceCurrentOuterInitialSchedule
  (parent rows descendants node walk parent_reserved rows_ge descendants_ge walk_ge)
end Schedule
variable {bits : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private def Stores [DecidableEq (EdgeKey Symbol Guard)] (state : Caller (bits + 2)) : Prop :=
  NativeSupport state.checked.native.machine.heap state.checked.native ∧
    Nonempty (History empty state.checked.native.machine.heap) ∧
    MergeStored state.merge ∧ MergeSupport state.merge ∧ UnionNormal state.checked.native.machine.heap

private theorem reservation [DecidableEq (EdgeKey Symbol Guard)]
    {inventory : Inventory} {budget : Nat} {request : EdgeRequest}
    {before : Caller (bits+2)} {memos : Memos} {profile : Profile} {alphabet : List Guard}
    (initial : Context formulas solver inventory before memos) (fits : Fits profile before.checked)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (uniform : SourceCurrentParentAlphabetReservation.UniformReserved bits budget alphabet profile) :
    SourceCurrentEdgeCallNumeric.Reserved bits budget request before profile := by
  generalize started : beginEdge request before = observation
  obtain ⟨handle,action,running⟩ := observation
  cases action with
  | evaluate captured =>
      obtain ⟨runningContext,owner,_key,_cell⟩ :=
        SourceCurrentAllocatedPartialCallSteps.edge_start formulas solver initial inherited resident started
      have checked := (beginEdge_components request before).1
      rw [started] at checked
      dsimp only at checked
      have bounded : Fits profile running.checked := by simpa only [checked] using fits
      have carrier : Carrier (fun guard => guard ∈ alphabet) running.checked.native.machine.heap := by simpa only [checked] using known
      have room := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet captured
        running memos runningContext profile bounded carrier owner.inherited owner.input uniform
      simpa only [SourceCurrentEdgeCallNumeric.Reserved,started] using room
  | ready | busy | absent => simp only [SourceCurrentEdgeCallNumeric.Reserved,started]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem one_step {g s r e p h m c n budget : Nat} {first last : Phase (bits + 2)}
    (actual : Step g s r e p h m c n budget first last)
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : Carrier (fun guard => guard ∈ seed.1) (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (forecast budget first seed).2)
    (stores : Stores (caller first)) : Stores (caller last) := by
  have unchanged := stores
  obtain ⟨supported,⟨causal⟩,merged,positiveMemo,normal⟩ := stores
  cases actual with
  | node_evaluate started =>
      rename_i request before handle running owner fuel
      have components := beginNode_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checked,merge,_fourth,_edges⟩ := components
      simpa only [Stores,SourceCurrentOuterActiveAncestry.caller,checked,merge] using unchanged
  | body_rows => exact unchanged
  | rows_edge done =>
      rename_i fuel inherited original before narrowed middle rest
      simp only [forecast,Schedule.rows] at room
      let parentSeed := Schedule.parent budget seed
      have parentRoom : Room bits parentSeed.2 := room.mono
        ((Schedule.descendants_ge fuel budget parentSeed).1.trans
          (Schedule.rows_ge fuel budget (Schedule.descendants fuel budget parentSeed)).1)
      have uniform := Schedule.parent_reserved bits budget seed parentRoom
      have resident := inputs.2 _ List.mem_cons_self
      have reserved := reservation formulas solver (request := ⟨inherited,original⟩) initial fits known inputs.1 resident uniform
      obtain ⟨next,final,receipt,_numeric,_carrier⟩ := SourceCurrentOuterEdgeGuardAlphabet.edge_call
        formulas solver inventory budget seed.1 ⟨inherited,original⟩ before memos initial frame seed.2 fits known
        inputs.1 resident uniform done
      exact SourceCurrentOuterNativeStores.edge_call formulas solver inventory next budget ⟨inherited,original⟩
        before middle memos final seed.2 narrowed initial frame fits inputs.1 resident reserved receipt
        normal supported causal merged positiveMemo
  | rows_tail edge children =>
      rename_i fuel inherited original before narrowed middle result after rest
      simp only [forecast,Schedule.rows] at room
      let parentSeed := Schedule.parent budget seed
      let tailSeed := Schedule.descendants fuel budget parentSeed
      have parentRoom : Room bits parentSeed.2 := room.mono
        ((Schedule.descendants_ge fuel budget parentSeed).1.trans (Schedule.rows_ge fuel budget tailSeed).1)
      have uniform := Schedule.parent_reserved bits budget seed parentRoom
      have resident := inputs.2 _ List.mem_cons_self
      have reserved := reservation formulas solver (request := ⟨inherited,original⟩) initial fits known inputs.1 resident uniform
      obtain ⟨next,final,receipt,numeric,carrier⟩ := SourceCurrentOuterEdgeGuardAlphabet.edge_call
        formulas solver inventory budget seed.1 ⟨inherited,original⟩ before memos initial frame seed.2 fits known
        inputs.1 resident uniform edge
      obtain ⟨middleSupport,⟨middleCausal⟩,middleMerged,middlePositive,middleNormal⟩ :=
        SourceCurrentOuterNativeStores.edge_call formulas solver inventory next budget ⟨inherited,original⟩
          before middle memos final seed.2 narrowed initial frame fits inputs.1 resident reserved receipt
          normal supported causal merged positiveMemo
      have descendantRoom : Room bits tailSeed.2 := room.mono (Schedule.rows_ge fuel budget tailSeed).1
      exact SourceCurrentOuterNativeStores.descendants formulas solver fuel parentSeed receipt.post.context
        receipt.frame numeric carrier (inputs.1.grows receipt.post.effects.grows.constraint_growth)
        receipt.semantic.resident descendantRoom middleNormal middleSupport middleCausal middleMerged
        middlePositive children
  | descendants_children => exact unchanged
  | children_walk => exact unchanged
  | walk_head => exact unchanged
  | walk_tail done =>
      rename_i fuel before combined index value result middle rest
      simp only [forecast,Schedule.walk] at room
      obtain ⟨receipt,returned,numeric,post⟩ := SourceCurrentInheritedNumeric.descent formulas solver
        inventory before memos combined index initial frame seed.2 fits inputs.1
      let nodeSeed := Schedule.node fuel budget seed
      have nodeRoom : Room bits nodeSeed.2 := room.mono (Schedule.walk_ge fuel budget nodeSeed).1
      exact SourceCurrentOuterNativeStores.node_call formulas solver fuel seed post.context returned numeric known
        receipt.inherited (post.effects.keeps.available _ (inputs.2 _ List.mem_cons_self)) nodeRoom
        normal supported causal merged positiveMemo done

private theorem prefixes {g s r e p h m c n budget : Nat} {first last : Phase (bits + 2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (actual : Reached g s r e p h m c n budget first last)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : Carrier (fun guard => guard ∈ seed.1) (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (forecast budget first seed).2)
    (stores : Stores (caller first)) : Stores (caller last) := by
  induction actual with
  | refl => exact stores
  | snoc earlier step ih =>
      obtain ⟨next,final,current,_trace,post,returned,numeric,carrier,currentInputs,
          _below,_guards,currentRoom,_bounds,_alphabet,_need⟩ :=
        SourceCurrentOuterInitialPrefix.reached formulas solver seed earlier initial frame fits known inputs room
      exact one_step formulas solver step current post.context returned numeric carrier currentInputs currentRoom ih

theorem reached
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {g s r e p h m c n budget : Nat} {first last : Phase (bits + 2)}
    {inventory : Inventory} {memos : Memos} (seed : Seed)
    (actual : Reached g s r e p h m c n budget first last)
    (initial : Context formulas solver inventory (caller first) memos)
    (frame : Frame formulas solver inventory (caller first).checked)
    (fits : Fits seed.2 (caller first).checked)
    (known : Carrier (fun guard => guard ∈ seed.1) (caller first).checked.native.machine.heap)
    (inputs : Inputs first) (room : Room bits (forecast budget first seed).2)
    (normal : UnionNormal (caller first).checked.native.machine.heap)
    (supported : NativeSupport (caller first).checked.native.machine.heap (caller first).checked.native)
    (causal : History empty (caller first).checked.native.machine.heap)
    (merged : MergeStored (caller first).merge) (positiveMemo : MergeSupport (caller first).merge) :
    ∃ next final current, SeedTrace actual seed current ∧
      Post formulas solver next (caller first) (caller last) final ∧
      Frame formulas solver next (caller last).checked ∧ Fits current.2 (caller last).checked ∧
      Carrier (fun guard => guard ∈ current.1) (caller last).checked.native.machine.heap ∧ Inputs last ∧
      Le (forecast budget last current).2 (forecast budget first seed).2 ∧
      (forecast budget last current).1 ⊆ (forecast budget first seed).1 ∧
      Room bits (forecast budget last current).2 ∧
      Fits (forecast budget first seed).2 (caller last).checked ∧
      Carrier (fun guard => guard ∈ (forecast budget first seed).1) (caller last).checked.native.machine.heap ∧
      SourceCurrentOuterInitialFuel.phaseNeed budget last current ≤
        SourceCurrentOuterInitialFuel.phaseNeed budget first seed ∧
      NativeSupport (caller last).checked.native.machine.heap (caller last).checked.native ∧
      Nonempty (History empty (caller last).checked.native.machine.heap) ∧
      MergeStored (caller last).merge ∧ MergeSupport (caller last).merge ∧
      UnionNormal (caller last).checked.native.machine.heap := by
  obtain ⟨next,final,current,trace,post,returned,numeric,carrier,currentInputs,
      below,guards,currentRoom,bounds,alphabet,need⟩ :=
    SourceCurrentOuterInitialPrefix.reached formulas solver seed actual initial frame fits known inputs room
  have stores := prefixes formulas solver seed actual initial frame fits known inputs room
    ⟨supported,⟨causal⟩,merged,positiveMemo,normal⟩
  exact ⟨next,final,current,trace,post,returned,numeric,carrier,currentInputs,
    below,guards,currentRoom,bounds,alphabet,need,stores⟩

end MicroCFTA.SourceCurrentOuterPrefixNativeStores

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentOuterPrefixNativeStores.reached
#print MicroCFTA.SourceCurrentOuterPrefixNativeStores.reached
#print axioms MicroCFTA.SourceCurrentOuterPrefixNativeStores.reached
