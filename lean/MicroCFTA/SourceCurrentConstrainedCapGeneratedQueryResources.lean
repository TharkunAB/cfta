import MicroCFTA.SourceCurrentConstrainedCapCheckedJointComputedQuery
import MicroCFTA.SourceCurrentAllocatedNativeResourceForecast
import MicroCFTA.SourceCurrentAllocatedTargetQuery

/-!
# Generated query receipts under one numeric resource forecast

The initial forecast bounds the literal entry counters and causal payload
mass. The query constructs its own joint receipt. Its same physical trace
retains readiness, global tables, exact language, and the next forecast.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Stored" => InternedValueMassHeap.Stored
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
variable {width bits : Nat}

/-- Actual counters and every stored payload fit the supplied numeric forecast. -/
structure Fits (profile : Profile) (state : Checked width) : Prop where
  /-- The current node supply fits the forecast. -/
  nodes : state.native.machine.heap.nodes.next ≤ profile.nodes
  /-- The current edge supply fits the forecast. -/
  edges : state.native.machine.heap.edges.next ≤ profile.edges
  /-- The current domain supply fits the forecast. -/
  domains : state.native.machine.domains.next ≤ profile.domains
  /-- Every successful stored payload fits the causal mass bound. -/
  stored : Stored profile.mass state.native.machine.heap

/-- Initial numeric room bounds the actual query entry. -/
theorem Fits.room {profile : Profile} {state : Checked width} (fits : Fits profile state)
    (room : Room bits profile) :
    state.native.machine.heap.nodes.next < 2 ^ bits ∧
      state.native.machine.heap.edges.next ≤ 2 ^ (bits + 2) ∧
      state.native.machine.domains.next +
        2 ^ (state.native.machine.heap.nodes.next + state.native.machine.heap.nodes.next * state.native.machine.heap.nodes.next) <
        2 ^ (bits + 1) := by
  exact Room.mono room (show Le
    ⟨state.native.machine.heap.nodes.next, state.native.machine.heap.edges.next, state.native.machine.domains.next, profile.mass⟩
    profile from ⟨fits.nodes, fits.edges, fits.domains, Nat.le_refl _⟩)

/-- Larger numeric forecasts retain the same actual state. -/
theorem Fits.mono {first last : Profile} {state : Checked width} (fits : Fits first state) (larger : Le first last) :
    Fits last state :=
  ⟨Nat.le_trans fits.nodes larger.1, Nat.le_trans fits.edges larger.2.1,
    Nat.le_trans fits.domains larger.2.2.1, fits.stored.mono larger.2.2.2⟩

/-- One current inventory retains all laws needed by the next generated query. -/
structure Frame (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory) (state : Checked width) : Prop where
  /-- The same state retains all physical query invariants. -/
  ready : Ready state
  /-- Populated native cells retain current inventory admission. -/
  admitted : At formulas solver inventory state
  /-- The current heap retains its semantic and guard observations. -/
  context : Context Plain inventory.source state.native.machine
  /-- Completed native cells retain both joint laws. -/
  joint : SourceCurrentConstrainedCapCheckedJointCache.Stored Plain inventory.source state.native
  /-- Every allocated native cell retains its captured source witnesses. -/
  origins : SourceCurrentConstrainedCapCheckedJointOrigins.Stored inventory.source state.native

/-- Empty native tables derive the initial inventory and joint laws from physical readiness. -/
theorem Frame.initial (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (ready : Ready (⟨initial width machine, operations⟩ : Checked width))
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain machine.heap) (same : inventory.source = machine.heap) :
    Frame formulas solver inventory ⟨initial width machine, operations⟩ := by
  have growth : Grows inventory.source machine.heap := by rw [same]; exact grows_refl _
  have history : Extends inventory.source.nodes.issued machine.heap.nodes.issued := by rw [same]; exact extends_refl _
  exact ⟨ready, SourceCurrentAllocatedNativeInventoryState.initial inventory formulas solver width machine operations growth history,
    ⟨ready.good.native.machine, ready.semantic.ready.semantic, guards, growth, history⟩,
    SourceCurrentConstrainedCapCheckedJointCache.initial_stored Plain inventory.source width machine,
    SourceCurrentConstrainedCapCheckedJointOrigins.initial_stored inventory.source width machine⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The same actual return retains semantic receipts and its complete numeric forecast. -/
structure Receipt (profile : Profile) (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (after : Checked width) (memos : Memos) : Prop where
  /-- The actual query retains its joint laws and captured origins. -/
  joint : SourceCurrentConstrainedCapCheckedJointInventoryQuery.Receipt inventory depth formulas solver fuel left right before value after
  /-- The same trace retains exact language, readiness, and global tables. -/
  query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver inventory left right before value after memos
  /-- The literal returned state admits the next generated query. -/
  frame : Frame formulas solver inventory after
  /-- The initial forecast bounds all yielded instructions. -/
  count : fuel ≤ instructionBound profile.nodes profile.edges profile.mass
  /-- The computed fuel executes to the same result and checked state. -/
  done : execute (instructionBound profile.nodes profile.edges profile.mass + 1)
    (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after
  /-- The same returned state fits the next numeric forecast. -/
  fits : Fits (SourceCurrentAllocatedNativeResourceForecast.step profile) after
  /-- The returned payload fits the forecast mass schedule. -/
  mass : InternedValueMass.value value ≤
    massAfter (instructionBound profile.nodes profile.edges profile.mass) profile.mass

/-- Initial forecast room constructs a generated query with all laws on one actual trace. -/
theorem complete (profile : Profile) (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked (bits + 2)) (frame : Frame formulas solver inventory before)
    (fits : Fits profile before) (room : Room bits profile)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (leftCap : SourceCurrentConstrainedCap.Cap Plain depth left)
    (rightCap : SourceCurrentConstrainedCap.Cap Plain depth right)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ next fuel value after, Receipt profile depth formulas solver next fuel left right before value after memos := by
  have actualRoom := fits.room room
  let next := SourceCurrentAllocatedNativeInventoryRebase.extend inventory before.native.machine.heap frame.ready.good.native.machine.1
    frame.admitted.growth frame.admitted.history left right leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨fuel, value, after, joint, count, _done, stored, mass, nodes, edges, domains⟩ :=
    SourceCurrentConstrainedCapCheckedJointComputedQuery.generated_complete bits depth formulas solver inventory before
      frame.ready.good frame.admitted frame.ready.semantic frame.context frame.joint frame.origins
      frame.ready.scopedCache frame.ready.idle left right leftAvailable rightAvailable leftClosed rightClosed
      leftCap rightCap fits.stored actualRoom.1 actualRoom.2.1 actualRoom.2.2
  have effects := SourceCurrentAllocatedNativeTraceEffects.effects joint.trace frame.ready.good frame.ready.semantic
    frame.ready.costs (fun _ => trivial)
  obtain ⟨events, runs, silent, globals⟩ := SourceCurrentAllocatedNativeGlobalMemos.trace_memos joint.trace
    frame.ready.good frame.ready.semantic frame.ready.costs (fun _ => trivial) memos valid
  have ready : Ready after := ⟨effects.1, effects.2.1.ready.semantic, effects.2.1.ready.costs, joint.scopedCache, joint.idle⟩
  have query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right before value after memos :=
    ⟨.run joint.trace, ready, joint.inventoryAt, effects.2.1, effects.2.2, joint.result, joint.closed,
      joint.meaning, globals, events, runs, silent⟩
  have larger := SourceCurrentAllocatedNativeComputedBudget.instructionBound_mono fits.nodes fits.edges (Nat.le_refl profile.mass)
  have total : fuel ≤ instructionBound profile.nodes profile.edges profile.mass := Nat.le_trans count larger
  have exactResult := done_stable (fuel + 1)
    (instructionBound profile.nodes profile.edges profile.mass - fuel)
    (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before after value joint.done
  have sameFuel : fuel + 1 + (instructionBound profile.nodes profile.edges profile.mass - fuel) =
      instructionBound profile.nodes profile.edges profile.mass + 1 := by omega
  rw [sameFuel] at exactResult
  have massBound := SourceCurrentAllocatedRecursiveMassMonotone.massAfter_count_mono larger profile.mass
  have credits := SourceCurrentAllocatedRecursiveMassMonotone.credit_count_mono larger profile.mass
  refine ⟨next, fuel, value, after, joint, query,
    ⟨ready, joint.inventoryAt, joint.context, joint.stored, joint.origins⟩, total, exactResult, ?_, Nat.le_trans mass massBound⟩
  exact ⟨Nat.le_trans nodes (Nat.add_le_add fits.nodes credits),
    Nat.le_trans edges (Nat.add_le_add fits.edges credits), Nat.le_trans domains (Nat.add_le_add fits.domains larger),
    stored.mono massBound⟩

end MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources
