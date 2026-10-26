import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourceCurrentAllocatedTargetCallerResources

/-!
# Native query resources for the captured recursive packet

One query constructs its returned packet from current facts. A completed
query history uses one reservation from its original profile. The history
records actual native queries. It does not execute the recursive driver.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionCode
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Reserved step advance)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
variable {Typing : Type} {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]

/-- Initial reservation constructs one query and retains the captured packet for later queries. -/
theorem query_complete (count : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : Metadata Typing) (before : Cached) (left right : Value Symbol Constraint)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (fits : Fits profile caller.checked) (reserved : Reserved bits profile (count + 1))
    (leftAvailable : Available caller.checked.native.machine.heap left)
    (rightAvailable : Available caller.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ next value after,
      next.source = caller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right caller.checked value after memos ∧
      Post formulas solver next caller
        (SourceCurrentAllocatedPartialState.advance caller after caller.fourth caller.merge) memos ∧
      Packet formulas solver next
        (SourceCurrentAllocatedPartialState.advance caller after caller.fourth caller.merge) memos metadata before ∧
      SourceEqualityNativeDemand.execute (instructionBound profile.nodes profile.edges profile.mass + 1)
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) caller.checked = .done value after ∧
      Fits (step profile) after ∧ Reserved bits (step profile) count := by
  obtain ⟨next, value, after, source, roots, receipt, post, done, bounded, _mass⟩ :=
    SourceCurrentAllocatedTargetQuery.finite_caller_resources profile formulas solver inventory caller
      left right memos packet.context fits reserved.head leftAvailable rightAvailable leftClosed rightClosed
  exact ⟨next, value, after, source, roots, receipt, post, captured_post packet post,
    done, bounded, reserved.tail⟩

/-- A finite sequence records complete native query returns at their literal caller states. -/
inductive QueryHistory : Nat → Caller (bits + 2) → Caller (bits + 2) → Prop where
  /-- An empty query history retains its caller. -/
  | nil (caller : Caller (bits + 2)) : QueryHistory 0 caller caller
  /-- The next query starts at the complete returned caller of its predecessor. -/
  | cons {count fuel : Nat} {caller final : Caller (bits + 2)} {after : Checked (bits + 2)}
      {left right value : Value Symbol Constraint}
      (leftAvailable : Available caller.checked.native.machine.heap left)
      (rightAvailable : Available caller.checked.native.machine.heap right)
      (leftClosed : left.free = []) (rightClosed : right.free = [])
      (done : SourceEqualityNativeDemand.execute fuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) caller.checked = .done value after)
      (rest : QueryHistory count
        (SourceCurrentAllocatedPartialState.advance caller after caller.fourth caller.merge) final) :
      QueryHistory (count + 1) caller final

/-- One original reservation preserves the full captured packet across every recorded query. -/
theorem query_history_resources
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (metadata : Metadata Typing) (before : Cached) (memos : Memos)
    {count : Nat} {caller final : Caller (bits + 2)} (history : QueryHistory count caller final)
    (inventory : Inventory) (profile : Profile)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (fits : Fits profile caller.checked) (reserved : Reserved bits profile count) :
    ∃ next, Post formulas solver next caller final memos ∧
      Packet formulas solver next final memos metadata before ∧ Fits (advance profile count) final.checked := by
  induction history generalizing inventory profile with
  | nil => exact ⟨inventory, Post.refl packet.context, packet, fits⟩
  | @cons count fuel caller final after left right value leftAvailable rightAvailable leftClosed rightClosed done rest ih =>
      obtain ⟨middle, _source, _roots, _receipt, post, bounded, _mass⟩ :=
        SourceCurrentAllocatedTargetQuery.raw_done_caller_resources profile fuel formulas solver inventory
          caller after left right value memos packet.context fits reserved.head
          leftAvailable rightAvailable leftClosed rightClosed done
      obtain ⟨next, finalPost, finalPacket, finalFits⟩ :=
        ih middle (step profile) (captured_post packet post) bounded reserved.tail
      exact ⟨next, post.trans finalPost, finalPacket, finalFits⟩

end MicroCFTA.SourcePruningEnumerationRecursive
