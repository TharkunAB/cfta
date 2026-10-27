import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationEdgeInputs
import MicroCFTA.EnumerationStratifiedTransport

namespace MicroCFTA.SourcePruningEnumerationOpaqueEvent
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The actual own-class allocation receipts retain the complete recursive packet. -/
theorem own_prefix_packet
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before after : Cached) (count : Nat)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (core : after.core = suspendedState count before.core)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller after) :
    SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata after := by
  have safe : Safe after.core := by
    rw [core]
    exact suspension_safe count before.core packet.safe
  have origin : EnumeratedOrigin before.core after.core := by
    rw [core]
    exact suspension_origin count before.core
  have protects : ∀ held fragment, before.core.values[held]? = some (.enumerated fragment) →
      EnumerationDriver.Protected held before.core after.core := by
    intro held fragment stored
    obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held fragment stored
    rw [core]
    exact EnumerationDriver.suspension_protected held count before.core packet.safe inside root
  have pending : EnumerationReferences.PendingReferences after.core := by
    intro held fragment stored
    have old := origin held fragment stored
    have incoming := packet.pending held fragment old
    change EnumerationReferences.ReferencesAllowed
      (fun slot => ¬UnionFind.SameClass after.core.representatives held slot) after.core
    rw [core, EnumerationConstruction.suspended_forest]
    exact EnumerationReferences.suspension_allowed _ count before.core incoming
  obtain ⟨level, frontier, beforeOrder⟩ := packet.ordered
  obtain ⟨nextLevel, ordered⟩ := EnumerationOrder.stratified_preserved before.core after.core
    safe level frontier beforeOrder origin protects
  refine ⟨packet.context, safe, pending, valid, ⟨nextLevel, frontier, ordered⟩, ?_⟩
  intro group member entry listed
  have old := packet.bounded group member entry listed
  rw [core, suspended_counter]
  omega

end MicroCFTA.SourcePruningEnumerationOpaqueEvent
