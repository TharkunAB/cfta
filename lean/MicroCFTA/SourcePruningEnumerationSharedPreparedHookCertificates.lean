import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
import MicroCFTA.SourcePruningEnumerationSharedHookCertificates

/-!
# Current packets and outputs for shared prepared recursion

The receipt predicates use the same actual shared edge result.
Output fields are identical in both shared recursive workers.
No ordinary recursive outcome or failure is converted here.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedNativeBranchCompletion (Admitted FragmentHistory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A completed shared receipt supplies the current packet before its actual callback. -/
theorem receipt_packet
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing)
    (originalCore : Core) (target : Nat) (fragment : Fragments.Fragment Symbol)
    (after : Cached) (level : Nat → Nat) (frontier : Nat)
    (context : SourceCurrentAllocatedPartialInvariant.Context formulas solver inventory caller memos)
    (admitted : Admitted target (.complete fragment caller memos.query after))
    (history : FragmentHistory originalCore (.complete fragment caller memos.query after))
    (pending : EnumerationReferences.PendingReferences after.core)
    (ordered : EnumerationOrder.Stratified originalCore level frontier)
    (bounded : ∀ group ∈ metadata.pending,
      SourcePruningPartialMatch.PendingBound originalCore.counter group) :
    Packet formulas solver inventory caller memos metadata after := by
  obtain ⟨nextLevel, afterOrder⟩ := history.2.2 level frontier ordered
  refine ⟨context, admitted.2.1, pending, admitted.1, ⟨nextLevel, frontier + 1, afterOrder⟩, ?_⟩
  intro group member entry listed
  exact Nat.lt_of_lt_of_le (bounded group member entry listed) history.1

/-- Prepared outputs use the common output fields and current packet contract. -/
abbrev OutputResources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing) : Prop :=
  SourcePruningEnumerationSharedRecursive.OutputResources formulas solver original seed output

variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {original middle : Caller width} {middleInventory : Inventory} {middleMemos : Memos}
variable {seed larger : Seed} {output : Output width Typing}

/-- An earlier actual Post retains the same output, cache and full memos. -/
theorem OutputResources.post
    (post : Post formulas solver middleInventory original middle middleMemos)
    (resources : OutputResources formulas solver middle seed output) :
    OutputResources formulas solver original seed output :=
  SourcePruningEnumerationSharedRecursive.OutputResources.post post resources

/-- Larger resource and carrier bounds retain the same output packet. -/
theorem OutputResources.mono (numeric : Le seed.2 larger.2) (alphabet : seed.1 ⊆ larger.1)
    (resources : OutputResources formulas solver original seed output) :
    OutputResources formulas solver original larger output :=
  SourcePruningEnumerationSharedRecursive.OutputResources.mono numeric alphabet resources

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
