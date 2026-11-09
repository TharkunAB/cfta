import MicroCFTA.SourcePruningEnumerationSharedRecursive
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationSharedIncomingReservation

/-!
# Resources for actual shared recursive outcomes

The receipt predicates use the shared selected-edge result.
Failed finalization keeps its endpoint but is not an admitted continuation.
Each output retains its own packet and full native memo state.
A stopped hook retains its actual optional endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedNativeBranchCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies InternedConstructorTemplates
open SourcePruningEnumerationNativeBranchCompletion (CacheValid)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
variable {width : Nat}

/-- Admitted shared receipts retain finalized safety or their valid rejection cache. -/
def Admitted (target : Nat) : Receipt width → Prop
  | .complete fragment caller _ after =>
      CacheValid caller after ∧ Safe after.core ∧ FragmentBound after.core.counter fragment ∧
      after.core.values[target]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
      IsRoot after.core.representatives target
  | .rejected caller _ after => CacheValid caller after
  | .stopped _ (.ok (some []), caller, _, _outer, _waiting) (some after) => CacheValid caller after
  | .unhandled => True
  | .finalizeStopped _ _ _ _ => False
  | _ => False

/-- Each admitted continuation avoids references to every enumerated class. -/
def Pending : Receipt width → Prop
  | .complete _ _ _ after | .rejected _ _ after => EnumerationReferences.PendingReferences after.core
  | .stopped _ (.ok (some []), _, _, _outer, _waiting) (some after) =>
      EnumerationReferences.PendingReferences after.core
  | .unhandled => True
  | .finalizeStopped _ _ _ _ => False
  | _ => False

/-- Completed shared receipts retain counter growth and fragment dependency levels. -/
def FragmentHistory (before : EnumerationState.State Symbol Constraint) : Receipt width → Prop
  | .complete fragment _ _ after =>
      before.counter ≤ after.core.counter ∧ PendingFragment after.core fragment ∧
      ∀ level frontier, EnumerationOrder.Stratified before level frontier →
        ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1)
  | _ => True

/-- An earlier dependency order retains the same shared receipt history. -/
theorem fragmentHistory_transport (before after : EnumerationState.State Symbol Constraint)
    (growth : before.counter ≤ after.counter)
    (transport : ∀ level frontier, EnumerationOrder.Stratified before level frontier →
      ∃ nextLevel, EnumerationOrder.Stratified after nextLevel frontier)
    (receipt : Receipt width) (history : FragmentHistory after receipt) :
    FragmentHistory before receipt := by
  cases receipt with
  | complete fragment caller queries cache =>
      refine ⟨Nat.le_trans growth history.1, history.2.1, ?_⟩
      intro level frontier stratified
      obtain ⟨nextLevel, ordered⟩ := transport level frontier stratified
      exact history.2.2 nextLevel frontier ordered
  | unhandled | rejected _ _ _ | stopped _ _ _ | finalizeStopped _ _ _ _ => trivial

end MicroCFTA.SourcePruningEnumerationSharedNativeBranchCompletion

namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
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

/-- Every shared output retains its own packet, full memos and current resources. -/
def OutputResources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing) : Prop :=
  ∃ (next : Inventory) (final : Memos) (metadata : Metadata Typing),
    Post formulas solver next original output.caller final ∧ final.query = output.queries ∧
    Packet formulas solver next output.caller final metadata output.cache ∧
    (output.metadata = none ∨ output.metadata = some metadata) ∧
    Fits seed.2 output.caller.checked ∧
    Heap (fun guard => guard ∈ seed.1) output.caller.checked.native.machine.heap

/-- A shared recursive outcome retains every output and its actual optional endpoint. -/
def OutcomeResources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed)
    (outcome : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
      (Output width Typing) (Failure width Typing) width) : Prop :=
  ∃ (reached : Caller width) (next : Inventory) (final : Memos),
    Post formulas solver next original reached final ∧ Fits seed.2 reached.checked ∧
    Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap ∧
    match outcome with
    | .complete outputs caller queries =>
        caller = reached ∧ queries = final.query ∧
        ∀ output ∈ outputs, OutputResources formulas solver original seed output
    | .stopped outputs _ endpoint =>
        (endpoint = none ∨ endpoint = some (reached, final.query)) ∧
        ∀ output ∈ outputs, OutputResources formulas solver original seed output

variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {original middle : Caller width} {middleInventory : Inventory} {middleMemos : Memos}
variable {seed larger : Seed} {output : Output width Typing}
variable {outcome : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width}

/-- An earlier Post composes without changing a shared output or its memos. -/
theorem OutputResources.post
    (post : Post formulas solver middleInventory original middle middleMemos)
    (resources : OutputResources formulas solver middle seed output) :
    OutputResources formulas solver original seed output := by
  obtain ⟨next, final, metadata, outputPost, query, packet, shape, fits, known⟩ := resources
  exact ⟨next, final, metadata, post.trans outputPost, query, packet, shape, fits, known⟩

/-- An earlier Post composes with the actual shared endpoint and every output. -/
theorem OutcomeResources.post
    (post : Post formulas solver middleInventory original middle middleMemos)
    (resources : OutcomeResources formulas solver middle seed outcome) :
    OutcomeResources formulas solver original seed outcome := by
  obtain ⟨reached, next, final, reachedPost, fits, known, shape⟩ := resources
  refine ⟨reached, next, final, post.trans reachedPost, fits, known, ?_⟩
  cases outcome with
  | complete outputs caller queries =>
      obtain ⟨callerSame, querySame, outputsValid⟩ := shape
      exact ⟨callerSame, querySame, fun value member => (outputsValid value member).post post⟩
  | stopped outputs reason endpoint =>
      obtain ⟨endpointSame, outputsValid⟩ := shape
      exact ⟨endpointSame, fun value member => (outputsValid value member).post post⟩

/-- A larger current profile and carrier retain the same shared output packet. -/
theorem OutputResources.mono (numeric : Le seed.2 larger.2) (alphabet : seed.1 ⊆ larger.1)
    (resources : OutputResources formulas solver original seed output) :
    OutputResources formulas solver original larger output := by
  obtain ⟨next, final, metadata, outputPost, query, packet, shape, fits, known⟩ := resources
  refine ⟨next, final, metadata, outputPost, query, packet, shape, fits.mono numeric, ?_⟩
  intro key edge found
  exact alphabet (known key edge found)

/-- Current resource padding retains the optional endpoint of the same shared outcome. -/
theorem OutcomeResources.mono (numeric : Le seed.2 larger.2) (alphabet : seed.1 ⊆ larger.1)
    (resources : OutcomeResources formulas solver original seed outcome) :
    OutcomeResources formulas solver original larger outcome := by
  obtain ⟨reached, next, final, reachedPost, fits, known, shape⟩ := resources
  refine ⟨reached, next, final, reachedPost, fits.mono numeric, ?_, ?_⟩
  · intro key edge found
    exact alphabet (known key edge found)
  · cases outcome with
    | complete outputs caller queries =>
        obtain ⟨callerSame, querySame, outputsValid⟩ := shape
        exact ⟨callerSame, querySame, fun value member => (outputsValid value member).mono numeric alphabet⟩
    | stopped outputs reason endpoint =>
        obtain ⟨endpointSame, outputsValid⟩ := shape
        exact ⟨endpointSame, fun value member => (outputsValid value member).mono numeric alphabet⟩

end MicroCFTA.SourcePruningEnumerationSharedRecursive
