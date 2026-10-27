import MicroCFTA.SourcePruningEnumerationSelectedInvocationLanguage
import MicroCFTA.SourcePruningEnumerationHeadCheckedArity
import MicroCFTA.SourcePruningEnumerationDischargedRetention

/-!
# Selected receipt meaning from checked history and its discharged output

Actual checked construction supplies the current head's fresh arity.
The same head's false callback and remaining history supply child retention.
The original selected invocation theorem retains its complete semantic result.
Initial canonical storage and all other original inputs remain explicit.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationValidity EnumerationCompressionFrame EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
universe u v
variable {Typing Key : Type} {bits : Nat}
attribute [local instance] SourcePruningEnumerationEntry.entryMonadList
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Checked provenance and the same discharged output derive both original selected semantic gates. -/
theorem narrowed_receipt_sound_of_invocation_checked_output
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (checked : Core)
    (prepared : MergedSourceComparison.Result Symbol Constraint
      (Node × Option (EnumerateM Symbol Constraint Unit)))
    (ordinaryCaller : Caller (bits + 2)) (ordinaryMemos : Memos) (narrowed : Cached)
    (action : Option (List (Except Error (Unit × Core))))
    (updated : Metadata Typing) (rightCore : Core)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (canonical : Canonical before.core)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query))
    (actual : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before memos.query =
        .narrowed checked prepared ordinaryCaller ordinaryMemos.query action (some narrowed)
          (some [.ok ((false, updated), rightCore)]) none)
    (entryFuel target entryHandle : Nat) (scs : List Suspended) (entryValue : Node) (entered : Cached)
    (entry : Success
      (SourcePruningEnumerationEntry.enter ordinaryCaller.checked.native.machine.heap entryFuel uv)
      narrowed.core (target, entryHandle, scs, entryValue) entered.core)
    (enteredPacket : SourcePruningEnumerationRecursive.Packet formulas solver inventory
      ordinaryCaller ordinaryMemos updated entered)
    (seed : Seed) (inherited : Nat)
    (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos)
    (edge : EdgeValue Symbol Constraint) (headBound : Nat)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2))
    (saved : SourceEndpointMemo.Memos) (after : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos)
    (prefixPost : SourceCurrentAllocatedPartialInvariant.Post formulas solver headInventory
      ordinaryCaller headCaller headMemos)
    (receipt : SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt seed inherited
      formulas solver headInventory headCaller headMemos updated entered checkEmpty target scs edge headBound
      fragment reached saved after returnedInventory returnedMemos)
    (callbackFuel : Nat) (recorded : Metadata Typing) (callbackAfter : Core)
    (recording : Success
      (SourcePruningRecordTypes.recordTypes graph templates callbackFuel updated target (.inl fragment))
      after.core (false, recorded) callbackAfter)
    {Output : Type u} {Reason : Type v}
    (hook : Fragments.Fragment Symbol → Caller (bits + 2) → SourceEndpointMemo.Memos → Cached →
      SourcePruningEnumerationNativeContinuations.HookResult Output Reason (bits + 2))
    (n p h k : Nat)
    (invocation : SourcePruningEnumerationHookInvocation.OrdinaryInvocation hook checkEmpty
      entryFuel n p h k uv edgesOf ordinaryCaller narrowed ordinaryMemos.query
      fragment reached saved after)
    (sourceSymbol : Symbol) (original : Constraint) (storedField : SourceEqualityConstraintAllocation.Value)
    (sourceChildren : List Node) (operations : SourceEqualityConstraintMemoAllocation.State)
    (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (physical : SourceEqualityPhysicalPayload.read original.equalities = .ok storedField.payload)
    (storedReady : SourceEqualityConstraintAllocation.Ready operations.constraints storedField)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (sourceReady : SourceEqualityRequiredCache.Ready sourceHeap)
    (sourceAvailable : SourceEqualityMkEdgeAllocation.accepted original sourceChildren.length = true →
      InternedNestedProvenance.Values sourceHeap sourceChildren)
    (builtEdge : EdgeValue Symbol Constraint)
    (builtOperations : SourceEqualityConstraintMemoAllocation.State)
    (builtHeap : InternedConstructorTemplates.State Symbol Constraint)
    (constructed : SourceEqualityMkEdgeAllocation.build sourceSymbol storedField original.guard sourceChildren
      operations sourceHeap = (.ok builtEdge, builtOperations, builtHeap))
    (builtCaller : Caller (bits + 2))
    (builtAt : builtCaller.checked.native.machine.heap = builtHeap)
    (constructorPost : SourceCurrentAllocatedPartialInvariant.Post formulas solver headInventory
      builtCaller headCaller headMemos)
    (sameIdentity : builtEdge.entry.identity = edge.entry.identity)
    (recursiveFuel : Nat) (tailSeed : Seed) (tailCeiling : Nat)
    (output : SourcePruningEnumerationRecursive.Output (bits + 2) Typing)
    (callback : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates callbackFuel updated target
      (.inl fragment) after.core) = [.ok ((false, recorded), callbackAfter)])
    (tail : SourcePruningEnumerationRecursive.ResourceHistory
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver callbackFuel
      recursiveFuel returnedInventory reached returnedMemos recorded
      (EnumerationExpandableIndex.frame callbackAfter after) tailSeed tailCeiling
      (SourcePruningEnumerationRestart.decision stop order recorded
        (EnumerationExpandableIndex.frame callbackAfter after)) output)
    (discharged : SourcePruningEnumerationRendering.Discharged output.cache.core) :
    ∃ (handle : Nat) (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat)
      (free : List InternedBinderProtocol.Reference),
      narrowed.core.values[target]? = some (.unenumerated (some handle) scs) ∧
      lookupNode headCaller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free) ∧
      edge ∈ storedEdges ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient reached.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment callbackAfter →
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment before.core ∧
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment target) ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient (.node parentEntry storedEdges depth free) (assignment target) ∧
        (∀ sc ∈ scs, Suspended.Holds assignment (assignment target) sc) ∧
        Fragments.fill assignment fragment = assignment target := by
  have freshArity := SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt.freshArity_of_checked_build
    seed inherited formulas solver headInventory headCaller headMemos updated entered checkEmpty target scs edge
    headBound fragment reached saved after returnedInventory returnedMemos receipt
    sourceSymbol original storedField sourceChildren operations sourceHeap cached physical storedReady operationsValid
    sourceReady sourceAvailable builtEdge builtOperations builtHeap constructed builtCaller builtAt constructorPost
    sameIdentity
  have retained := SourcePruningEnumerationOpaqueEvent.completed_head_output_retained
    seed inherited formulas solver headInventory headCaller headMemos updated entered checkEmpty target scs edge
    headBound fragment reached saved after returnedInventory returnedMemos receipt
    holeKey fits admits graph templates edgesOf stop order callbackFuel recursiveFuel recorded callbackAfter
    tailSeed tailCeiling output callback tail discharged
  exact narrowed_receipt_sound_of_invocation
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv
    caller before memos checked prepared ordinaryCaller ordinaryMemos narrowed action updated rightCore
    packet canonical chosen valid actual entryFuel target entryHandle scs entryValue entered entry enteredPacket
    seed inherited headInventory headCaller headMemos edge headBound fragment reached saved after
    returnedInventory returnedMemos prefixPost receipt callbackFuel recorded callbackAfter recording
    hook n p h k invocation freshArity retained

end MicroCFTA.SourcePruningEnumerationSelectedStep
