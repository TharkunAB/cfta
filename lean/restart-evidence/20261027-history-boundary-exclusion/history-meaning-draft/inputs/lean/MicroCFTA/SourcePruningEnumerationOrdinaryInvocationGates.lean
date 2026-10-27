import MicroCFTA.SourcePruningEnumerationOrdinaryInvocation
import MicroCFTA.SourcePruningEnumerationOrdinaryReceiptLanguage

/-!
# Nonterminal buckets at the same actual ordinary entry

The invocation supplies its literal successful entry row.
The retained receipt names a successful row of that same action.
Their equality derives the bucket used by the semantic consumer.
-/
namespace MicroCFTA.SourcePruningEnumerationHookInvocation
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The same actual entry receipt has the invocation's nonterminal bucket. -/
theorem OrdinaryInvocation.entry_nonterminal
    {hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width}
    {checkEmpty : Bool} {r n p h k uv : Nat} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
    {caller : Caller width} {before : Cached} {queries : Queries}
    {fragment : Fragment} {reached : Caller width} {saved : Queries} {after : Cached}
    (invocation : OrdinaryInvocation hook checkEmpty r n p h k uv edgesOf caller before queries
      fragment reached saved after)
    {target handle : Nat} {bucket : List Suspended} {decoded : Node} {entered : Core}
    (entry : Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv)
      before.core (target, handle, bucket, decoded) entered) :
    bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
  obtain ⟨actualTarget, actualHandle, actualBucket, actualEntry, actualRows, actualDepth,
    actualFree, actualEntered, actualRead, nonterminal, _invoked⟩ := invocation
  change Except.ok ((target, handle, bucket, decoded), entered) ∈
    ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) at entry
  rw [actualRead] at entry
  have same := Except.ok.inj (List.mem_singleton.mp entry)
  have bucketSame : bucket = actualBucket := congrArg
    (fun packet : (Nat × Nat × List Suspended × Node) × Core => packet.1.2.2.1) same
  rw [bucketSame]
  exact nonterminal

end MicroCFTA.SourcePruningEnumerationHookInvocation

namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
universe u v
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq (Value Symbol Constraint)]


/-- The actual invocation derives the only removed semantic gate. -/
theorem CompletedHeadReceipt.sound_ordinary_callback_input_of_invocation
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv : Nat} {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached} {returnedInventory : Inventory} {returnedMemos : Memos}
    {scanInventory : Inventory} {scanCaller : Caller (bits + 2)} {scanMemos : Memos}
    {ordinaryBefore : Cached} {entryFuel entryTarget entryHandle : Nat}
    {entryValue : InternedConstructorTemplates.Value Symbol Constraint}
    (originalPacket : SourcePruningEnumerationRecursive.Packet formulas solver scanInventory
      scanCaller scanMemos metadata ordinaryBefore)
    (entry : Success
      (SourcePruningEnumerationEntry.enter scanCaller.checked.native.machine.heap entryFuel entryTarget)
      ordinaryBefore.core (uv, entryHandle, scs, entryValue) before.core)
    (scanPacket : SourcePruningEnumerationRecursive.Packet formulas solver scanInventory
      scanCaller scanMemos metadata before)
    (prefixPost : SourceCurrentAllocatedPartialInvariant.Post formulas solver inventory
      scanCaller caller memos)
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved after returnedInventory returnedMemos)
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {callbackFuel : Nat} {recorded : Metadata Typing}
    {callbackAfter : EnumerationState.State Symbol Constraint}
    (recording : Success
      (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv (.inl fragment))
      after.core (false, recorded) callbackAfter)
    (canonical : Canonical ordinaryBefore.core)
    {Output : Type u} {Reason : Type v}
    (hook : Fragments.Fragment Symbol → Caller (bits + 2) → SourceEndpointMemo.Memos → Cached →
      SourcePruningEnumerationNativeContinuations.HookResult Output Reason (bits + 2))
    (n p h k : Nat) (edgesOf : Value Symbol Constraint → List (EdgeValue Symbol Constraint))
    (invocation : SourcePruningEnumerationHookInvocation.OrdinaryInvocation hook checkEmpty
      entryFuel n p h k entryTarget edgesOf scanCaller ordinaryBefore scanMemos.query
      fragment reached saved after)
    (freshArity : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      arityAllows edge.children.length (EnumerationCorrectness.suspendedVars before.core.counter tries) = true)
    (retained : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ incoming bucket,
        (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
        (match incoming with | .node _ _ _ _ => True | _ => False) ∨
          bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) :
    ∃ (handle : Nat) (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
      before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free) ∧
      edge ∈ storedEdges ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient reached.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment callbackAfter →
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient scanCaller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment ordinaryBefore.core ∧
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge (assignment uv) ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient (.node parentEntry storedEdges depth free) (assignment uv) ∧
        (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
        Fragments.fill assignment fragment = assignment uv := by
  have nonterminal := invocation.entry_nonterminal entry
  exact CompletedHeadReceipt.sound_ordinary_callback_input originalPacket entry scanPacket prefixPost receipt
    recording canonical nonterminal freshArity retained

end MicroCFTA.SourcePruningEnumerationNativeHookResources
