import MicroCFTA.SourcePruningEnumerationHeadReceiptLanguage

/-!
# Head meaning at the original sibling scan input

The aggregate native Post connects the actual head input to the scan input.
Both inputs retain the same captured enumeration cache.
The current structural gates remain explicit.
-/
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
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq (Value Symbol Constraint)]

/-- The actual head receipt restores the original scan input through its aggregate native Post. -/
theorem CompletedHeadReceipt.sound_scan_input
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv : Nat} {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached} {returnedInventory : Inventory} {returnedMemos : Memos}
    {scanInventory : Inventory} {scanCaller : Caller (bits + 2)} {scanMemos : Memos}
    (scanPacket : SourcePruningEnumerationRecursive.Packet formulas solver scanInventory
      scanCaller scanMemos metadata before)
    (prefixPost : SourceCurrentAllocatedPartialInvariant.Post formulas solver inventory
      scanCaller caller memos)
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved after returnedInventory returnedMemos)
    (canonical : Canonical before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
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
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment after.core →
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient scanCaller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment before.core ∧
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge (assignment uv) ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient (.node parentEntry storedEdges depth free) (assignment uv) ∧
        (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
        Fragments.fill assignment fragment = assignment uv := by
  obtain ⟨handle, parentEntry, storedEdges, depth, free, stored, decoded, selected, sound⟩ :=
    receipt.sound_current canonical nonterminal freshArity retained
  have captured := SourcePruningEnumerationRecursive.captured_post_semantics
    formulas solver scanInventory inventory scanCaller caller scanMemos memos metadata before scanPacket prefixPost
  refine ⟨handle, parentEntry, storedEdges, depth, free, stored, decoded, selected, ?_⟩
  intro ambient assignment satisfied
  obtain ⟨beforeHolds, edgeHolds, parentHolds, suspendedHolds, filled⟩ := sound ambient assignment satisfied
  exact ⟨(captured.2 ambient _ assignment).mp beforeHolds,
    edgeHolds, parentHolds, suspendedHolds, filled⟩

end MicroCFTA.SourcePruningEnumerationNativeHookResources
