import MicroCFTA.SourcePruningEnumerationHeadAdmission
import MicroCFTA.SourcePruningEnumerationCapturedEdgeDiagonalResourceSoundness
import MicroCFTA.SourcePruningEnumerationPacketLanguage

/-!
# Actual completed-head meaning from its own resource receipt

The receipt supplies its input parent and stable actual completed endpoint.
The original resource gates replace a universal range predicate.
Canonical, fresh arity and child retention remain explicit semantic gates.
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

/-- The actual head resource receipt restores its input language under the current structural gates. -/
theorem CompletedHeadReceipt.sound_current
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv : Nat} {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached} {returnedInventory : Inventory} {returnedMemos : Memos}
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
          ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment before.core ∧
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge (assignment uv) ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient (.node parentEntry storedEdges depth free) (assignment uv) ∧
        (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
        Fragments.fill assignment fragment = assignment uv := by
  obtain ⟨handle, parentEntry, storedEdges, depth, free, stored, decoded, selected⟩ := receipt.admission.source
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := receipt.admission.packet.valid
  obtain ⟨tries, residual, projected⟩ := receipt.projected
  have reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
    simpa only [SourcePruningEnumerationNativeBranchCompletion.edgeCost, receipt.allowed,
      projected, ↓reduceIte] using receipt.admission.reserved
  have pending := EnumerationReferences.pending_inputs before.core receipt.admission.packet.pending
    uv (some handle) scs stored
  refine ⟨handle, parentEntry, storedEdges, depth, free, stored, decoded, selected, ?_⟩
  exact SourcePruningEnumerationCapturedEdge.diagonal_complete_sound_current_resources
    seed formulas solver inventory caller before checkEmpty uv handle scs parentEntry storedEdges depth free
    edge roots memos receipt.admission.packet.context receipt.admission.ready stored decoded realized
    selected paths counts flags pending receipt.allowed tries residual projected receipt.admission.bounded
    reserved receipt.admission.known canonical nonterminal (freshArity tries residual projected)
    (retained tries residual projected) receipt.running

/-- The same head Post retains assignment meaning of the restored captured input cache. -/
theorem CompletedHeadReceipt.captured_semantics
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing} {before : Cached}
    {checkEmpty : Bool} {uv : Nat} {scs : List Suspended} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached} {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached saved after returnedInventory returnedMemos) :
    SourcePruningEnumerationRecursive.Packet formulas solver returnedInventory reached returnedMemos metadata before ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (residualMeaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient reached.checked.native.machine.heap) residualMeaning assignment before.core ↔
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap) residualMeaning assignment before.core :=
  SourcePruningEnumerationRecursive.captured_post_semantics formulas solver inventory returnedInventory
    caller reached memos returnedMemos metadata before receipt.admission.packet receipt.post

end MicroCFTA.SourcePruningEnumerationNativeHookResources
