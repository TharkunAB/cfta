import MicroCFTA.SourcePruningEnumerationResourceHistoryMeaning
import MicroCFTA.SourcePruningEnumerationArityHeapHead

/-!
# Arity of a captured ordinary edge from its original scan heap

The same captured cache retains its pending native handle across siblings.
The initial packet realizes that handle before any sibling runs.
The actual head Post keeps this original readback at the later head caller.
The original scan heap therefore checks the exact selected edge's arity.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
variable [DecidableEq (Value Symbol Constraint)]

/-- The original ordinary input heap supplies the selected edge's arity without a later heap premise. -/
theorem OrdinaryHistoryReceipt.with_arity_from_scan_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {metadata : Metadata Typing} {checkEmpty : Bool} {workFuel uv : Nat}
    {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos} {before : Cached}
    {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : OrdinaryHistoryReceipt formulas solver metadata checkEmpty workFuel uv inventory caller memos
      before fragment reached after returnedInventory returnedMemos)
    (heap : SourcePruningEnumerationArityOrigins.Heap caller.checked.native.machine.heap) :
    OrdinaryHistoryArityReceipt formulas solver metadata checkEmpty workFuel uv inventory caller memos
      before fragment reached after returnedInventory returnedMemos := by
  obtain ⟨entered, handle, scs, decoded, edge, headSeed, inherited, headInventory, headCaller,
    headMemos, headBound, original, entry, enteredPacket, post, captured, completed⟩ := receipt
  obtain ⟨sourceHandle, parentEntry, sourceEdges, depth, free, stored, headLookup, selected⟩ :=
    completed.admission.source
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := enteredPacket.valid
  obtain ⟨oldParent, oldLookup, oldAvailable, _closed⟩ := realized uv sourceHandle scs stored
  have keptLookup := lookupNode_keeps caller.checked.native.machine.heap headCaller.checked.native.machine.heap
    post.effects.keeps sourceHandle oldParent oldLookup
  have sameParent : oldParent = .node parentEntry sourceEdges depth free :=
    Option.some.inj (keptLookup.symm.trans headLookup)
  subst oldParent
  have ready := enteredPacket.context.ready.semantic.ready
  have resident : InternedEdgeResidency.EdgeResident caller.checked.native.machine.heap edge :=
    InternedEdgeResidency.resident_edges caller.checked.native.machine.heap ready.semantic.1.normal.facts.linked
      (.node parentEntry sourceEdges depth free) oldAvailable.resident edge selected
  have own := SourcePruningEnumerationArityOrigins.Heap.edge caller.checked.native.machine.heap heap
    ready.semantic.1.normal.facts.coherent edge resident
  refine ⟨entered, handle, scs, decoded, edge, headSeed, inherited, headInventory, headCaller,
    headMemos, headBound, original, entry, enteredPacket, post, captured, completed, ?_⟩
  intro tries residual projected
  exact own tries residual projected entered.core.counter

end MicroCFTA.SourcePruningEnumerationRecursive
