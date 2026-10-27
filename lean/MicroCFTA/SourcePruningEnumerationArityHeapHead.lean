import MicroCFTA.SourcePruningEnumerationArityOrigins
import MicroCFTA.SourcePruningEnumerationHeadAdmission

/-!
# Selected head arity from its actual certified edge-record heap

The current head receipt identifies its resident selected edge.
A key-dependent heap certificate supplies its projected arity.
The heap certificate must be derived from actual construction and execution.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual selected head obtains projected arity from its own certified physical edge records. -/
theorem CompletedHeadReceipt.freshArity_of_origin_heap
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : SourcePruningRecordTypes.Metadata Typing}
    {before : Cached} {checkEmpty : Bool} {uv : Nat} {scs : List Suspended}
    {edge : EdgeValue Symbol Constraint} {bound : Nat} {fragment : Fragments.Fragment Symbol}
    {reached : Caller (bits + 2)} {savedQueries : SourceEndpointMemo.Memos} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (head : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv scs edge bound fragment reached savedQueries after returnedInventory returnedMemos)
    (known : SourcePruningEnumerationArityOrigins.Heap caller.checked.native.machine.heap) :
    ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      arityAllows edge.children.length (suspendedVars before.core.counter tries) = true := by
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := head.admission.packet.valid
  obtain ⟨handle, parentEntry, edges, depth, free, stored, decoded, selected⟩ := head.admission.source
  obtain ⟨parent, parentLookup, available, _closed⟩ := realized uv handle scs stored
  have parentSame : parent = .node parentEntry edges depth free :=
    Option.some.inj (parentLookup.symm.trans decoded)
  subst parent
  have ready := head.admission.packet.context.ready.semantic.ready
  have selectedResident : InternedEdgeResidency.EdgeResident caller.checked.native.machine.heap edge :=
    InternedEdgeResidency.resident_edges caller.checked.native.machine.heap ready.semantic.1.normal.facts.linked
      (.node parentEntry edges depth free) available.resident edge selected
  have ownArity := SourcePruningEnumerationArityOrigins.Heap.edge
    caller.checked.native.machine.heap known ready.semantic.1.normal.facts.coherent edge selectedResident
  intro tries residual projected
  exact ownArity tries residual projected before.core.counter

end MicroCFTA.SourcePruningEnumerationNativeHookResources
