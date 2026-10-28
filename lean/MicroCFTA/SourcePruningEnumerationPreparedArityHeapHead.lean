import MicroCFTA.SourcePruningEnumerationArityOrigins
import MicroCFTA.SourcePruningEnumerationPreparedHeadAdmission

/-!
# Prepared parent arity from its actual resident edge records

The prepared parent has its own availability proof.
Each selected edge is resident in that parent's physical heap.
The original source handle does not identify the prepared parent.
-/
namespace MicroCFTA.SourcePruningEnumerationArityOrigins
open InternedConstructorTemplates InternedProbeProvenance
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {Symbol : Type}

/-- An available ordinary parent's selected edge has the arity stored in its actual origin heap. -/
theorem Heap.parent_edge
    {state : State Symbol Constraint}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey}
    {edges : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    (heap : Heap state) (facts : InternedNestedFacts.Facts state)
    (parentAvailable : Available state (.node parentEntry edges depth free)) (selected : edge ∈ edges) :
    Fits edge.entry.key.constraint edge.children.length := by
  have resident : InternedEdgeResidency.EdgeResident state edge :=
    InternedEdgeResidency.resident_edges state facts.linked
      (.node parentEntry edges depth free) parentAvailable.resident edge selected
  exact Heap.edge state heap facts.coherent edge resident

end MicroCFTA.SourcePruningEnumerationArityOrigins

namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
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

/-- The prepared parent's actual physical edge records derive its selected head's own projected arity. -/
theorem CompletedHeadReceipt.freshArity_of_origin_heap
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : SourcePruningRecordTypes.Metadata Typing}
    {before : Cached} {checkEmpty : Bool} {uv handle : Nat} {scs : List Suspended}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey}
    {edges : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)}
    {savedQueries : SourceEndpointMemo.Memos} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (head : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata before
      checkEmpty uv handle scs parentEntry edges depth free edge bound fragment reached savedQueries after
      returnedInventory returnedMemos)
    (known : SourcePruningEnumerationArityOrigins.Heap caller.checked.native.machine.heap) :
    ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      arityAllows edge.children.length (suspendedVars before.core.counter tries) = true := by
  have own := SourcePruningEnumerationArityOrigins.Heap.parent_edge known
    head.admission.packet.context.ready.semantic.ready.semantic.1.normal.facts
    head.admission.parentAvailable head.admission.selected
  intro tries residual projected
  exact own tries residual projected before.core.counter

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
