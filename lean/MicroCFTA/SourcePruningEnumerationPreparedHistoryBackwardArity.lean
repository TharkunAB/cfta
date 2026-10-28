import MicroCFTA.SourcePruningEnumerationPreparedHistoryPost
import MicroCFTA.SourcePruningEnumerationArityOrigins

/-!
# Earlier edge arity from the same actual native endpoint

Actual physical growth retains every earlier complete edge record.
An arity certificate for the reached heap therefore checks each earlier record.
The actual native Post fixes the same caller and full memo endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationArityOrigins
open InternedConstructorTemplates
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {Symbol : Type}

/-- Actual physical record growth transfers reached arity to every earlier edge record. -/
theorem Heap.of_grows {before after : State Symbol Constraint}
    (heap : Heap after) (growth : Grows before after) : Heap before := by
  intro key edge present
  exact heap key edge (growth.edgeRecords key edge present)

/-- Actual retained constructor effects transfer reached arity to the original heap. -/
theorem Heap.of_keeps {before after : State Symbol Constraint}
    (heap : Heap after) (keeps : SourceEqualityRequiredCache.Keeps before after) : Heap before :=
  heap.of_grows keeps.growth

end MicroCFTA.SourcePruningEnumerationArityOrigins

namespace MicroCFTA.SourceCurrentAllocatedPartialInvariant
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
open SourceCurrentAllocatedNativeInventoryState (Inventory)
variable {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]

/-- The actual endpoint Post transfers reached edge arity to its original native caller. -/
theorem Post.arity_before
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {before after : Caller width} {final : Memos}
    (post : Post formulas solver inventory before after final)
    (heap : ArityHeap after.checked.native.machine.heap) : ArityHeap before.checked.native.machine.heap :=
  heap.of_grows post.effects.keeps.growth

end MicroCFTA.SourceCurrentAllocatedPartialInvariant

namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open SourcePruningEnumerationRecursive (Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
variable [DecidableEq Node]

/-- The exact selected endpoint certificate checks its original caller's complete edge records. -/
theorem SelectedHistoryReceipt.arity_before
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {metadata : Metadata Typing} {checkEmpty : Bool} {workFuel uv : Nat}
    {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos} {before : Cached}
    {fragment : Fragments.Fragment Symbol} {reached : Caller (bits + 2)} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    (receipt : SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv
      inventory caller memos before fragment reached after returnedInventory returnedMemos)
    (heap : ArityHeap reached.checked.native.machine.heap) : ArityHeap caller.checked.native.machine.heap :=
  receipt.native_post.arity_before heap

/-- The same actual output's native arity certificate checks the entire input heap. -/
theorem ResourceHistory.arity_before
    {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
    {graph : EnumerationState.Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {checkEmpty : Bool} {edgesOf : Node → List (InternedConstructorTemplates.EdgeValue Symbol Constraint)}
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {workFuel recursiveFuel : Nat} {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos}
    {metadata : Metadata Typing} {before : Cached} {seed : Seed} {ceiling : Nat}
    {next : Option EnumerationState.Next} {output : Output (bits + 2) Typing}
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (heap : ArityHeap output.caller.checked.native.machine.heap) : ArityHeap caller.checked.native.machine.heap := by
  obtain ⟨_returnedInventory, _final, post, _queries⟩ := history.native_post
  exact post.arity_before heap

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
