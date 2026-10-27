import MicroCFTA.SourcePruningEnumerationFiniteHistoryContract

/-!
# Native Posts along the same actual resource history

The history records every prefix and completed-head native endpoint.
Their Posts compose with the tail Post at the full retained memo state.
The final query field belongs to the output's own recorded caller.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
variable [DecidableEq Node]

/-- The actual output history retains its full native Post and exact query field. -/
theorem ResourceHistory.native_post
    {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {checkEmpty : Bool} {edgesOf : Node → List (InternedConstructorTemplates.EdgeValue Symbol Constraint)}
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {workFuel recursiveFuel : Nat} {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos}
    {metadata : Metadata Typing} {before : Cached} {seed : Seed} {ceiling : Nat}
    {next : Option EnumerationSchedule.Next} {output : Output (bits + 2) Typing}
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output) :
    ∃ (returnedInventory : Inventory) (final : Memos),
      Post formulas solver returnedInventory caller output.caller final ∧ final.query = output.queries := by
  induction history with
  | stopped admission => exact ⟨_, _, Post.refl admission.1.context, rfl⟩
  | done admission => exact ⟨_, _, Post.refl admission.1.context, rfl⟩
  | parked _ _ _ _ ih => exact ih
  | ordinary _ _ _ prefixPost _ receipt _ _ _ ih =>
      obtain ⟨_entered, _handle, _scs, _decoded, _edge, _headSeed, _inherited,
        _headInventory, _headCaller, _headMemos, _headBound,
        _original, _entry, _enteredPacket, headPost, _captured, completed⟩ := receipt
      obtain ⟨returnedInventory, final, tailPost, queries⟩ := ih
      exact ⟨returnedInventory, final,
        ((prefixPost.trans headPost).trans completed.post).trans tailPost, queries⟩

end MicroCFTA.SourcePruningEnumerationRecursive
