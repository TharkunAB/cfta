import MicroCFTA.SourcePruningEnumerationSharedReceiptContinuation
import MicroCFTA.SourcePruningEnumerationSharedSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationSelectedPreparationResources

/-!
# Hook-aware selected dispatch after one actual preparation

The common preparation runs once after the Right callback. Ordinary rows
use the shared fold. Opaque and terminal values use the shared child worker.
Every native outcome retains its heap. Every result retains the entry rows.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedContinuations
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) × Core))
/-- Retain the entry rows and the literal native preparation outcome. -/
abbrev Preparation := Raw × Option (MergedSourceComparison.Result Symbol Constraint Node)
local notation "HookResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
local notation "Fold" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
universe u v
variable {Typing : Type} {width : Nat} {Output : Type u} {Reason : Type v}
/-- A native preparation failure retains its literal returned heap. -/
def preparation_endpoint (caller : Caller width) (queries : Queries) (observation : Preparation) :
    Caller width × Queries :=
  match observation.2 with
  | none => (caller, queries)
  | some native => (SourcePruningEnumerationSelectedValueCaller.advance caller native.state, queries)

/-- Preparation without a native result retains its entry endpoint. -/
theorem endpoint_entry (caller : Caller width) (queries : Queries) (raw : Raw) :
    preparation_endpoint caller queries (raw, none) = (caller, queries) := rfl

/-- Native success supplies its actual returned heap to the caller. -/
theorem endpoint_done (caller : Caller width) (queries : Queries) (raw : Raw) (value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) :
    preparation_endpoint caller queries (raw, some (.done value heap)) =
      (SourcePruningEnumerationSelectedValueCaller.advance caller heap, queries) := rfl

/-- Native failure supplies its actual fault heap to the caller. -/
theorem endpoint_failed (caller : Caller width) (queries : Queries) (raw : Raw)
    (fault : MergedSourceComparison.Fault) (heap : InternedConstructorTemplates.State Symbol Constraint) :
    preparation_endpoint caller queries (raw, some (.failed fault heap)) =
      (SourcePruningEnumerationSelectedValueCaller.advance caller heap, queries) := rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Prepare once and run the actual branch with its hook in source order. -/
noncomputable def run
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) : Preparation × Option (Fold Output Reason width) :=
  let observation := SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before
  (observation, match observation.2 with
    | some (.done value heap) =>
        match observation.1 with
        | [.ok ((target, _handle, scs, _decoded), entered)] =>
            some (if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
              SourcePruningEnumerationSharedReceiptContinuation.run hook
                (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
                (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
                  (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
                  (EnumerationExpandableIndex.frame entered before) queries)
            else match value with
              | parent@(.node ..) =>
                  SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run hook checkEmpty r n p h k target scs
                    (EnumerationExpandableIndex.frame entered before) (edgesOf parent)
                    (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
              | _ =>
                  SourcePruningEnumerationSharedReceiptContinuation.run hook
                    (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
                    (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
                      (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
                      (EnumerationExpandableIndex.frame entered before) queries))
        | _ => none
    | _ => none)

/-- Every actual entry row and native preparation outcome remains exact. -/
theorem preparation_readback
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    (run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries).1 =
      SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before := rfl

/-- Ordinary siblings run at each preceding hook's actual returned native endpoint. -/
theorem ordinary
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv target handle : Nat)
    (scs : List Suspended) (decoded : Node)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)], some (.done (.node entry edges depth free) heap)))
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      (([.ok ((target, handle, scs, decoded), entered)], some (.done (.node entry edges depth free) heap)),
        some (SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run hook checkEmpty r n p h k target scs
          (EnumerationExpandableIndex.frame entered before) (edgesOf (.node entry edges depth free))
          (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries)) := by
  simp only [run, observed, nonterminal, Bool.false_eq_true, ↓reduceIte]

/-- Terminal dispatch continues the exact actual child receipt at the captured target. -/
theorem terminal
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv target handle : Nat)
    (scs : List Suspended) (decoded value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)))
    (here : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true) :
    run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      (([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)),
        some (SourcePruningEnumerationSharedReceiptContinuation.run hook
          (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
          (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value
            (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
            (EnumerationExpandableIndex.frame entered before) queries))) := by
  simp only [run, observed, here, ↓reduceIte]

/-- Native preparation failure retains its actual fault heap and does not invoke a hook. -/
theorem failed
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (raw : Raw)
    (fault : MergedSourceComparison.Fault) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      (raw, some (.failed fault heap))) :
    run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      ((raw, some (.failed fault heap)), none) := by
  simp only [run, observed]

/-- Missing native preparation retains the complete actual entry observation. -/
theorem entry_only
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (entryFuel nativeFuel r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (raw : Raw)
    (observed : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before = (raw, none)) :
    run hook checkEmpty entryFuel nativeFuel r n p h k uv edgesOf caller before queries =
      ((raw, none), none) := by
  simp only [run, observed]

end MicroCFTA.SourcePruningEnumerationSharedPreparedContinuations
