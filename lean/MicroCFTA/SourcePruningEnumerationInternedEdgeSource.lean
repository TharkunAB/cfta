import MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations
import MicroCFTA.InternedEdgeResidency
import MicroCFTA.SourcePruningEnumerationRecursive

namespace MicroCFTA.SourcePruningEnumerationInternedEdgeSource
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) ×
  EnumerationState.State Symbol Constraint))
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
section
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Use the literal stored row order in the existing ordinary wrapper. -/
noncomputable def run
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationNativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv : Nat) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    Raw × Option (SourcePruningEnumerationNativeContinuations.Result Output Reason width) :=
  SourcePruningEnumerationNativeOrdinaryContinuations.run hook checkEmpty r n p h k uv
    InternedEdgeResidency.nodeEdges caller before queries

/-- The actual entry selects the literal rows for its ordinary nonterminal fold. -/
theorem run_eq
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationNativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv : Nat) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    run hook checkEmpty r n p h k uv caller before queries =
      let raw := ExceptT.run
        (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core)
      (raw, match raw with
        | [.ok ((target, _handle, scs, .node _ edges _ _), entered)] =>
            if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
            else some (SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k target scs
              (EnumerationExpandableIndex.frame entered before) edges caller queries)
        | _ => none) := by
  unfold run SourcePruningEnumerationNativeOrdinaryContinuations.run
  dsimp only
  congr 1
  generalize ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) = rows
  cases rows with
  | nil => rfl
  | cons first rest =>
      cases first with
      | error _ => rfl
      | ok pair =>
          obtain ⟨⟨_target, _handle, _scs, parent⟩, _entered⟩ := pair
          cases parent <;> cases rest <;> rfl

end
/-- Every structural tail retains the canonical row origin of the captured parent. -/
theorem ordinary_tail_origin
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) (offset : Nat) :
    ∀ edge ∈ edges.drop offset,
      edge ∈ InternedEdgeResidency.nodeEdges (.node entry edges depth free) := by
  intro edge present
  change edge ∈ edges
  induction offset generalizing edges with
  | zero => exact present
  | succ _offset ih =>
      cases edges with
      | nil => cases present
      | cons first rest => exact List.mem_cons_of_mem first (ih rest present)

variable {Typing Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Fix the same concrete getter throughout the existing native recursive worker. -/
noncomputable def worker
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    SourcePruningEnumerationNativeContinuations.HookResult
      (SourcePruningEnumerationRecursive.Output width Typing)
      (SourcePruningEnumerationRecursive.Failure width Typing) width :=
  SourcePruningEnumerationRecursive.run holeKey fits admits graph templates checkEmpty
    InternedEdgeResidency.nodeEdges stop order workFuel recursiveFuel metadata caller queries before

/-- The worker starts with the actual restart decision and the concrete getter. -/
theorem worker_eq
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    worker holeKey fits admits graph templates checkEmpty stop order workFuel recursiveFuel
      metadata caller queries before =
      SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty
        InternedEdgeResidency.nodeEdges stop order workFuel recursiveFuel metadata caller queries before
        (SourcePruningEnumerationRestart.decision stop order metadata before) := rfl

end MicroCFTA.SourcePruningEnumerationInternedEdgeSource
