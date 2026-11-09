import MicroCFTA.SourcePruningEnumerationSharedPreparedHookInduction

/-!
# Actual prepared shared recursive outcomes at depth zero

Every restart decision has its literal zero-depth result. The result
retains the current native state and full memos. Emitted outputs retain
their actual metadata and cache. Expansion retains its exhausted receipt.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- Every literal zero-depth decision keeps its exact endpoint and output packets. -/
theorem resume_zero_outcome_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (next : Option Next) (seed : Seed)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ outcome : Result,
      (∀ workFuel, resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0
        metadata caller memos.query before next = outcome) ∧
      OutcomeResources formulas solver caller seed outcome := by
  cases next with
  | none =>
      refine ⟨.complete [⟨some metadata, before, caller, memos.query⟩] caller memos.query,
        (fun _ => rfl), caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      have same := List.mem_singleton.mp member
      subst output
      exact ⟨inventory, memos, metadata, Post.refl packet.context, rfl, packet, Or.inr rfl, bounded, known⟩
  | some selected =>
      cases selected with
      | done =>
          refine ⟨.complete [⟨none, before, caller, memos.query⟩] caller memos.query,
            (fun _ => rfl), caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
          intro output member
          have same := List.mem_singleton.mp member
          subst output
          exact ⟨inventory, memos, metadata, Post.refl packet.context, rfl, packet, Or.inl rfl, bounded, known⟩
      | stuck =>
          refine ⟨.complete [] caller memos.query, (fun _ => rfl),
            caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
          intro output member
          exact (List.not_mem_nil member).elim
      | expand uv =>
          refine ⟨.stopped [] (.exhausted uv metadata before) (some (caller, memos.query)),
            (fun _ => rfl), caller, inventory, memos, Post.refl packet.context,
            bounded, known, Or.inr rfl, ?_⟩
          intro output member
          exact (List.not_mem_nil member).elim

variable {bits : Nat}

/-- The literal depth-zero worker supplies the base case for actual recursive induction. -/
theorem zero_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    _selectionMembers _selectionLength _initialMass _reserved
  obtain ⟨outcome, running, resources⟩ := resume_zero_outcome_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
    caller memos before metadata (SourcePruningEnumerationRestart.decision stop order metadata before)
    seed packet bounded known
  exact ⟨0, outcome, fun extra => running (0 + extra), resources⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
