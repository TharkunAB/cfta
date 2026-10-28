import MicroCFTA.SourcePruningEnumerationPreparedResumeZero
import MicroCFTA.SourcePruningEnumerationPreparedFiniteProjectionHeapContract

namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "ProjectionHeap" => Heap
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- Zero depth retains the original resources and projection at each actual caller. -/
theorem resume_zero_outcome_resources_projection_heap
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
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (initialProjection : ProjectionHeap caller.checked.native.machine.heap) :
    ∃ outcome : Result,
      (∀ workFuel, resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0
        metadata caller memos.query before next = outcome) ∧
      OutcomeResources formulas solver caller seed outcome ∧
      OutcomeProjectionHeap outcome := by
  obtain ⟨outcome, stable, resources⟩ := resume_zero_complete_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory caller memos
    before metadata next seed.2 (fun guard => guard ∈ seed.1) packet bounded known
  have originalResources : OutcomeResources formulas solver caller seed outcome := by
    refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, ?_⟩
    cases outcome with
    | complete outputs reached saved =>
        obtain ⟨callerSame, queriesSame, _bounded, _known, outputPackets⟩ := resources
        refine ⟨callerSame, queriesSame, ?_⟩
        intro output member
        obtain ⟨outputPacket, outputCaller, outputQueries, metadataSame, _cacheSame⟩ := outputPackets output member
        refine ⟨inventory, memos, metadata, ?_, outputQueries.symm, ?_, metadataSame, ?_, ?_⟩
        · simpa only [outputCaller] using Post.refl packet.context
        · simpa only [outputCaller] using outputPacket
        · simpa only [outputCaller] using bounded
        · simpa only [outputCaller] using known
    | stopped outputs reason endpoint =>
        obtain ⟨_selected, _nextSame, noOutputs, _reasonSame, endpointSame, _bounded, _known⟩ := resources
        refine ⟨Or.inr endpointSame, ?_⟩
        intro output member
        rw [noOutputs] at member
        exact False.elim (List.not_mem_nil member)
  have projected : OutcomeProjectionHeap outcome := by
    cases outcome with
    | complete outputs reached saved =>
        obtain ⟨callerSame, _queriesSame, _bounded, _known, outputPackets⟩ := resources
        refine ⟨?_, ?_⟩
        · simpa only [callerSame] using initialProjection
        · intro output member
          have outputCaller := (outputPackets output member).2.1
          simpa only [outputCaller] using initialProjection
    | stopped outputs reason endpoint =>
        obtain ⟨_selected, _nextSame, noOutputs, _reasonSame, endpointSame, _bounded, _known⟩ := resources
        refine ⟨?_, ?_⟩
        · simpa only [endpointSame] using initialProjection
        · intro output member
          rw [noOutputs] at member
          exact False.elim (List.not_mem_nil member)
  exact ⟨outcome, stable, originalResources, projected⟩

variable {bits : Nat}

/-- The literal zero-depth decision closes the original-input projection contract. -/
theorem zero_complete_with_projection_heap
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    CompleteWithProjectionHeap (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    _selectionMembers _selectionLength _initialMass _reserved initialProjection
  obtain ⟨outcome, running, resources, projected⟩ := resume_zero_outcome_resources_projection_heap
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
    caller memos before metadata (SourcePruningEnumerationRestart.decision stop order metadata before)
    seed packet bounded known initialProjection
  refine ⟨0, outcome, ?_, ?_, projected⟩
  · intro extra
    simpa only [run, Nat.zero_add] using running extra
  · simpa only [SourcePruningEnumerationPreparedReservation.final_zero] using resources

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
