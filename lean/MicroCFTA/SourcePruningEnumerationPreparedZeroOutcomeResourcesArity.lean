import MicroCFTA.SourcePruningEnumerationPreparedResumeZero
import MicroCFTA.SourcePruningEnumerationPreparedFiniteArityContract

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
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- Zero depth retains the original result and adds its same-endpoint arity receipt. -/
theorem resume_zero_outcome_resources_arity
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
    (arity : ArityHeap caller.checked.native.machine.heap) :
    ∃ outcome : Result,
      (∀ workFuel, resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0
        metadata caller memos.query before next = outcome) ∧
      OutcomeResources formulas solver caller seed outcome ∧
      OutcomeResourcesWithArity formulas solver caller seed outcome := by
  obtain ⟨outcome, stable, resources⟩ := resume_zero_complete_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory caller memos
    before metadata next seed.2 (fun guard => guard ∈ seed.1) packet bounded known
  have strengthened : OutcomeResourcesWithArity formulas solver caller seed outcome := by
    refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, arity, ?_⟩
    cases outcome with
    | complete outputs reached saved =>
        obtain ⟨callerSame, queriesSame, _bounded, _known, outputPackets⟩ := resources
        refine ⟨callerSame, queriesSame, ?_⟩
        intro output member
        obtain ⟨outputPacket, outputCaller, outputQueries, metadataSame, _cacheSame⟩ := outputPackets output member
        refine ⟨?_, ?_⟩
        · refine ⟨inventory, memos, metadata, ?_, outputQueries.symm, ?_, metadataSame, ?_, ?_⟩
          · simpa only [outputCaller] using Post.refl packet.context
          · simpa only [outputCaller] using outputPacket
          · simpa only [outputCaller] using bounded
          · simpa only [outputCaller] using known
        · simpa only [outputCaller] using arity
    | stopped outputs reason endpoint =>
        obtain ⟨_selected, _nextSame, noOutputs, _reasonSame, endpointSame, _bounded, _known⟩ := resources
        refine ⟨Or.inr endpointSame, ?_⟩
        intro output member
        rw [noOutputs] at member
        exact False.elim (List.not_mem_nil member)
  exact ⟨outcome, stable, strengthened.forget, strengthened⟩

variable {bits : Nat}

/-- The exact initial decision closes the stronger contract at zero recursive depth. -/
theorem zero_complete_with_arity
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    CompleteWithArity (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    _selectionMembers _selectionLength _initialMass _reserved arity
  obtain ⟨outcome, running, resources, strengthened⟩ := resume_zero_outcome_resources_arity
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
    caller memos before metadata (SourcePruningEnumerationRestart.decision stop order metadata before)
    seed packet bounded known arity
  refine ⟨0, outcome, ?_, ?_, ?_⟩
  · intro extra
    simpa only [run, Nat.zero_add] using running extra
  · simpa only [SourcePruningEnumerationPreparedReservation.final_zero] using resources
  · simpa only [SourcePruningEnumerationPreparedReservation.final_zero] using strengthened

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
