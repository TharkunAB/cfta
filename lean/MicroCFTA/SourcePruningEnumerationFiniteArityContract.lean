import MicroCFTA.SourcePruningEnumerationFiniteContract
import MicroCFTA.SourcePruningEnumerationResumeZero
import MicroCFTA.SourcePruningEnumerationArityOrigins

/-!
# Finite recursive resources with their actual arity heaps

The stronger outcome retains the original reached caller and full memos.
It records arity at that endpoint even when no output is emitted.
Every emitted output also retains arity at its own caller.
This module proves only the zero-depth driver case.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState InternedConstructorTemplates
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
variable {Typing Key : Type} {width bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- The same aggregate receipt retains arity at its endpoint and every actual output caller. -/
def OutcomeResourcesWithArity
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (outcome : Result) : Prop :=
  ∃ (reached : Caller width) (next : Inventory) (final : Memos),
    Post formulas solver next original reached final ∧ Fits seed.2 reached.checked ∧
    Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap ∧
    ArityHeap reached.checked.native.machine.heap ∧
    match outcome with
    | .complete outputs caller queries =>
        caller = reached ∧ queries = final.query ∧
        ∀ output ∈ outputs, OutputResources formulas solver original seed output ∧
          ArityHeap output.caller.checked.native.machine.heap
    | .stopped outputs _ endpoint =>
        (endpoint = none ∨ endpoint = some (reached, final.query)) ∧
        ∀ output ∈ outputs, OutputResources formulas solver original seed output ∧
          ArityHeap output.caller.checked.native.machine.heap

/-- Forget only the new arity fields without changing the original aggregate witness. -/
theorem OutcomeResourcesWithArity.forget
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {original : Caller width} {seed : Seed} {outcome : Result}
    (resources : OutcomeResourcesWithArity formulas solver original seed outcome) :
    OutcomeResources formulas solver original seed outcome := by
  obtain ⟨reached, next, final, post, bounded, known, _arity, shape⟩ := resources
  refine ⟨reached, next, final, post, bounded, known, ?_⟩
  cases outcome with
  | complete outputs caller queries =>
      obtain ⟨callerSame, querySame, outputsValid⟩ := shape
      exact ⟨callerSame, querySame, fun output member => (outputsValid output member).1⟩
  | stopped outputs reason endpoint =>
      obtain ⟨endpointSame, outputsValid⟩ := shape
      exact ⟨endpointSame, fun output member => (outputsValid output member).1⟩

variable [DecidableEq Symbol] [DecidableEq Node]

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

/-- The original finite-driver contract adds initial arity and returns the same complete receipt with arity. -/
def CompleteWithArity
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
    SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling →
    ArityHeap caller.checked.native.machine.heap →
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      OutcomeResourcesWithArity formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome

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
  · simpa only [SourcePruningEnumerationFiniteReservation.final_zero] using resources
  · simpa only [SourcePruningEnumerationFiniteReservation.final_zero] using strengthened

end MicroCFTA.SourcePruningEnumerationRecursive
