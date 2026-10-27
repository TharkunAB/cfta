import MicroCFTA.SourceFlatPruningRecursiveOutputOrigin
import MicroCFTA.SourceFlatPruningRecursiveOutputRendering

/-!
# Original-input completion with actual output certificates

One original producer chooses the work bound and stable result.
Every adequate actual flat run retains each output's own resource packet
and its actual stop or done frontier. Rendering retains its separate gates.
-/
namespace MicroCFTA.SourceFlatPruningRecursive
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
variable {Typing Key : Type} {width bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A metadata output retains the actual stop rule and all accepted remaining candidates. -/
theorem output_stop_frontier
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (output : Output width Typing) (metadata : Metadata Typing)
    (origin : OutputOrigin stop order output) (stopped : output.metadata = some metadata) :
    ∃ rule, stop = some rule ∧ SourceFlatPruningRestart.candidates output.cache ≠ [] ∧
      ∀ uv ∈ SourceFlatPruningRestart.candidates output.cache, rule metadata uv = true := by
  simp only [OutputOrigin, stopped] at origin
  exact (SourceFlatPruningOutputFrontier.decision_none_iff stop order metadata output.cache).mp origin

/-- A done output retains the decoded recursive frontier at its own native heap. -/
theorem output_done_frontier
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing)
    (resources : OutputResources formulas solver original seed output)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (origin : OutputOrigin stop order output) (completed : output.metadata = none) :
    ∀ (uv handle : Nat) (scs : List Suspended),
      output.cache.core.values[uv]? = some (.unenumerated (some handle) scs) →
        ∃ value, SourcePruningEnumerationNodes.lookupNode output.caller.checked.native.machine.heap handle = some value ∧
          InternedProbeProvenance.Available output.caller.checked.native.machine.heap value ∧ value.free = [] ∧
          MergedOrdinaryHeight.recursiveBoundary value = true ∧ scs = [] := by
  obtain ⟨_next, _final, _metadata, earlier, _post, _queries, packet, related,
    _shape, correct, _fits, _known⟩ := resources
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  simp only [OutputOrigin, completed] at origin
  exact (SourceFlatPruningOutputFrontier.candidates_nil_iff_native_frontier
    output.caller.checked.native.machine.heap output.cache earlier related correct realized).mp origin

variable [DecidableEq Symbol] [DecidableEq Node]

/-- Original admission derives one stable result and certifies every actual emitted flat output. -/
theorem run_finite_complete_output_certificates
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationRecursive.run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      SourcePruningEnumerationRecursive.OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      ∀ (flat : EnumerationFlatCached.Cached Symbol Constraint), EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ (flatOutcome : SourceFlatPruningNativeContinuations.HookResult
          (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
          run holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel metadata caller memos.query flat = flatOutcome ∧
          ResultRelated flatOutcome outcome ∧
          ∀ (output : Output (bits + 2) Typing), output ∈ SourceFlatPruningOutputFlow.hookOutputs flatOutcome →
            OutputResources formulas solver caller
              (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) output ∧
            OutputOrigin stop order output := by
  obtain ⟨bound, outcome, originalRunning, resources, flatRunning⟩ :=
    run_finite_complete_output_resources holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved
  refine ⟨bound, outcome, originalRunning, resources, ?_⟩
  intro flat related extra
  obtain ⟨flatOutcome, actual, compared, outputPackets⟩ := flatRunning flat related extra
  have origins := run_output_origin holeKey fits admits graph templates checkEmpty edgesOf stop order
    (bound + extra) recursiveFuel metadata caller memos.query flat
  rw [actual] at origins
  exact ⟨flatOutcome, actual, compared, fun output member =>
    ⟨outputPackets output member, origins output member⟩⟩

end MicroCFTA.SourceFlatPruningRecursive
