import MicroCFTA.SourceSynthesisOriginalCheckedHereditarySharedCompletion
import MicroCFTA.SourceSynthesisOriginalFiniteDriver
import MicroCFTA.SourcePruningEnumerationSharedRecursive

/-!
# Shared enumeration at the same original worker return

The entry retains failed root observations and unencoded successful roots.
An encoded return starts the actual shared recursive driver at that root's
caller, fourth memo, Merge memo and current query memo. It retains the
literal startup cache and the complete bounded driver observation.

One accepted original completion supplies all root and startup facts.
No caller is initialized again. No native seed is reset at the returned
heap. Work fuel and recursive depth are observation parameters. This proof
does not establish driver convergence, adequate depth, final capacity,
language completeness, rank inverses or Haskell correspondence.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedDriver
open Cache EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedPartialInitialization (caller emptyValue globals)
open SourceSynthesisOriginalSharedRankCompletion (seed)
open SourceCurrentAllocatedNativeResourceForecast (Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceSynthesisOriginalFiniteDriver (initialMetadata startup)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "SharedReady" => SourceSynthesisNativeTypeSharedState.Ready
local notation "initialShared" => SourceCurrentAllocatedSharedTargetState.initial
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "History" => SourceSynthesisHereditaryClosedMemo.History
local notation "NodeFields" => SourceSynthesisHereditaryClosedMemo.NodeFields
local notation "ValueFields" => SourceSynthesisHereditaryProgramFields.ValueFields
local notation "envelope" => SourceCurrentSharedOuterRankEnvelope.envelope
local notation "count" => SourceCurrentPositiveQuotientCount.count
local notation "mass" => InternedValueMass.value
local notation "forecast" => SourceCurrentSharedOuterInitialPrefix.forecast
local notation "phaseNeed" => SourceCurrentSharedOuterInitialFuel.phaseNeed
local notation "cover" => SourceCurrentInitialSelectionForecast.cover
local notation "nodeCall" => SourceCurrentAllocatedSharedPartialWorker.nodeCall

/-- Keep the actual root endpoint and the exact shared driver observation. -/
inductive Outcome (width : Nat) (Typing : Type) : Type 1 where
  | failed (fault : SourceCurrentAllocatedSharedPartialWorker.Fault width)
      (caller : Caller width) (queries : Queries)
  | unencoded (value : Node) (caller : Caller width) (queries : Queries)
  | started (value : Node) (handle : Nat) (caller : Caller width) (queries : Queries)
      (cache : Cached)
      (observed : SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
        (SourcePruningEnumerationSharedRecursive.Output width Typing)
        (SourcePruningEnumerationSharedRecursive.Failure width Typing) width)

variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Start only from the actual encoded return and its current query memo. -/
noncomputable def start
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Guard))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveDepth : Nat)
    (metadata : Metadata Typing)
    (root : SourceCurrentAllocatedSharedPartialWorker.Outcome Node width) (queries : Queries) :
    Outcome width Typing :=
  match root with
  | .failed fault after => .failed fault after queries
  | .done value after =>
      match encodeNode value with
      | none => .unencoded value after queries
      | some handle =>
          let cached := startup value handle
          .started value handle after queries cached
            (SourcePruningEnumerationSharedRecursive.run holeKey fits admits graph templates
              checkEmpty edgesOf stop order workFuel recursiveDepth metadata after queries cached)

/-- Execute the literal shared root call before entering the shared recursive driver. -/
noncomputable def run
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Guard))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveDepth : Nat)
    (metadata : Metadata Typing)
    (fuel g s r e p h m c n budget : Nat) (request : NodeRequest) (before : Caller width)
    (queries : Queries) : Outcome width Typing :=
  start holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata
    (nodeCall fuel g s r e p h m c n budget request before) queries

/-- A failed root retains its full diagnostic and actual caller without driver execution. -/
theorem start_failed
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Guard))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveDepth : Nat)
    (metadata : Metadata Typing) (fault : SourceCurrentAllocatedSharedPartialWorker.Fault width)
    (after : Caller width) (queries : Queries) :
    start holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
      metadata (.failed fault after) queries = .failed fault after queries := rfl

/-- One original shared completion starts the literal driver at its same returned state. -/
theorem accepted
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : firstOrderRaw lib query signed = .ok expression)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (sourceGraph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (typing : Typing) (types openHoles : List Nat) (bits budget workFuel recursiveDepth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ _built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (SourceEqualityConstraintOrigins.guards (ordinarySymbols expression)) Cache.emptyState fields cache ∧
      let request : NodeRequest := ⟨emptyValue cache, value⟩
      let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
      let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (caller (bits + 2) cache heap)
      let need := phaseNeed budget first (seed heap)
      Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) →
      ∃ result after,
        SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
          output.1 need need need need need need need need need budget request
          (caller (bits + 2) cache heap) ∧
        (∀ fuel, output.1 ≤ fuel →
          nodeCall fuel need need need need need need need need need budget request
            (caller (bits + 2) cache heap) = .done result after) ∧
        (∀ fuel, output.1 ≤ fuel →
          SourceCurrentAllocatedSharedPartialWorkerRanges.nodeCall
            fuel need need need need need need need need need budget request
            (caller (bits + 2) cache heap)) ∧
        ∃ next final, ∃ graph : SourceCurrentAllocatedSharedPartialGraph.NodeCall budget request
            (caller (bits + 2) cache heap) result after,
          SourceCurrentAllocatedSharedPartialChecks.Checks
            (SourceCurrentAllocatedSharedPartialChecks.nodeCallTrace graph) ∧
          SourceCurrentAllocatedSharedPartialEndpointReads.NodeCallReads formulas solver graph globals final ∧
          Post formulas solver next (caller (bits + 2) cache heap) after final ∧
          Frame formulas solver next after.checked ∧
          Fits (forecast budget first (seed heap)).2 after.checked ∧
          SourceEqualityAnnotationHeap.Heap
            (fun guard => guard ∈ (forecast budget first (seed heap)).1) after.checked.native.machine.heap ∧
          Available after.checked.native.machine.heap result ∧
          SourceCurrentAllocatedPartialMemoSound.NodeLaw formulas solver request result ∧
          SharedReady lib (initialShared after.checked after.merge) ∧
          GuardHeap (Origin lib) after.checked.native.machine.heap ∧ History lib literal after ∧
          result.free = [] ∧ NodeFields lib literal request result ∧ ValueFields (Origin lib) literal result ∧
          ∃ handle,
            encodeNode result = some handle ∧ lookupNode after.checked.native.machine.heap handle = some result ∧
            Packet formulas solver next after final (initialMetadata typing types openHoles) (startup result handle) ∧
            EnumerationValidity.Canonical (startup result handle).core ∧
            (startup result handle).core.values[0]? = some (.unenumerated (some handle) []) ∧
            SourcePruningEnumerationPrefixAdmission.suspendedBound (startup result handle).core = 0 ∧
            EnumerationCanonicalWaiting.Correct (fun uv => uv) (startup result handle).core.values
              (startup result handle).waiting ∧
            (∀ slot, SourcePruningEnumerationNativeIndex.candidate after.checked.native.machine.heap
              (((startup result handle).core.values[slot]?).getD .eliminated) =
                some ((startup result handle).expandable slot)) ∧
            (∀ fuel, output.1 ≤ fuel →
              run holeKey fits admits sourceGraph templates checkEmpty InternedEdgeResidency.nodeEdges stop order
                workFuel recursiveDepth (initialMetadata typing types openHoles)
                fuel need need need need need need need need need budget request (caller (bits + 2) cache heap)
                final.query =
              .started result handle after final.query (startup result handle)
                (SourcePruningEnumerationSharedRecursive.run holeKey fits admits sourceGraph templates
                  checkEmpty InternedEdgeResidency.nodeEdges stop order workFuel recursiveDepth
                  (initialMetadata typing types openHoles) after final.query (startup result handle))) := by
  obtain ⟨fields, cache, value, heap, built, prepared, complete⟩ :=
    SourceSynthesisOriginalCheckedHereditarySharedCompletion.accepted
      lib query signed expression returned bits budget formulas solver
  let request : NodeRequest := ⟨emptyValue cache, value⟩
  let output := envelope budget (count (request.inherited.payload.getD []) value) (mass value) (seed heap)
  let first := SourceCurrentOuterCopiedWarmHit.Phase.node output.1 request (caller (bits + 2) cache heap)
  let need := phaseNeed budget first (seed heap)
  refine ⟨fields, cache, value, heap, built, prepared, ?_⟩
  change Room bits (cover [output.2.2.2] (forecast budget first (seed heap)).2) → _
  intro room
  obtain ⟨result, after, baseRanges, done, allRanges, next, final, actual, checks, reads, post,
      frame, bounded, known, available, law, ready, guards, history, closed, fields, recursiveFields⟩ := complete room
  obtain ⟨handle, encoded, decoded, packet, canonical, stored, suspended, waiting, flags⟩ :=
    SourcePruningEnumerationRecursive.initial_packet formulas solver next after final
      (initialMetadata typing types openHoles) result post.context available closed rfl
  refine ⟨result, after, baseRanges, done, allRanges, next, final, actual, checks, reads, post,
    frame, bounded, known, available, law, ready, guards, history, closed, fields, recursiveFields,
    handle, encoded, decoded, packet, canonical, stored, suspended, waiting, flags, ?_⟩
  intro fuel enough
  simp only [run, done fuel enough, start, encoded]

end MicroCFTA.SourcePruningEnumerationSharedPreparedDriver
