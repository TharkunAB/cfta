import MicroCFTA.SourceFlatPruningRecursiveFiniteResources
import MicroCFTA.EnumerationFlatSemantics
import MicroCFTA.EnumerationFlatNativeIndex

/-!
# Resources at each actual flat recursive output

Each output keeps its own caller, full memos, metadata and cache.
The old packet supplies safety and dependency order at the related core.
The native cache certificate uses this output's actual native heap.
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

/-- The complete resource packet belongs to the actual output's caller and cache. -/
def OutputResources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing) : Prop :=
  ∃ (next : Inventory) (final : Memos) (metadata : Metadata Typing) (earlier : Cached),
    Post formulas solver next original output.caller final ∧ final.query = output.queries ∧
    SourcePruningEnumerationRecursive.Packet formulas solver next output.caller final metadata earlier ∧
    EnumerationFlatCached.Related output.cache earlier ∧
    (output.metadata = none ∨ output.metadata = some metadata) ∧
    EnumerationFlatNativeIndex.Correct output.caller.checked.native.machine.heap output.cache ∧
    Fits seed.2 output.caller.checked ∧
    Heap (fun guard => guard ∈ seed.1) output.caller.checked.native.machine.heap

/-- A related emitted output derives its complete packet at its own actual native endpoint. -/
theorem output_resources_of_related
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing)
    (earlier : SourcePruningEnumerationRecursive.Output width Typing)
    (resources : SourcePruningEnumerationRecursive.OutputResources formulas solver original seed earlier)
    (related : OutputRelated output earlier) :
    OutputResources formulas solver original seed output := by
  obtain ⟨next, final, metadata, post, queries, packet, shape, bounded, known⟩ := resources
  obtain ⟨metadataSame, caches, callerSame, queriesSame⟩ := related
  obtain ⟨roots, paths, storage, _realized, counts, flags⟩ := packet.valid
  refine ⟨next, final, metadata, earlier.cache, ?_, queries.trans queriesSame.symm,
    ?_, caches, ?_, ?_, ?_, ?_⟩
  · simpa only [callerSame] using post
  · simpa only [callerSame] using packet
  · simpa only [metadataSame] using shape
  · rw [callerSame]
    exact EnumerationFlatNativeIndex.correct_of_related caches earlier.caller.checked.native.machine.heap
      roots paths storage.aligned flags counts
  · simpa only [callerSame] using bounded
  · simpa only [callerSame] using known

/-- Output packets expose logical storage bounds, live roots and dependency levels on the flat core. -/
theorem output_state
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing)
    (resources : OutputResources formulas solver original seed output) :
    FlatUnionFind.Valid output.cache.core.representatives ∧
    output.cache.core.counter = output.cache.core.values.length ∧
    (∀ value ∈ output.cache.core.values, EnumerationCorrectness.SlotBound output.cache.core.counter value) ∧
    (∀ obligation ∈ output.cache.core.obligations,
      EnumerationCorrectness.FragmentBound output.cache.core.counter obligation.2) ∧
    (∀ uv value, output.cache.core.values[uv]? = some value →
      (value ≠ .eliminated ↔ FlatUnionFind.root output.cache.core.representatives uv = uv)) ∧
    ∃ (level : Nat → Nat) (frontier : Nat),
      FlatUnionFind.Satisfies output.cache.core.representatives level ∧
      (∀ uv fragment, output.cache.core.values[uv]? = some (.enumerated fragment) →
        level uv < frontier ∧ ∀ hole, EnumerationDependencies.HasHole fragment hole → level uv < level hole) ∧
      (∀ uv node scs, output.cache.core.values[uv]? = some (.unenumerated node scs) → level uv = frontier) := by
  obtain ⟨_next, _final, _metadata, earlier, _post, _queries, packet, related,
    _shape, correct, _bounded, _known⟩ := resources
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  refine ⟨related.core.valid, correct.aligned, ?_, ?_, ?_, level, frontier,
    (FlatUnionFind.represents_satisfies related.core.representatives level).mp ordered.classes, ?_, ?_⟩
  · simpa only [related.core.counter, related.core.values] using packet.safe.1.values
  · simpa only [related.core.counter, related.core.obligations] using packet.safe.1.guards
  · intro uv value stored
    have oldStored : earlier.core.values[uv]? = some value := by
      simpa only [related.core.values] using stored
    exact (packet.safe.2 uv value oldStored).trans (EnumerationFlatState.related_isRoot related.core uv)
  · simpa only [related.core.values] using ordered.expanded
  · simpa only [related.core.values] using ordered.pending

private theorem ordered_output_resources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed)
    {outputs : List (Output width Typing)}
    {earlier : List (SourcePruningEnumerationRecursive.Output width Typing)}
    (related : SourceFlatPruningNativeBranches.OrderedRelated OutputRelated outputs earlier)
    (valid : ∀ output ∈ earlier,
      SourcePruningEnumerationRecursive.OutputResources formulas solver original seed output) :
    ∀ output ∈ outputs, OutputResources formulas solver original seed output := by
  revert valid
  induction related with
  | nil =>
      intro _valid output member
      exact False.elim (List.not_mem_nil member)
  | cons head _tail ih =>
      intro valid output member
      rcases List.mem_cons.mp member with rfl | later
      · exact output_resources_of_related formulas solver original seed _ _
          (valid _ List.mem_cons_self) head
      · exact ih (fun value listed => valid value (List.mem_cons_of_mem _ listed)) output later

/-- Complete and stopped observations retain each emitted flat output's own resource packet. -/
theorem result_output_resources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed)
    (outcome : SourceFlatPruningNativeContinuations.HookResult
      (Output width Typing) (Failure width Typing) width)
    (earlier : SourcePruningEnumerationNativeContinuations.HookResult
      (SourcePruningEnumerationRecursive.Output width Typing)
      (SourcePruningEnumerationRecursive.Failure width Typing) width)
    (resources : SourcePruningEnumerationRecursive.OutcomeResources formulas solver original seed earlier)
    (related : ResultRelated outcome earlier) :
    ∀ output ∈ (match outcome with | .complete outputs _ _ | .stopped outputs _ _ => outputs),
      OutputResources formulas solver original seed output := by
  obtain ⟨_reached, _next, _final, _post, _bounded, _known, shape⟩ := resources
  cases outcome with
  | complete outputs caller queries =>
      cases earlier with
      | stopped _ _ _ => cases related
      | complete oldOutputs oldCaller oldQueries =>
          exact ordered_output_resources formulas solver original seed related.1 shape.2.2
  | stopped outputs reason endpoint =>
      cases earlier with
      | complete _ _ _ => cases related
      | stopped oldOutputs oldReason oldEndpoint =>
          exact ordered_output_resources formulas solver original seed related.1 shape.2

variable [DecidableEq Symbol] [DecidableEq Node]

/-- The complete original-input producer also certifies every output of each actual flat run. -/
theorem run_finite_complete_output_resources
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
          ∀ output ∈ (match flatOutcome with | .complete outputs _ _ | .stopped outputs _ _ => outputs),
            OutputResources formulas solver caller
              (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) output := by
  obtain ⟨bound, outcome, originalRunning, resources, flatRunning⟩ :=
    run_finite_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved
  refine ⟨bound, outcome, originalRunning, resources, ?_⟩
  intro flat related extra
  obtain ⟨flatOutcome, actual, compared⟩ := flatRunning flat related extra
  exact ⟨flatOutcome, actual, compared,
    result_output_resources formulas solver caller
      (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling)
      flatOutcome outcome resources compared⟩

end MicroCFTA.SourceFlatPruningRecursive
