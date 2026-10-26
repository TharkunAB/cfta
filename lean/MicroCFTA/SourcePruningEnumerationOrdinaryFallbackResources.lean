import MicroCFTA.SourcePruningEnumerationOrdinaryForecastResources

/-!
# Actual ordinary-entry fallback observations

Entry still runs for a recursive value or a terminal suspended bucket. The
ordinary wrapper retains that exact raw result and supplies no scan. Native
resources and the caller stay unchanged.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
universe u v
variable {Typing : Type} {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Current invariants derive the exact fallback entry and its returned packet at a common work bound. -/
theorem fallback_complete_resources
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv handle : Nat) (scs : List Suspended) (value : Node)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some value)
    (fallback : match value with
      | .node .. => scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      | _ => True)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : Fits profile caller.checked) (known : Heap property caller.checked.native.machine.heap) :
    ∃ (bound : Nat) (entered : Cached),
      (∀ extra, ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
        (bound + extra) uv before.core) = [.ok ((uv, handle, scs, value), entered.core)]) ∧
      EnumerationDriver.RenderStable before.core entered.core ∧
      entered.core.counter = before.core.counter ∧ entered.core.values = before.core.values ∧
      entered.expandable = before.expandable ∧ entered.waiting = before.waiting ∧
      Packet formulas solver inventory caller memos metadata entered ∧
      (∀ extra (hook : Fragment → Caller width → Queries → Cached →
          SourcePruningEnumerationNativeContinuations.HookResult Output Reason width),
        run hook checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          uv edgesOf caller before memos.query =
            ([.ok ((uv, handle, scs, value), entered.core)], none)) ∧
      Post formulas solver inventory caller caller memos ∧ Fits profile caller.checked ∧
      Heap property caller.checked.native.machine.heap := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨bound, actualValue, enteredCache, entryRun, lookup, _available, _closed, counter, values,
    sameFlags, sameWaiting, _enteredStored, _enteredReady, _protected, enteredPaths, enteredRealized,
    enteredCounts, enteredFlags, _bucketBounded, _retained, stable⟩ :=
    SourcePruningEnumerationSelectedEntry.complete caller.checked.native.machine.heap before uv handle scs roots
      ready stored realized paths counts flags
  have same : actualValue = value := Option.some.inj (lookup.symm.trans decoded)
  subst actualValue
  have enteredPacket : Packet formulas solver inventory caller memos metadata enteredCache := by
    obtain ⟨level, frontier, ordered⟩ := packet.ordered
    refine ⟨packet.context, stable.safe,
      EnumerationReferences.pending_read before.core enteredCache.core stable packet.pending,
      ⟨roots, enteredPaths, stable.safe.1, enteredRealized, enteredCounts, enteredFlags⟩,
      ⟨level, frontier, EnumerationOrder.stratified_read before.core enteredCache.core level frontier stable ordered⟩,
      ?_⟩
    simpa only [counter] using packet.bounded
  refine ⟨bound, enteredCache, entryRun, stable, counter, values, sameFlags, sameWaiting,
    enteredPacket, ?_, Post.refl packet.context, bounded, known⟩
  intro extra hook
  unfold run
  rw [entryRun extra]
  cases value with
  | node entry edges depth free => simp only [fallback, ↓reduceIte]
  | empty | reference _ | union _ _ _ _ | mu _ _ _ _ => rfl

end MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations
