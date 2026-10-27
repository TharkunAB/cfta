import MicroCFTA.EnumerationFlatNativeCachedCompletion
import MicroCFTA.SourcePruningEnumerationFoldResources

/-!
# Original reservations construct the complete cached fold

The original mixed schedule derives every old range premise.
The same actual return retains the entire earlier completion packet and
adds numeric and guard bounds at its exact returned native caller.
-/
namespace MicroCFTA.EnumerationFlatNativeCachedCompletion
open EnumerationState EnumerationSchedule EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open EnumerationCompleteness (PendingAt PendingOrEliminated)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}

/-- Original reservations derive adequate flat cached completion and bound the same native return. -/
theorem complete_resources
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (flat : EnumerationFlatCached.Cached Symbol Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (related : EnumerationFlatCached.Related flat before) (sources : List Nat)
    (checkEmpty : Bool) (target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (storage : StorageValid before.core)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (correct : EnumerationFlatNativeIndex.Correct beforeCaller.checked.native.machine.heap flat)
    (targetPending : PendingAt before.core target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before.core source)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed sources.length)
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap) :
    ∃ (fuel p h : Nat)
      (rows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
      (afterCaller : Caller (bits + 2)) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (after : EnumerationExpandableIndex.Cached Symbol Constraint),
      (∀ extra P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationCachedFold.run checkEmpty (fuel + extra) P H sources
          beforeCaller before target memos.query =
          ((.ok (some (rows.map (fun row => .ok (row.1, row.2.core)))),
            afterCaller, savedQueries, after.core), some after)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      after.core.counter = before.core.counter ∧
      after.core.representatives = before.core.representatives ∧ Roots after.core.representatives (FlatUnionFind.root flat.core.representatives) ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct (FlatUnionFind.root flat.core.representatives) after.core.values after.waiting ∧
      after.waiting = before.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (rows = [] ∨ rows = [((), after)]) ∧ PendingAt after.core target ∧
      (∀ (slot : Nat), before.core.values[slot]? = some .eliminated →
        after.core.values[slot]? = some .eliminated) ∧
      (rows = [((), after)] → ∀ source ∈ sources, source ≠ target →
        after.core.values[source]? = some .eliminated) ∧
      (∀ (slot : Nat), slot ∉ sources → slot ≠ target →
        after.core.values[slot]? = before.core.values[slot]?) ∧
      (∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
        after.core.values[slot]? = some (.enumerated fragment) →
        before.core.values[slot]? = some (.enumerated fragment)) ∧
      (∀ extra P H, p ≤ P → h ≤ H →
        ∃ (flatRows : List (Except EnumerationState.Error (Unit × EnumerationFlatState.State Symbol Constraint)))
          (outer : EnumerationFlatState.State Symbol Constraint)
          (recovered : EnumerationFlatCached.Cached Symbol Constraint),
          EnumerationFlatNativeCachedFold.run checkEmpty (fuel + extra) P H sources
            beforeCaller flat target memos.query =
            ((.ok (some flatRows), afterCaller, savedQueries, outer), some recovered) ∧
          EnumerationFlatCached.Related recovered after ∧
          EnumerationFlatState.Related outer after.core ∧
          EnumerationResultRelation.Results EnumerationFlatState.Related flatRows
            (rows.map (fun row => .ok (row.1, row.2.core))) ∧
          EnumerationFlatNativeIndex.Correct afterCaller.checked.native.machine.heap recovered) ∧
      Fits (advance seed sources.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed sources.length).1) afterCaller.checked.native.machine.heap := by
  have ranges := SourcePruningEnumerationFold.initial_ranges seed formulas solver inventory beforeCaller
    before.core sources checkEmpty target memos initial realized targetPending selected fits reserved known
  obtain ⟨fuel, p, h, rows, afterCaller, savedQueries, final, next, after,
    stable, post, querySame, counterSame, representativesSame, afterPaths, afterStorage,
    afterRealized, afterCounts, waitingSame, afterFlags, shape, afterTarget, eliminated,
    completed, frame, origin, flatRuns⟩ :=
      complete formulas solver inventory beforeCaller flat before related sources checkEmpty target memos
        initial storage realized correct targetPending selected ranges
  have actual := stable 0 p h (Nat.le_refl _) (Nat.le_refl _)
  simp only [Nat.add_zero] at actual
  have erased := (SourcePruningEnumerationCachedFold.erase checkEmpty fuel p h sources
    beforeCaller before target memos.query).symm.trans (congrArg (fun output => output.1) actual)
  have bounded := SourcePruningEnumerationFold.observed_resources seed formulas solver inventory beforeCaller
    before.core sources checkEmpty fuel p h target memos initial realized targetPending selected
    fits reserved known erased
  exact ⟨fuel, p, h, rows, afterCaller, savedQueries, final, next, after,
    stable, post, querySame, counterSame, representativesSame, afterPaths, afterStorage,
    afterRealized, afterCounts, waitingSame, afterFlags, shape, afterTarget, eliminated,
    completed, frame, origin, flatRuns, bounded.1, bounded.2⟩

end MicroCFTA.EnumerationFlatNativeCachedCompletion
