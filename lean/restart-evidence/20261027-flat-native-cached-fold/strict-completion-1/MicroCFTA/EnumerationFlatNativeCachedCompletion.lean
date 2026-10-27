import MicroCFTA.EnumerationFlatNativeCachedFold
import MicroCFTA.SourcePruningEnumerationCachedFoldCompletion

namespace MicroCFTA.EnumerationFlatNativeCachedCompletion
open EnumerationState EnumerationSchedule EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open EnumerationCompleteness (PendingAt PendingOrEliminated)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}

/-!
# Actual flat cached completion at every sufficient execution bound

Use the original admitted completion once. Keep its stable native caller and
full global memo packet. Each adequate flat run supplies its actual endpoint.
No literal equality between flat endpoints at different bounds is asserted.
-/

/-- Original admission derives full native effects and correct caches for every adequate flat run. -/
theorem complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
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
    (ranges : SourcePruningEnumerationFold.Ranges checkEmpty sources
      beforeCaller before.core target memos.query) :
    ∃ (fuel p h : Nat)
      (rows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
      (afterCaller : Caller width) (savedQueries : Queries) (final : Memos) (next : Inventory)
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
          EnumerationFlatNativeIndex.Correct afterCaller.checked.native.machine.heap recovered) := by
  let roots := FlatUnionFind.root flat.core.representatives
  have paths : Roots before.core.representatives roots :=
    EnumerationFlatNativeIndex.related_roots related.core.representatives
  have counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting := by
    rw [← related.core.values, ← related.waiting]
    exact correct.waiting
  have flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap ((before.core.values[slot]?).getD .eliminated) =
        some (before.expandable slot) := by
    intro slot
    rw [← related.core.values, ← related.expandable]
    exact correct.expandable slot
  obtain ⟨fuel, p, h, rows, afterCaller, savedQueries, final, next, after,
    stable, post, querySame, counterSame, representativesSame, afterPaths, afterStorage,
    afterRealized, afterCounts, waitingSame, afterFlags, shape, afterTarget, eliminated,
    completed, frame, origin⟩ :=
      SourcePruningEnumerationCachedFoldCompletion.complete formulas solver inventory beforeCaller
        before sources checkEmpty target memos roots initial storage realized paths counts flags
        targetPending selected ranges
  refine ⟨fuel, p, h, rows, afterCaller, savedQueries, final, next, after,
    stable, post, querySame, counterSame, representativesSame, afterPaths, afterStorage,
    afterRealized, afterCounts, waitingSame, afterFlags, shape, afterTarget, eliminated,
    completed, frame, origin, ?_⟩
  intro extra P H pBound hBound
  have correspondence := EnumerationFlatNativeCachedFold.run_related related checkEmpty
    (fuel + extra) P H sources beforeCaller target memos.query
  rw [stable extra P H pBound hBound] at correspondence
  generalize actual : EnumerationFlatNativeCachedFold.run checkEmpty (fuel + extra) P H
    sources beforeCaller flat target memos.query = observed at correspondence
  obtain ⟨⟨outcome, reachedCaller, returnedQueries, outer⟩, recovered⟩ := observed
  obtain ⟨⟨callerSame, queriesSame, outerRelated, rowRelated⟩, cacheRelated⟩ := correspondence
  dsimp only at callerSame queriesSame outerRelated rowRelated cacheRelated
  subst reachedCaller
  subst returnedQueries
  cases recovered with
  | none => cases cacheRelated
  | some recovered =>
    cases outcome with
    | error fault => cases rowRelated
    | ok returned =>
      cases returned with
      | none => cases rowRelated
      | some flatRows =>
        exact ⟨flatRows, outer, recovered, actual, cacheRelated, outerRelated, rowRelated,
          EnumerationFlatNativeIndex.correct_of_related cacheRelated
            afterCaller.checked.native.machine.heap roots afterPaths afterStorage.aligned
            afterFlags afterCounts⟩

end MicroCFTA.EnumerationFlatNativeCachedCompletion
