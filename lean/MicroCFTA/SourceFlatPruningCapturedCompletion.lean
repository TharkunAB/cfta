import MicroCFTA.SourceFlatPruningCapturedEdge
import MicroCFTA.SourceFlatPruningSelectedCompletion

/-!
# Flat observations of the complete captured-edge producer

Common original bounds align selected execution with its actual finalizer.
The complete original packet keeps its own caller, memos and history.
-/

namespace MicroCFTA.SourceFlatPruningCapturedCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningEnumerationCapturedEdge
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Result" => SourcePruningEnumerationSelectedEdge.Result
local notation "FlatResult" => SourceFlatPruningSelectedEdge.Result
variable {width : Nat}

private theorem result_correct
    (flat : FlatResult width) (result : Result width)
    (afterCaller : Caller width) (after : Cached) (savedQueries : Queries)
    (roots : Nat → Nat) (paths : Roots after.core.representatives roots)
    (storage : StorageValid after.core)
    (counts : EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
      ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot))
    (shape : (∃ fragment, result = .complete fragment afterCaller savedQueries after) ∨
      ∃ fragments outer waiting, result = .stopped fragments
        (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after))
    (related : SourceFlatPruningSelectedEdge.ResultRelated flat result) :
    match flat with
    | .complete _ reached _ recovered =>
        EnumerationFlatNativeIndex.Correct reached.checked.native.machine.heap recovered
    | .stopped _ observation (some recovered) =>
        EnumerationFlatNativeIndex.Correct observation.2.1.checked.native.machine.heap recovered
    | _ => False := by
  rcases shape with ⟨fragment, completed⟩ | ⟨fragments, outer, waiting, stopped⟩
  · rw [completed] at related
    cases flat with
    | unhandled => cases related
    | rejected reached saved recovered => cases related
    | stopped prefixFragments observation candidate => cases related
    | complete flatFragment reached saved recovered =>
        obtain ⟨_fragmentSame, callerSame, _querySame, caches⟩ := related
        change EnumerationFlatNativeIndex.Correct reached.checked.native.machine.heap recovered
        rw [callerSame]
        exact EnumerationFlatNativeIndex.correct_of_related caches afterCaller.checked.native.machine.heap
          roots paths storage.aligned flags counts
  · rw [stopped] at related
    cases flat with
    | unhandled => cases related
    | rejected reached saved recovered => cases related
    | complete flatFragment reached saved recovered => cases related
    | stopped prefixFragments observation candidate =>
        obtain ⟨_fragmentsSame, ⟨callerSame, _queriesSame, _outerRelated, _waitingSame, _rowsRelated⟩,
          cacheRelated⟩ := related
        cases candidate with
        | none => cases cacheRelated
        | some recovered =>
            change EnumerationFlatNativeIndex.Correct observation.2.1.checked.native.machine.heap recovered
            dsimp only at callerSame
            rw [callerSame]
            exact EnumerationFlatNativeIndex.correct_of_related cacheRelated
              afterCaller.checked.native.machine.heap roots paths storage.aligned flags counts

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Keep every old captured receipt and append actual flat observations at common bounds. -/
theorem complete_with_history
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller width) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (ranges : SourcePruningEnumerationSelectedEdge.Ranges checkEmpty scs edge caller before memos.query) :
    ∃ (r n p h k : Nat) (afterCaller : Caller width) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result width),
      ((∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) uv scs edge caller before memos.query = some result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (∀ held fragment, held ≠ uv → after.core.values[held]? = some (.enumerated fragment) →
        before.core.values[held]? = some (.enumerated fragment)) ∧
      InputsPending after.core scs ∧
      (∀ held, held ≠ uv → held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        EnumerationReferences.PendingReferences after.core) ∧
      ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
          Safe after.core ∧ FragmentBound after.core.counter fragment ∧
          after.core.values[uv]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
          IsRoot after.core.representatives uv ∧ PendingFragment after.core fragment ∧
          ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
            ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1)) ∨
        ∃ fragments outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after))) ∧
      (∀ (flat : FlatCached), EnumerationFlatCached.Related flat before →
        ∀ en P H, p ≤ P → h ≤ H →
        ∃ flatResult,
          SourceFlatPruningCapturedEdge.run checkEmpty (n + en) P H uv scs edge
            caller flat memos.query = some flatResult ∧
          SourceFlatPruningSelectedEdge.ResultRelated flatResult result ∧
          match flatResult with
          | .complete _ reached _ recovered =>
              EnumerationFlatNativeIndex.Correct reached.checked.native.machine.heap recovered
          | .stopped _ observation (some recovered) =>
              EnumerationFlatNativeIndex.Correct observation.2.1.checked.native.machine.heap recovered
          | _ => False) := by
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots, result, packet⟩ :=
    SourcePruningEnumerationCapturedEdge.complete_with_history formulas solver inventory caller before
      checkEmpty uv handle scs parentEntry edges depth free edge roots memos initial ready stored decoded
      realized selected paths counts flags pending allowed tries residual projected ranges
  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry edges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  obtain ⟨selectedR, selectedN, selectedP, selectedH, selectedK,
    _selectedCaller, _selectedAfter, _selectedQueries, _selectedFinal, _selectedInventory,
    _selectedRoots, selectedResult, selectedRun, _selectedPost, _selectedQuerySame,
    _selectedGrowth, _selectedPaths, _selectedStorage, _selectedRealized, _selectedCounts,
    _selectedFlags, _selectedOrigin, _selectedPending, _selectedProtects, _selectedHistory,
    _selectedIncoming, _selectedShape, selectedFlat⟩ :=
    SourceFlatPruningSelectedCompletion.complete_with_fragments formulas solver inventory caller before checkEmpty
      parentEntry edges depth free edge scs roots memos initial available closed selected ready.safe realized
      paths counts flags bounded pending allowed tries residual projected ranges
  obtain ⟨oldRun, oldRest⟩ := packet
  have shiftedRun : ∀ er en P H ek, max p selectedP ≤ P → max h selectedH ≤ H →
      SourcePruningEnumerationCapturedEdge.run checkEmpty (r + selectedR + er) (n + selectedN + en)
        P H (k + selectedK + ek) uv scs edge caller before memos.query = some result := by
    intro er en P H ek enoughP enoughH
    simpa only [Nat.add_assoc] using oldRun (selectedR + er) (selectedN + en) P H
      (selectedK + ek) (Nat.le_trans (Nat.le_max_left p selectedP) enoughP)
      (Nat.le_trans (Nat.le_max_left h selectedH) enoughH)
  refine ⟨r + selectedR, n + selectedN, max p selectedP, max h selectedH, k + selectedK,
    afterCaller, after, savedQueries, final, next, afterRoots, result, ⟨shiftedRun, oldRest⟩, ?_⟩
  obtain ⟨_post, _querySame, _growth, afterPaths, storage, _afterRealized,
    afterCounts, afterFlags, _origin, _pending, _protects, _history, shape⟩ := oldRest
  have resultShape : (∃ fragment, result = .complete fragment afterCaller savedQueries after) ∨
      ∃ fragments outer waiting, result = .stopped fragments
        (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after) := by
    rcases shape with ⟨fragment, completed, _⟩ | ⟨fragments, outer, waiting, stopped⟩
    · exact .inl ⟨fragment, completed⟩
    · exact .inr ⟨fragments, outer, waiting, stopped⟩
  intro flat related en P H enoughP enoughH
  have selectedEnoughP := Nat.le_trans (Nat.le_max_right p selectedP) enoughP
  have selectedEnoughH := Nat.le_trans (Nat.le_max_right h selectedH) enoughH
  obtain ⟨flatSelected, flatAt, selectedRelated⟩ :=
    selectedFlat flat related (n + en) P H selectedEnoughP selectedEnoughH
  have selectedAt : SourcePruningEnumerationSelectedEdge.run checkEmpty (r + selectedR)
      (n + selectedN + en) P H (k + selectedK) scs edge caller before memos.query = selectedResult := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      selectedRun r (n + en) P H k selectedEnoughP selectedEnoughH
  have flatSelectedAt : SourceFlatPruningSelectedEdge.run checkEmpty (n + selectedN + en) P H
      scs edge caller flat memos.query = flatSelected := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using flatAt
  have actualSelected : SourceFlatPruningSelectedEdge.ResultRelated
      (SourceFlatPruningSelectedEdge.run checkEmpty (n + selectedN + en) P H
        scs edge caller flat memos.query)
      (SourcePruningEnumerationSelectedEdge.run checkEmpty (r + selectedR) (n + selectedN + en)
        P H (k + selectedK) scs edge caller before memos.query) := by
    rw [flatSelectedAt, selectedAt]
    exact selectedRelated
  have actualCaptured : SourcePruningEnumerationCapturedEdge.run checkEmpty (r + selectedR)
      (n + selectedN + en) P H (k + selectedK) uv scs edge caller before memos.query = some result := by
    simpa only [Nat.add_zero] using shiftedRun 0 en P H 0 enoughP enoughH
  obtain ⟨flatResult, actual, resultRelated⟩ :=
    SourceFlatPruningCapturedEdge.run_completed checkEmpty (r + selectedR) (n + selectedN + en)
      P H (k + selectedK) uv scs edge caller flat before memos.query result actualSelected actualCaptured
  refine ⟨flatResult, actual, resultRelated, ?_⟩
  have correct := result_correct flatResult result afterCaller after savedQueries afterRoots afterPaths storage
    afterCounts afterFlags resultShape resultRelated
  cases flatResult with
  | unhandled => exact correct
  | rejected reached saved recovered => exact correct
  | complete fragment reached saved recovered => exact correct
  | stopped fragments observation candidate => cases candidate <;> exact correct

end MicroCFTA.SourceFlatPruningCapturedCompletion
