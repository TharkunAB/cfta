import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations
import MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents

/-!
# Actual query events for every child dispatch branch

Note [One child dispatch event list]
The observer uses the original complete child run in zero-query branches.
The terminal branch reuses the existing terminal observer at the same literal
partition. Exactness retains the full result and cache. The resource and Seeds
proofs both refer to that same explicit terminal observation and event tuple.
They do not identify hidden witnesses through a Prop proof index.

The resource position counts consumed source iterations. It does not count
queries. Event refinement does not prove whole-worker Seeds propagation,
native inhabitance or ONE finite accepted completion.
-/

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedChildDispatchQueryEvents
open EnumerationCorrectness EnumerationCompleteness EnumerationSchedule EnumerationDependencies
open EnumerationState (Suspended)
open InternedConstructorTemplates InternedProbeProvenance
open Cache (Interned)
open SourcePruningEnumerationObservation (PendingRealized)
open SourcePruningEnumerationSharedDispatchQueryEvents (Event)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentNativeNumericalSeedInvariant (Seeds)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceEqualityNativeDemand (Control)
open SourceRecursiveIntersectionControl (identity)
open SourceRecursiveIntersectionCode (requestNode)
open InternedBinderProtocol (NodeKey)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable {width bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the exact child result and its actual ordered terminal queries. -/
noncomputable def observe
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation width × Option Cached) ×
      List (Event width)
 :=
  if incoming = .empty then
    (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming caller before queries, [])
  else
    match scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | ([], _) =>
        (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
          checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming caller before queries, [])
    | (first :: rest, descendants) =>
        SourcePruningEnumerationSharedTerminalQueryEvents.runObserved
          checkEmpty representativeFuel nativeFuel p h indexFuel
          first rest caller before incoming descendants queries

/-- The observer retains the complete original result and optional cache. -/
theorem observe_exact
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    (observe checkEmpty representativeFuel nativeFuel p h indexFuel
      scs incoming caller before queries).1 =
      SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
        checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming caller before queries
 := by
  by_cases empty : incoming = .empty
  · simp only [observe, ite_eq_left empty]
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
        cases here with
        | nil => simp only [observe, ite_eq_right empty, partitioned]
        | cons first rest =>
            simp only [observe, ite_eq_right empty, partitioned]
            exact (SourcePruningEnumerationSharedTerminalQueryEvents.run_observe_exact
              checkEmpty representativeFuel nativeFuel p h indexFuel
              first rest caller before incoming descendants queries).1.trans
                (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.terminal
                  checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming caller before queries
                  first rest descendants partitioned).symm

/-- Current source resources preserve Seeds at the return and every actual query prefix. -/
theorem observe_original_source_query_resources_and_seeds
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (scs : List Suspended) (incoming : Node)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (pending : InputsPending before.core scs)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (available : Available beforeCaller.checked.native.machine.heap incoming)
    (closed : incoming.free = [])
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (scs.length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (sourceGrowth : Grows sourceHeap beforeCaller.checked.native.machine.heap)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId beforeCaller.checked)
    (representativeFuel nativeFuel p h indexFuel : Nat) :
    let observed := observe checkEmpty representativeFuel nativeFuel p h indexFuel
      scs incoming beforeCaller before memos.query
    observed.1 = SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming beforeCaller before memos.query ∧
    (Seeds sourceHeap entry body depth ordinary bodyId observed.1.1.2.1.checked ∧
      Grows sourceHeap observed.1.1.2.1.checked.native.machine.heap) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      ∃ consumed : Nat, consumed < scs.length + 1 ∧
        SourceCurrentConjunctionClassScan.Ready start.checked ∧
        Fits (advance seed consumed).2 start.checked ∧
        SourceCurrentAllocatedNativeCreditProfile.Admits bits (advance seed consumed).2 ∧
        Available start.checked.native.machine.heap left ∧
        Available start.checked.native.machine.heap right ∧
        left.free = [] ∧ right.free = [] ∧
        actual = SourceEqualityNativeDemand.execute nativeFuel
          (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked ∧
        (Seeds sourceHeap entry body depth ordinary bodyId actual.state ∧
          Grows sourceHeap actual.state.native.machine.heap) ∧
        ∀ (count : Nat) (resume : Control Node) (after : SourceEqualityNativeDemand.State (bits + 2)),
          count ≤ nativeFuel → Trace count
            (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked resume after →
          Seeds sourceHeap entry body depth ordinary bodyId after ∧
            Grows sourceHeap after.native.machine.heap
 := by
  dsimp only
  refine ⟨observe_exact checkEmpty representativeFuel nativeFuel p h indexFuel
    scs incoming beforeCaller before memos.query, ?_⟩
  by_cases empty : incoming = .empty
  · simp only [observe, ite_eq_left empty]
    refine ⟨?_, ?_⟩
    · simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
        ite_eq_left empty] using And.intro pastSeeds sourceGrowth
    · intro start saved left right actual member
      exact False.elim (List.not_mem_nil member)
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
        cases here with
        | nil =>
            simp only [observe, ite_eq_right empty, partitioned]
            refine ⟨?_, ?_⟩
            · have rawCaller :
                  (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe
                    checkEmpty representativeFuel nativeFuel p h scs incoming
                    beforeCaller before.core before.waiting memos.query).2.1 = beforeCaller := by
                unfold SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.observe
                rw [ite_eq_right empty, partitioned]
                cases SourcePruningEnumerationShallowChild.prepareChild
                    (EnumGuard := Constraint) scs incoming <;> rfl
              have callerSame :
                  (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
                    checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming
                    beforeCaller before memos.query).1.2.1 = beforeCaller :=
                (congrArg (fun observation => observation.2.1)
                  (SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.erase
                    checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming
                    beforeCaller before memos.query)).trans rawCaller
              rw [callerSame]
              exact And.intro pastSeeds sourceGrowth
            · intro start saved left right actual member
              exact False.elim (List.not_mem_nil member)
        | cons first rest =>
            simp only [observe, ite_eq_right empty, partitioned]
            have terminal : scs.filter (fun sc => EqualityTrie.isTerminal sc.trie) = first :: rest := by
              simpa only [List.partition_eq_filter_filter] using congrArg Prod.fst partitioned
            have activeSubset : (first :: rest) ⊆ scs := by
              intro sc member
              exact (List.mem_filter.mp (terminal ▸ member)).1
            have activeLength : (first :: rest).length ≤ scs.length := by
              rw [← terminal]
              exact List.length_filter_le _ _
            have activeBounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter :=
              fun sc member => bounded sc (activeSubset member)
            have activePending : InputsPending before.core (first :: rest) := by
              intro held fragment storedValue sc member
              exact pending held fragment storedValue sc (activeSubset member)
            have activeReserved : Reserved bits seed ((first :: rest).length + 1) :=
              reserved.prefix (Nat.add_le_add_right activeLength 1)
            have terminalSeeds :=
              SourcePruningEnumerationSharedTerminalQueryEvents.run_original_source_observe_preserves_seeds
                lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
                stored bodyId bodyIdentity seed formulas solver inventory beforeCaller before checkEmpty
                first rest incoming descendants roots memos initial safe paths counts activeBounded
                activePending realized available closed fits activeReserved known sourceGrowth pastSeeds
                representativeFuel nativeFuel p h indexFuel
            have terminalResources :=
              SourcePruningEnumerationSharedTerminalQueryEvents.run_observe_query_resources
                seed formulas solver inventory beforeCaller before checkEmpty first rest incoming descendants
                roots memos initial safe paths counts activeBounded activePending realized available closed
                fits activeReserved known representativeFuel nativeFuel p h indexFuel
            refine ⟨terminalSeeds.2.2.1, ?_⟩
            intro start saved left right actual member
            obtain ⟨consumed, less, ready, currentFits, admitted, leftAvailable, rightAvailable,
              leftClosed, rightClosed, executed⟩ :=
              terminalResources.2.2 start saved left right actual member
            have meanings := terminalSeeds.2.2.2 start saved left right actual member
            exact ⟨consumed, Nat.lt_of_lt_of_le less (Nat.add_le_add_right activeLength 1),
              ready, currentFits, admitted, leftAvailable, rightAvailable,
              leftClosed, rightClosed, executed, meanings.2⟩

end MicroCFTA.SourcePruningEnumerationSharedChildDispatchQueryEvents
