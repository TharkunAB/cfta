import MicroCFTA.SourcePruningEnumerationSharedChildDispatchQueryEvents

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

/- Note [No Mu through the same child dispatch]
The empty and nonterminal branches retain their original caller and no events.
The terminal branch keeps the actual partition of this suspended list.
Its resources and no-Mu laws describe that same terminal observation.
The consumed-source bound is enlarged only to the original list length.
This proof adds no future event or query admission provider.
-/

theorem observe_original_no_mu_query_inventory
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (noMuSource : ∀ (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node),
      sourceHeap.nodeRecords key ≠ some (.mu entry body depth ordinary))
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
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap beforeCaller.checked.native.machine.heap)
    (representativeFuel nativeFuel p h indexFuel : Nat) :
    let observed := observe checkEmpty representativeFuel nativeFuel p h indexFuel
      scs incoming beforeCaller before memos.query
    observed.1 = SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
      checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming beforeCaller before memos.query ∧
    (InternedShallowHeap.NoNewMu sourceHeap observed.1.1.2.1.checked.native.machine.heap ∧
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
        (InternedShallowHeap.NoNewMu sourceHeap actual.state.native.machine.heap ∧
          Grows sourceHeap actual.state.native.machine.heap) ∧
        ∀ (count : Nat) (resume : Control Node) (after : SourceEqualityNativeDemand.State (bits + 2)),
          count ≤ nativeFuel → Trace count
            (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked resume after →
          InternedShallowHeap.NoNewMu sourceHeap after.native.machine.heap ∧
            Grows sourceHeap after.native.machine.heap
 := by
  dsimp only
  refine ⟨observe_exact checkEmpty representativeFuel nativeFuel p h indexFuel
    scs incoming beforeCaller before memos.query, ?_⟩
  by_cases empty : incoming = .empty
  · simp only [observe, ite_eq_left empty]
    refine ⟨?_, ?_⟩
    · simpa only [SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run,
        ite_eq_left empty] using And.intro pastInventory sourceGrowth
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
              exact And.intro pastInventory sourceGrowth
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
            have terminalInventory :=
              SourcePruningEnumerationSharedTerminalQueryEvents.run_original_source_observe_preserves_no_mu_inventory
                lib query signed whole accepted rootValue sourceHeap built noMuSource seed formulas solver inventory beforeCaller before checkEmpty
                first rest incoming descendants roots memos initial safe paths counts activeBounded
                activePending realized available closed fits activeReserved known sourceGrowth pastInventory
                representativeFuel nativeFuel p h indexFuel
            have terminalResources :=
              SourcePruningEnumerationSharedTerminalQueryEvents.run_observe_query_resources
                seed formulas solver inventory beforeCaller before checkEmpty first rest incoming descendants
                roots memos initial safe paths counts activeBounded activePending realized available closed
                fits activeReserved known representativeFuel nativeFuel p h indexFuel
            refine ⟨terminalInventory.2.2.1, ?_⟩
            intro start saved left right actual member
            obtain ⟨consumed, less, ready, currentFits, admitted, leftAvailable, rightAvailable,
              leftClosed, rightClosed, executed⟩ :=
              terminalResources.2.2 start saved left right actual member
            have eventInventory := terminalInventory.2.2.2 start saved left right actual member
            exact ⟨consumed, Nat.lt_of_lt_of_le less (Nat.add_le_add_right activeLength 1),
              ready, currentFits, admitted, leftAvailable, rightAvailable,
              leftClosed, rightClosed, executed, eventInventory.2⟩

end MicroCFTA.SourcePruningEnumerationSharedChildDispatchQueryEvents
