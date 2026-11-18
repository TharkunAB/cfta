import MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations
import MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents

/-!
# Native Seeds at an actual child dispatch return

Note [Child dispatch retains one terminal observation]
The empty and shallow routes retain their input native caller. The terminal
route uses the actual partition of the original bucket. That partition supplies
the bounded pending inputs and a prefix of the original reservation. The proof
uses one terminal observer receipt to identify the returned caller.

This theorem concerns the returned caller. It does not construct a child query
event list or prove whole-worker Seeds propagation or native inhabitance.
-/

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
open EnumerationCorrectness EnumerationCompleteness EnumerationSchedule EnumerationDependencies
open EnumerationState (Suspended)
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation (PendingRealized)
open SourcePruningEnumerationSharedIncomingReservation (Seed Reserved)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentNativeNumericalSeedInvariant (Seeds)
open SourceRecursiveIntersectionControl (identity)
open InternedBinderProtocol (NodeKey)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

theorem original_source_run_preserves_seeds
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
    let actual := run checkEmpty representativeFuel nativeFuel p h indexFuel
      scs incoming beforeCaller before memos.query
    Seeds sourceHeap entry body depth ordinary bodyId actual.1.2.1.checked ∧
      Grows sourceHeap actual.1.2.1.checked.native.machine.heap
 := by
  dsimp only
  by_cases empty : incoming = .empty
  · simpa only [run, ite_eq_left empty] using And.intro pastSeeds sourceGrowth
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
        cases here with
        | nil =>
            have rawCaller :
                (observe checkEmpty representativeFuel nativeFuel p h scs incoming
                  beforeCaller before.core before.waiting memos.query).2.1 = beforeCaller := by
              unfold observe
              rw [ite_eq_right empty, partitioned]
              cases SourcePruningEnumerationShallowChild.prepareChild
                  (EnumGuard := Constraint) scs incoming <;> rfl
            have callerSame :
                (run checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming
                  beforeCaller before memos.query).1.2.1 = beforeCaller :=
              (congrArg (fun observation => observation.2.1)
                (erase checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming
                  beforeCaller before memos.query)).trans rawCaller
            rw [callerSame]
            exact And.intro pastSeeds sourceGrowth
        | cons first rest =>
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
            have finalSeeds := terminalSeeds.2.2.1
            rw [terminalSeeds.1] at finalSeeds
            simpa only [run, ite_eq_right empty, partitioned] using finalSeeds

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
