import MicroCFTA.SourceSynthesisCurrentInitialFilterInterval
import MicroCFTA.SourcePruningEnumerationOwnInputShape
import MicroCFTA.SourceSynthesisOwnChildTerminals
import MicroCFTA.SourcePruningEnumerationSharedIncomingNode
import MicroCFTA.SourceCurrentAllocatedNativeInventoryState

/-!
# The fresh slot of the actual prepared source goal

The root filter starts with an empty suspended bucket.
Its own equality class allocates one unbound slot.
The first prepared child receives one terminal for that exact slot.
The positive-fuel representative read publishes the same fresh root.
The later shared terminal prefix and fold remain separate operations.
-/
namespace MicroCFTA.SourceSynthesisCurrentSharedSourceGoalFreshSlot
open Cache EnumerationState InternedConstructorTemplates
open EnumerationCorrectness (StorageValid)
open InternedFreshOrdinaryConstruction (build)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Input" => Node × List Suspended ×
  Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

set_option autoImplicit false

/-- Actual root preparation derives the goal's terminal bucket and unbound fresh slot. -/
theorem source_goal_prepared_fresh_slot
    {width : Nat} [DecidableEq (EdgeKey Symbol Constraint)]
    (inventory : Inventory)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue inventory.source)
    (rootRow : EdgeValue Symbol Constraint)
    (rootMember : rootRow ∈ InternedEdgeResidency.nodeEdges rootValue)
    (caller : Caller width) (captured middle : Cached)
    (storage : StorageValid captured.core)
    (symbol : Symbol) (staged : List Input) (residual : Option Constraint)
    (prepared : SourcePruningEnumerationCachedOwn.prepare
      caller.checked.native.machine.heap [] rootRow captured =
        some [((symbol, staged, residual), middle)]) :
    ∃ (goal : Node) (goalHeap : InternedConstructorTemplates.State Symbol Constraint)
        (action : Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))),
      build (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) [] empty =
        .done goal goalHeap ∧
      staged[0]? = some (goal, [⟨.terminal, captured.core.counter⟩], action) ∧
      ([⟨EqualityTrie.Trie.terminal, captured.core.counter⟩] : List Suspended).partition
        (fun sc => EqualityTrie.isTerminal sc.trie) =
          ([⟨.terminal, captured.core.counter⟩], []) ∧
      middle.core = allocated none captured.core ∧
      middle.waiting = captured.waiting ∧ middle.expandable = captured.expandable ∧
      middle.core.values[captured.core.counter]? = some (.unenumerated none []) ∧
      middle.core.representatives captured.core.counter = none ∧
      ∀ fuel : Nat,
        UnionFind.findRoot (fuel + 1) middle.core.representatives captured.core.counter =
          some ⟨captured.core.counter, 1,
            UnionFind.put middle.core.representatives captured.core.counter (.root 1)⟩ ∧
        ExceptT.run (representative (fuel + 1) captured.core.counter middle.core) =
          [.ok (captured.core.counter, {middle.core with representatives :=
            UnionFind.put middle.core.representatives captured.core.counter (.root 1)})] := by
  obtain ⟨_chunks, goal, _candidate, goalHeap, _candidateAfter, _edgeAfter,
      _chunksRun, _wholeShape, _symbol, constraint, children, goalBuilt,
      _candidateContext, _candidateBuilt, _edgeMade, _rootMade, _candidateGrowth, _factory⟩ :=
    SourceSynthesisCurrentFirstFilterSourceLink.current_initial_filter_interval
      lib query signed whole accepted rootValue inventory.source built rootRow rootMember
  let trie := EnumerationEquality.classTrie [[0], [1, 0]]
  let ownAfter : Cached := ⟨allocated none captured.core, captured.expandable, captured.waiting⟩
  have projected : SourcePruningEnumerationConstraint.project rootRow.entry.key.constraint =
      some (EnumerationEquality.readClasses [[[0], [1, 0]]], none) := by
    rw [constraint]
    exact SourceSynthesisOwnChildTerminals.filter_projection
  have ownRun : SourcePruningEnumerationCachedOwn.suspendMany caller.checked.native.machine.heap
      (EnumerationEquality.readClasses [[[0], [1, 0]]]) captured =
      some ([⟨trie, captured.core.counter⟩], ownAfter) := by
    rfl
  have unfolded := prepared
  simp only [SourcePruningEnumerationCachedOwn.prepare, arityAllows, List.all_nil,
    ↓reduceIte, projected, ownRun, Option.map_some] at unfolded
  have middleSame : middle = ownAfter :=
    (Prod.mk.inj (List.cons.inj (Option.some.inj unfolded)).1).2.symm
  have inputShape := SourcePruningEnumerationCachedOwn.prepare_inputs
    caller.checked.native.machine.heap [] rootRow captured middle
    (EnumerationEquality.readClasses [[[0], [1, 0]]]) none
    (symbol, staged, residual) projected prepared
  have stagedSame := congrArg (fun result : Symbol × List Input × Option Constraint =>
    result.2.1) inputShape
  let first : Suspended := ⟨.terminal, captured.core.counter⟩
  let action := SourcePruningEnumerationShallowChild.prepareChild
    (EnumGuard := Constraint) [first] goal
  have selected : staged[0]? = some (goal, [first], action) := by
    rw [stagedSame]
    simp only [SourcePruningEnumerationEdgeInputs.children, children]
    rfl
  have slot : middle.core.values[captured.core.counter]? = some (.unenumerated none []) := by
    rw [middleSame]
    exact allocated_slot none captured.core storage.aligned
  have missing : middle.core.representatives captured.core.counter = none := by
    rw [middleSame]
    exact EnumerationCorrectness.outside_forest captured.core.representatives
      captured.core.counter captured.core.counter storage.forest (Nat.le_refl _)
  refine ⟨goal, goalHeap, action, goalBuilt, selected, rfl, ?_, ?_, ?_, slot, missing, ?_⟩
  · rw [middleSame]
  · rw [middleSame]
  · rw [middleSame]
  · intro fuel
    have found : UnionFind.findRoot (fuel + 1) middle.core.representatives captured.core.counter =
        some ⟨captured.core.counter, 1,
          UnionFind.put middle.core.representatives captured.core.counter (.root 1)⟩ := by
      simp only [UnionFind.findRoot, missing]
    exact ⟨found, EnumerationCorrectness.representative_exact (fuel + 1)
      captured.core.counter middle.core _ found⟩

end MicroCFTA.SourceSynthesisCurrentSharedSourceGoalFreshSlot

#check @MicroCFTA.SourceSynthesisCurrentSharedSourceGoalFreshSlot.source_goal_fresh_slot
#print axioms MicroCFTA.SourceSynthesisCurrentSharedSourceGoalFreshSlot.source_goal_fresh_slot
