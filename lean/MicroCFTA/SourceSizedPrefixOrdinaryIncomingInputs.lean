-- Ordinary inputs from actual selected-edge preparation.
import MicroCFTA.SourceSizedPrefixOrdinaryChildCreation
import MicroCFTA.SourceSizedPrefixOrdinarySlotCreation

/-!
# Ordinary inputs from actual selected-edge preparation

The producer creates the exact list consumed by ChildTraversal.run.
Each incoming value is an original selected-row child.
The recursive worker hook does not supply these values.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceSizedPrefixOrdinaryIncomingInputs
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceSizedPrefixKnownOrdinary
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Heap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Staged" => List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment))

/-- Actual preparation derives the consumer list and each incoming node certificate. -/
theorem complete (heightBound : Nat) (heap : Heap) (before : Cached)
    (known : KnownOrdinary heightBound heap before)
    (parentSlot parentHandle : Nat) (scs : List Suspended)
    (stored : before.core.values[parentSlot]? = some (.unenumerated (some parentHandle) scs))
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (decoded : lookupNode heap parentHandle = some (.node entry edges depth free))
    (edge : EdgeValue Symbol Constraint)
    (selected : edge ∈ InternedEdgeResidency.nodeEdges (.node entry edges depth free))
    (roots : Nat → Nat) (ready : SourceEqualityRequiredCache.Ready heap)
    (safe : Safe before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
    ∃ staged : Staged, ∃ after : Cached,
      SourcePruningEnumerationCachedOwn.prepare heap scs edge before =
        some [((edge.entry.key.symbol, staged, residual), after)] ∧
      staged.map (fun input => (input.1, input.2.1)) =
        SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries ∧
      Safe after.core ∧ Roots after.core.representatives roots ∧ PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      KnownOrdinary heightBound heap after ∧
      ∀ incoming bucket, (incoming, bucket) ∈ staged.map (fun input => (input.1, input.2.1)) →
        Available heap incoming ∧ incoming.free = [] ∧
        SourceCurrentAllocatedFiniteOrdinaryDomain.Node incoming ∧
        MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height (.node entry edges depth free) ∧
        MergedOrdinaryHeight.height incoming ≤ heightBound ∧
        (∀ sc ∈ bucket, sc.var < after.core.counter) ∧ InputsPending after.core bucket := by
  classical
  obtain ⟨parent, parentRead, parentAvailable, parentClosed⟩ :=
    realized parentSlot parentHandle scs stored
  have parentSame : parent = .node entry edges depth free :=
    Option.some.inj (parentRead.symm.trans decoded)
  subst parent
  change free = [] at parentClosed
  have parentPresent : UVarValue.unenumerated (some parentHandle) scs ∈ before.core.values :=
    List.mem_of_getElem? stored
  have selectedRows : edge ∈ edges := selected
  obtain ⟨_action, after, _prefix, prepared, _raw, _core, _counter, _forest,
    safeAfter, rootsAfter, realizedAfter, countsAfter, flagsAfter, _pendingOwn, inputFacts, _protected⟩ :=
    SourcePruningEnumerationEdgeInputs.complete heap entry edges depth free edge scs roots ready
      parentAvailable parentClosed selectedRows before safe realized paths counts flags bounded pending
      allowed tries residual projected
  obtain ⟨_output, kept, keptPrepared, keptKnown⟩ :=
    SourceSizedPrefixOrdinarySlotCreation.prepare_known heightBound heap scs edge before known
      allowed tries residual projected
  have sameAfter : kept = after := congrArg Prod.snd
    (List.cons.inj (Option.some.inj (keptPrepared.symm.trans prepared))).1
  subst kept
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  let staged : Staged := inputs.map (fun input =>
    (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1))
  have consumer : staged.map (fun input => (input.1, input.2.1)) = inputs := by
    simp only [staged, List.map_map]
    exact List.map_id inputs
  refine ⟨staged, after, prepared, consumer, safeAfter, rootsAfter, realizedAfter,
    countsAfter, flagsAfter, keptKnown, ?_⟩
  intro incoming bucket observed
  have input : (incoming, bucket) ∈ inputs := by
    simpa only [consumer] using observed
  have grade := SourceSizedPrefixOrdinaryChildCreation.selected_input_grade
    heightBound heap before known parentHandle scs parentPresent entry edges depth free decoded
    edge selected scs tries incoming bucket input
  have current := inputFacts incoming bucket input
  exact ⟨current.1, current.2.1, grade.1, grade.2.1, grade.2.2, current.2.2.1, current.2.2.2⟩

end MicroCFTA.SourceSizedPrefixOrdinaryIncomingInputs
