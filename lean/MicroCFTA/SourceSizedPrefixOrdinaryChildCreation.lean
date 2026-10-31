import MicroCFTA.SourceSizedPrefixKnownOrdinary
import MicroCFTA.SourcePruningEnumerationCachedChild
import MicroCFTA.SourcePruningEnumerationEdgeInputs

namespace MicroCFTA.SourceSizedPrefixOrdinaryChildCreation
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceSizedPrefixKnownOrdinary
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

/-- Literal parent rows give the domain and grade of the actual ordered child inputs. -/
theorem selected_input_grade
    (heightBound : Nat) (heap : Heap) (before : Cached)
    (known : KnownOrdinary heightBound heap before)
    (parentHandle : Nat) (parentScs : List Suspended)
    (stored : UVarValue.unenumerated (some parentHandle) parentScs ∈ before.core.values)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (decoded : lookupNode heap parentHandle = some (.node entry edges depth free))
    (edge : EdgeValue Symbol Constraint)
    (selected : edge ∈ InternedEdgeResidency.nodeEdges (.node entry edges depth free))
    (scs : List Suspended) (tries : List EqualityTrie.Trie)
    (incoming : Value Symbol Constraint) (bucket : List Suspended)
    (input : (incoming, bucket) ∈
      SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries) :
    SourceCurrentAllocatedFiniteOrdinaryDomain.Node incoming ∧
      MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height (.node entry edges depth free) ∧
      MergedOrdinaryHeight.height incoming ≤ heightBound := by
  obtain ⟨parent, actual, domain, bound⟩ := known parentHandle parentScs stored
  have same : parent = .node entry edges depth free := Option.some.inj (actual.symm.trans decoded)
  subst parent
  have rowMember : edge ∈ edges := by
    simpa only [InternedEdgeResidency.nodeEdges] using selected
  obtain ⟨indexed, indexedMember, pairSame⟩ := List.mem_map.mp input
  cases pairSame
  have grade := domain.child_lt edge rowMember indexed.1 (List.fst_mem_of_mem_zipIdx indexedMember)
  exact ⟨grade.1, grade.2, Nat.le_trans (Nat.le_of_lt grade.2) bound⟩

/-- The actual ordinary creator derives its handle, fresh slot, and same-cap certificate. -/
theorem prepareOrdinary_known
    (heightBound : Nat) (heap : Heap) (before : Cached)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (scs : List Suspended) (roots : Nat → Nat)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : Available heap (.node entry edges depth free)) (closed : free = [])
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (known : KnownOrdinary heightBound heap before)
    (ordinary : SourceCurrentAllocatedFiniteOrdinaryDomain.Node (.node entry edges depth free))
    (height : MergedOrdinaryHeight.height (.node entry edges depth free) ≤ heightBound) :
    ∃ (handle : Nat) (after : Cached) (fuel : Nat),
      encodeNode (.node entry edges depth free) = some handle ∧
      lookupNode heap handle = some (.node entry edges depth free) ∧
      (∀ extra, SourcePruningEnumerationCachedChild.prepareOrdinary heap (fuel + extra) scs
        (.node entry edges depth free) before = some (.hole before.core.counter, after)) ∧
      after.core.values[before.core.counter]? = some (.unenumerated (some handle) scs) ∧
      after.core.counter = before.core.counter + 1 ∧
      KnownOrdinary heightBound heap after := by
  obtain ⟨handle, _action, allocated, after, fuel, encoded, decoded, _prepared, _raw,
    _allocation, allocatedShape, _allocatedSlot, _allocatedStorage, _allocatedRealized,
    _allocatedCounts, _allocatedFlags, _waiting, _writes, prepares, afterShape,
    afterSlot, grows, _rest⟩ :=
    SourcePruningEnumerationCachedChild.complete heap before entry edges depth free scs roots
      coherent available closed storage realized paths counts flags bounded nonterminal
  have allocatedKnown : KnownOrdinary heightBound heap allocated := by
    intro current pending member
    rw [allocatedShape] at member
    change UVarValue.unenumerated (some current) pending ∈
      before.core.values ++ [UVarValue.unenumerated (some handle) []] at member
    rcases List.mem_append.mp member with old | added
    · exact known current pending old
    · have same : current = handle := Option.some.inj
        (UVarValue.unenumerated.inj (List.mem_singleton.mp added)).1
      subst current
      exact ⟨.node entry edges depth free, decoded, ordinary, height⟩
  refine ⟨handle, after, fuel, encoded, decoded, prepares, afterSlot, grows, ?_⟩
  intro current pending member
  rw [afterShape] at member
  change UVarValue.unenumerated (some current) pending ∈
    allocated.core.values.set before.core.counter (.unenumerated (some handle) scs) at member
  rcases List.mem_or_eq_of_mem_set member with retained | written
  · exact allocatedKnown current pending retained
  · have same : current = handle := Option.some.inj (UVarValue.unenumerated.inj written).1
    subst current
    exact ⟨.node entry edges depth free, decoded, ordinary, height⟩

end MicroCFTA.SourceSizedPrefixOrdinaryChildCreation
