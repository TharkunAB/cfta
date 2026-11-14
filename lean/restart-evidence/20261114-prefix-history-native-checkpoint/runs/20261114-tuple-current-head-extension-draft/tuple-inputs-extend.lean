namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualTuplePrefixExtension
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Extend the completed tuple prefix through its actual next child resources. -/
private theorem tuple_inputs_extend_current_head
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Unit) (before : Cached)
    (inputs : List (Node × List Suspended)) (completed : List Fragment)
    (caller : Caller (bits + 2)) (queries : Queries) (current : Cached)
    (incoming : Node) (bucket : List Suspended) (fragment : Fragment)
    (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
    (previous : TupleInputs formulas solver original metadata before inputs completed caller queries current)
    (member : (incoming, bucket) ∈ inputs)
    (pending : InputsPending current.core bucket)
    (head : ChildInputs formulas solver caller metadata current bucket fragment reached saved after) :
    TupleInputs formulas solver original metadata before inputs
      (completed ++ [fragment]) reached saved after := by
  obtain ⟨_currentInventory, _currentMemos, previousPost, _previousQuery, currentPacket,
    previousGrowth, previousOrigin, previousProtected, previousRootsProtected,
    previousReferences, previousBounds, previousHistory⟩ := previous
  obtain ⟨next, final, headPost, query, afterPacket, growth, origin, protects,
    references, fragmentBound, fragmentPending, fragmentSeparate⟩ := head
  have protectsEnumerated (held : Nat) (old : Fragment)
      (stored : current.core.values[held]? = some (.enumerated old)) :
      EnumerationDriver.Protected held current.core after.core := by
    obtain ⟨inside, root⟩ := enumerated_root current.core currentPacket.safe held old stored
    exact protects held inside root (pending held old stored)
  have protectsOriginalRoot (held : Nat) (inside : held < before.core.counter)
      (root : IsRoot before.core.representatives held)
      (avoids : ∀ child retained, (child, retained) ∈ inputs →
        Avoids before.core.representatives held retained) :
      EnumerationDriver.Protected held current.core after.core := by
    have first := previousRootsProtected held inside root avoids
    exact protects held (Nat.lt_of_lt_of_le inside previousGrowth) first.root
      (first.avoids bucket (avoids incoming bucket member))
  refine ⟨next, final, previousPost.trans headPost, query, afterPacket,
    Nat.le_trans previousGrowth growth, previousOrigin.trans origin, ?_, ?_, ?_, ?_, ?_⟩
  · intro held old stored
    have first := previousProtected held old stored
    exact first.trans (protectsEnumerated held old (first.value.trans stored))
  · intro held inside root avoids
    exact (previousRootsProtected held inside root avoids).trans
      (protectsOriginalRoot held inside root avoids)
  · intro allowed valid supplied future
    apply references allowed (previousReferences allowed valid supplied future)
      (supplied incoming bucket member)
    intro held inside
    exact future held (Nat.le_trans previousGrowth inside)
  · intro child included
    rcases List.mem_append.mp included with earlier | latest
    · exact fragmentBound_mono _ _ growth child (previousBounds child earlier)
    · rcases List.mem_singleton.mp latest with rfl
      exact fragmentBound
  · intro child included
    rcases List.mem_append.mp included with earlier | latest
    · obtain ⟨childPending, childSeparate⟩ := previousHistory child earlier
      refine ⟨pendingFragment_preserved current.core after.core currentPacket.safe afterPacket.safe
        growth child (previousBounds child earlier) childPending origin protectsEnumerated, ?_⟩
      intro held inside root avoids
      have lastProtection := protectsOriginalRoot held inside root avoids
      exact (fragmentAvoid_classes current.core.representatives after.core.representatives
        held child lastProtection.classes).mpr (childSeparate held inside root avoids)
    · rcases List.mem_singleton.mp latest with rfl
      refine ⟨fragmentPending, ?_⟩
      intro held inside root avoids
      have first := previousRootsProtected held inside root avoids
      exact fragmentSeparate held (Nat.lt_of_lt_of_le inside previousGrowth) first.root
        (first.avoids bucket (avoids incoming bucket member))

end ActualTuplePrefixExtension
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
