import MicroCFTA.SourceSizedPrefixKnownOrdinary
import MicroCFTA.SourcePruningEnumerationCachedOwn

namespace MicroCFTA.SourceSizedPrefixOrdinarySlotCreation
open EnumerationState
open SourceSizedPrefixKnownOrdinary
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint

/-- The actual unassigned-slot creator preserves every known pending handle. -/
theorem allocate_none_known
    (heightBound : Nat) (heap : Heap) (before : Cached)
    (known : KnownOrdinary heightBound heap before) :
    ∃ after : Cached,
      SourcePruningEnumerationCachedChild.allocate heap none before =
        some (before.core.counter, after) ∧
      KnownOrdinary heightBound heap after ∧
      after.core = EnumerationState.allocated none before.core := by
  let after : Cached :=
    ⟨EnumerationState.allocated none before.core, before.expandable, before.waiting⟩
  refine ⟨after, rfl, ?_, rfl⟩
  intro handle scs member
  change UVarValue.unenumerated (some handle) scs ∈
    before.core.values ++ [UVarValue.unenumerated none []] at member
  have oldMember : UVarValue.unenumerated (some handle) scs ∈ before.core.values := by
    simpa using member
  exact known handle scs oldMember

/-- The actual own-class allocation derives its result without a future witness. -/
theorem suspendMany_known
    (heightBound : Nat) (heap : Heap) (tries : List EqualityTrie.Trie)
    (before : Cached) (known : KnownOrdinary heightBound heap before) :
    ∃ suspended, ∃ after : Cached,
      SourcePruningEnumerationCachedOwn.suspendMany heap tries before =
        some (suspended, after) ∧
      KnownOrdinary heightBound heap after := by
  induction tries generalizing before with
  | nil => exact ⟨[], before, rfl, known⟩
  | cons trie rest ih =>
      obtain ⟨allocated, allocation, allocatedKnown, _shape⟩ :=
        allocate_none_known heightBound heap before known
      obtain ⟨suspended, after, suspendedRun, afterKnown⟩ := ih allocated allocatedKnown
      refine ⟨⟨trie, before.core.counter⟩ :: suspended, after, ?_, afterKnown⟩
      simp only [SourcePruningEnumerationCachedOwn.suspendMany, allocation,
        Option.bind_some, suspendedRun, Option.map_some]

/-- The actual selected-edge prefix preserves the same shared height bound. -/
theorem prepare_known
    (heightBound : Nat) (heap : Heap) (scs : List Suspended)
    (edge : InternedConstructorTemplates.EdgeValue Symbol Constraint) (before : Cached)
    (known : KnownOrdinary heightBound heap before)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint =
      some (tries, residual)) :
    ∃ output, ∃ after : Cached,
      SourcePruningEnumerationCachedOwn.prepare heap scs edge before =
        some [(output, after)] ∧
      KnownOrdinary heightBound heap after := by
  obtain ⟨suspended, after, suspendedRun, afterKnown⟩ :=
    suspendMany_known heightBound heap tries before known
  simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
    projected, suspendedRun, Option.map_some]
  exact ⟨_, after, rfl, afterKnown⟩

end MicroCFTA.SourceSizedPrefixOrdinarySlotCreation
