namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualTupleInputTransport
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- A completed prefix retains every original tuple input at its current endpoint. -/
private theorem tuple_inputs_current_inputs
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller (bits + 2)) (metadata : Metadata Unit) (before : Cached)
    (inputs : List (Node × List Suspended)) (completed : List Fragment)
    (caller : Caller (bits + 2)) (queries : Queries) (current : Cached)
    (previous : TupleInputs formulas solver original metadata before inputs completed caller queries current)
    (genuine : ∀ child bucket, (child, bucket) ∈ inputs →
      Available original.checked.native.machine.heap child ∧ child.free = [] ∧
      (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket) :
    ∀ child bucket, (child, bucket) ∈ inputs →
      Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
      (∀ sc ∈ bucket, sc.var < current.core.counter) ∧ InputsPending current.core bucket := by
  obtain ⟨_next, _final, post, _query, _packet, growth, origin, protects,
    _rootProtection, _references, _bounds, _history⟩ := previous
  intro child bucket member
  obtain ⟨available, closed, bounded, pending⟩ := genuine child bucket member
  refine ⟨post.effects.keeps.available child available, closed,
    fun sc included => Nat.lt_of_lt_of_le (bounded sc included) growth, ?_⟩
  intro held fragment stored
  have originalStored := origin held fragment stored
  exact (protects held fragment originalStored).avoids bucket
    (pending held fragment originalStored)

end ActualTupleInputTransport
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
