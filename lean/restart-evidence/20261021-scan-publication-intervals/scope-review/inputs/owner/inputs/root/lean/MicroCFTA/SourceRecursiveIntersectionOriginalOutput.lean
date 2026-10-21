import MicroCFTA.SourceRecursiveIntersectionNativeResultScope

/-!
# Closed available outputs retain original payload syntax

Coherent metadata propagates every non-interned payload reference to the
root free-name list. Mu binders remove only their own interned name.
A closed available result therefore contains only original payload syntax.
Probe metadata remains outside the Original predicate.
-/
namespace MicroCFTA.SourceRecursiveIntersectionOriginalOutput
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference)
open SourceRecursiveIntersectionInputView (Original)

mutual
/-- An available value with only interned free names has original payload syntax. -/
theorem original_of_free (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (names : ∀ name ∈ value.free, ∃ identity, name = Reference.interned identity) : Original value := by
  cases value with
  | empty => exact .empty
  | reference name =>
      obtain ⟨identity, rfl⟩ := names name (by simp [Value.free])
      exact .reference identity
  | node entry edges depth free =>
      apply Original.node
      apply original_edges edges state coherent (fun child member => available.children child member)
      intro child member name named
      apply names name
      rw [Value.free, InternedNormalizationFree.node_free state coherent entry edges depth free available.resident, childFree_member]
      exact ⟨child, member, named⟩
  | union entry members depth free =>
      apply Original.union
      apply original_values members state coherent (fun child member => available.children child member)
      intro child member name named
      apply names name
      rw [Value.free, InternedNormalizationFree.union_free state coherent entry members depth free available.resident, childFree_member]
      exact ⟨child, member, named⟩
  | mu entry body depth ordinary =>
      apply Original.mu
      apply original_of_free body state coherent (available.children body (by simp [children]))
      intro name member
      by_cases same : name = .interned entry.identity
      · exact ⟨entry.identity, same⟩
      · apply names name
        simp only [Value.free, List.mem_filter, bne_iff_ne]
        exact ⟨member, same⟩
termination_by sizeOf value

/-- Ordered available values with only interned free names retain original payload syntax. -/
theorem original_values (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ values, Available state value)
    (names : ∀ value ∈ values, ∀ name ∈ value.free, ∃ identity, name = Reference.interned identity) :
    ∀ value ∈ values, Original value := by
  cases values with
  | nil => intro value member; cases member
  | cons first rest =>
      have head := original_of_free first state coherent (available first List.mem_cons_self) (names first List.mem_cons_self)
      have tail := original_values rest state coherent (fun value member => available value (List.mem_cons_of_mem first member))
        (fun value member => names value (List.mem_cons_of_mem first member))
      intro value member
      rcases List.mem_cons.mp member with rfl | included
      · exact head
      · exact tail value included
termination_by sizeOf values

/-- Every actual ordered edge child with only interned free names has original payload syntax. -/
theorem original_edges (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value)
    (names : ∀ value ∈ edges.flatMap EdgeValue.children, ∀ name ∈ value.free, ∃ identity, name = Reference.interned identity) :
    ∀ edge ∈ edges, ∀ child ∈ edge.children, Original child := by
  cases edges with
  | nil => intro edge member; cases member
  | cons first rest =>
      cases first with
      | mk entry values =>
          have head := original_values values state coherent
            (fun value member => available value (by simp [EdgeValue.children, member]))
            (fun value member => names value (by simp [EdgeValue.children, member]))
          have tail := original_edges rest state coherent
            (fun value member => available value (by simp [EdgeValue.children, member]))
            (fun value member => names value (by simp [EdgeValue.children, member]))
          intro edge member child inside
          rcases List.mem_cons.mp member with rfl | included
          · exact head child inside
          · exact tail edge included child inside
termination_by sizeOf edges
end

/-- Closed coherent available records derive original payload syntax without an output-syntax premise. -/
theorem closed_original (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (closed : value.free = []) : Original value := by
  apply original_of_free value state coherent available
  intro name member
  rw [closed] at member
  cases member

end MicroCFTA.SourceRecursiveIntersectionOriginalOutput

namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionInputView (Original)

/-- An actual closed available native result has original payload syntax in its exact returned cache. -/
theorem Correct.closed_original [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {code : Code Symbol Guard (Value Symbol Guard)}
    {state after : SourceRecursiveIntersectionThunks.State width Symbol Guard} {value : Value Symbol Guard}
    (correct : Correct emptyGuard conjoin code state value after (fun final value => Available final.heap value))
    (closed : value.free = []) : Original value :=
  SourceRecursiveIntersectionOriginalOutput.closed_original value after.machine.heap correct.valid.machine.1.coherent correct.result closed

/-- Actual successful empty-domain native execution derives original output syntax from its proved closedness. -/
theorem done_original_of_ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) (left right value : Value Symbol Guard)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (leftAvailable : Available state.machine.heap left) (rightAvailable : Available state.machine.heap right)
    (heap : SemanticHeap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state)
    (done : execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done value after) :
    Original value := by
  have ready : NodeReady state.machine ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
    ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have correct := done_correct_of_ranges emptyGuard conjoin _ state after value (fun final value => Available final.heap value)
    (by intro value; trivial) (safe_requestNode _ _ _ _ ready) valid ranges fuel done
  exact correct.closed_original (done_closed_of_ranges emptyGuard conjoin fuel left right value state after valid
    leftAvailable rightAvailable heap ranges done)

end MicroCFTA.SourceRecursiveIntersectionNative
