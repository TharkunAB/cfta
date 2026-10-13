import MicroCFTA.SourceColdSharedRowsLanguage
import MicroCFTA.SourceSizedReferenceAPI

/-!
# Exact finite tables and size classes after cold shared traversal

The completed trace supplies the entire map domain. Ascending-key readback
copies its actual rows. The empty-root table retains the separate empty state.
The table has the original guarded physical language and exact Sized laws.
Completion of the cold trace remains an explicit premise.
-/
namespace MicroCFTA.SourceColdSharedRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open MergedPhysicalWarmup Language RecursiveSize
open SourcePreparedSharedRows (reference encode)

/-- Native readback uses ascending map keys, with a separate empty-root table. -/
def table (rows : Rows Symbol Guard) (keys : List Nat) (root : Value Symbol Guard) :
    List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard)) :=
  match reference root with
  | none => [(.empty, [])]
  | some _ => SourceInternedRows.table (heap rows) keys

/-- The exact finite map domain makes ascending table readback equal to the output graph. -/
theorem table_graph (rows : Rows Symbol Guard) (keys : List Nat)
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (meaning : Guard → Term Symbol → Bool) :
    FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning (SourceInternedRows.table (heap rows) keys)) =
      SourceInternedRows.graph (heap rows) meaning := by
  funext state
  cases state with
  | empty => exact SourceInternedRows.interpreted_empty _ meaning keys
  | interned identity =>
      rw [SourceInternedRows.interpreted_table]
      by_cases member : identity ∈ keys
      · simp only [ite_eq_left member]
      · have missing : rows identity = none := by
          cases found : rows identity with
          | none => rfl
          | some edges => exact False.elim (member ((domain identity).mp ⟨edges, found⟩))
        simp [member, SourceInternedRows.graph, heap, missing]

/-- A completed cold trace derives a finite distinct domain for its actual output map. -/
theorem Trace.domain [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {rows : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state (fun _ => none) pending rows final) :
    ∃ keys : List Nat, keys.Nodup ∧ ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys := by
  obtain ⟨keys, distinct, _, exact⟩ := trace.discovery
  exact ⟨keys, distinct, by simpa using exact⟩

/-- Actual completed cold traversal and ascending readback retain the original physical language. -/
theorem Trace.table_language [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (closed : value.free = []) (keys : List Nat)
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (meaning : Guard → Term Symbol → Bool) (term : Term Symbol) :
    Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning (table rows keys value))) (encode value) term ↔
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term := by
  cases same : reference value with
  | none =>
      have empty : value = .empty := by
        cases value <;> simp only [reference] at same <;> try contradiction
        rfl
      subst value
      constructor
      · intro accepted
        cases accepted with
        | node edge children member runs guard =>
            simp [table, reference, SourceInternedRows.interpretedRows, FTAValidation.rowFor, encode, SourceInternedRows.stateOf] at member
      · exact False.elim ∘ MergedPhysicalUnion.empty_rejects state meaning term
  | some identity =>
      simp only [table, same]
      rw [table_graph rows keys domain meaning]
      exact trace.language_exact state final value rows facts prepared available closed meaning term

/-- A completed actual cold walk yields a finite table and stable executable bounds with exact language. -/
theorem Trace.table_correct [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (closed : value.free = []) :
    ∃ keys raw outer inner, keys.Nodup ∧
      (∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys) ∧ raw = table rows keys value ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        collect largerOuter largerInner state (fun _ => none) [value] = .done rows final) ∧
      (∀ meaning term, Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning raw)) (encode value) term ↔
        EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term) := by
  obtain ⟨keys, distinct, domain⟩ := trace.domain
  obtain ⟨outer, inner, done⟩ := trace.finite
  exact ⟨keys, table rows keys value, outer, inner, distinct, domain, rfl, done,
    trace.table_language state final value rows facts prepared available closed keys domain⟩

/-- Actual cold output tables have exact finite distinct size classes and both rank inverses. -/
theorem Trace.sized [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (closed : value.free = []) (meaning : Guard → Term Symbol → Bool) :
    ∃ keys raw outer inner, keys.Nodup ∧ raw = table rows keys value ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        collect largerOuter largerInner state (fun _ => none) [value] = .done rows final) ∧
      (let A := FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning raw)
       let classes := fun size => SourceSizedReference.classes A size (encode value)
       (∀ size term, term ∈ classes size ↔
         EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term ∧ nodeSize term = size) ∧
       (∀ size, SourceSizedReference.ClassEvaluation A (size + 1) size (encode value) (classes size)) ∧
       (∀ bound, (SourceSizedQueries.through classes bound).Nodup ∧
         (SourceSizedQueries.through classes bound).Pairwise (fun first second => nodeSize first ≤ nodeSize second) ∧
         ∀ term, term ∈ SourceSizedQueries.through classes bound ↔
           EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term ∧ nodeSize term ≤ bound) ∧
       (∀ term position, SourceSizedQueries.rank classes nodeSize term = some position ↔
         SourceSizedQueries.unrank classes position = some term)) := by
  obtain ⟨keys, raw, outer, inner, distinct, _, rawEq, done, exactLanguage⟩ :=
    trace.table_correct state final value rows facts prepared available closed
  refine ⟨keys, raw, outer, inner, distinct, rawEq, done, ?_⟩
  dsimp only
  let A := FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning raw)
  refine ⟨?_, (fun size => SourceSizedReference.classes_evaluation_bound A size (encode value)), ?_, ?_⟩
  · intro size term
    rw [SourceSizedReference.mem_classes_iff, exactLanguage meaning term]
  · intro bound
    refine ⟨SourceSizedReferenceAPI.through_nodup A (encode value) bound,
      SourceSizedReferenceAPI.through_ordered A (encode value) bound, ?_⟩
    intro term
    rw [SourceSizedReferenceAPI.through_exact, exactLanguage meaning term]
  · intro term position
    exact ⟨SourceSizedReferenceAPI.unrank_rank A (encode value) term position,
      SourceSizedReferenceAPI.rank_unrank A (encode value) term position⟩

end MicroCFTA.SourceColdSharedRows
