import MicroCFTA.InternedNormalizationFree
import Init.Data.List.MinMax

/-!
# Binder costs of actual free-reference occurrences

A cost counts Mu records on a path to a free reference. Ordinary children
and union members add no cost. Each binder excludes its own reference.
The minimum is an executable candidate measure. This module proves its
connection to actual cached free names, without asserting unfolding progress.
-/
namespace MicroCFTA.InternedFreeOccurrenceRank
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNormalizationFree
open InternedBinderProtocol (Reference NodeKey)

mutual
/-- Actual source occurrences retain their free name and the number of enclosing Mu records. -/
def costs : Value Symbol Guard → List (Reference × Nat)
  | .empty => []
  | .reference name => [(name, 0)]
  | .node _ edges _ _ => edgeCosts edges
  | .union _ members _ _ => manyCosts members
  | .mu entry body _ _ =>
      ((costs body).filter (fun item => item.1 != .interned entry.identity)).map (fun item => (item.1, item.2 + 1))
termination_by value => sizeOf value

/-- Union members and ordinary ordered children retain every actual occurrence. -/
def manyCosts : List (Value Symbol Guard) → List (Reference × Nat)
  | [] => []
  | first :: rest => costs first ++ manyCosts rest
termination_by values => sizeOf values

/-- Original edge metadata contributes no binder frame to its children. -/
def edgeCosts : List (EdgeValue Symbol Guard) → List (Reference × Nat)
  | [] => []
  | .mk _ children :: rest => manyCosts children ++ edgeCosts rest
termination_by edges => sizeOf edges
end

mutual
/-- The executable occurrence list has exactly the free names in actual coherent source metadata. -/
theorem costs_free (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (name : Reference) :
    (∃ cost, (name, cost) ∈ costs value) ↔ name ∈ value.free := by
  cases value with
  | empty => simp [costs, Value.free]
  | reference own => simp [costs, Value.free]
  | node entry edges depth free =>
      rw [Value.free, node_free state coherent entry edges depth free available.resident, childFree_member]
      simpa only [costs] using edgeCosts_free edges state coherent (fun child member => available.children child member) name
  | union entry members depth free =>
      rw [Value.free, union_free state coherent entry members depth free available.resident, childFree_member]
      simpa only [costs] using manyCosts_free members state coherent (fun child member => available.children child member) name
  | mu entry body depth ordinary =>
      have inner := costs_free body state coherent (available.children body (by simp [InternedProbeProvenance.children])) name
      constructor
      · rintro ⟨count, member⟩
        simp only [costs] at member
        obtain ⟨⟨actual, prior⟩, selected, equal⟩ := List.mem_map.mp member
        have same : actual = name := congrArg Prod.fst equal
        subst actual
        have kept := List.mem_filter.mp selected
        have free := inner.mp ⟨prior, kept.1⟩
        simpa [Value.free, free] using kept.2
      · intro member
        have selected : name ∈ body.free ∧ name ≠ .interned entry.identity := by simpa [Value.free] using member
        obtain ⟨count, present⟩ := inner.mpr selected.1
        refine ⟨count + 1, ?_⟩
        simp only [costs]
        exact List.mem_map.mpr ⟨(name, count), List.mem_filter.mpr ⟨present, by simpa using selected.2⟩, rfl⟩
termination_by sizeOf value

/-- Child occurrence names agree with the original union of child free sets. -/
theorem manyCosts_free (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ values, Available state value) (name : Reference) :
    (∃ cost, (name, cost) ∈ manyCosts values) ↔ ∃ value ∈ values, name ∈ value.free := by
  cases values with
  | nil => simp [manyCosts]
  | cons first rest =>
      simp only [manyCosts, List.mem_append, exists_or]
      rw [costs_free first state coherent (available first (by simp)),
        manyCosts_free rest state coherent (fun value member => available value (by simp [member]))]
      simp
termination_by sizeOf values

/-- Source edge occurrence names agree with its actual ordered child payloads. -/
theorem edgeCosts_free (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value) (name : Reference) :
    (∃ cost, (name, cost) ∈ edgeCosts edges) ↔ ∃ value ∈ edges.flatMap EdgeValue.children, name ∈ value.free := by
  cases edges with
  | nil => simp [edgeCosts]
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [edgeCosts, List.mem_append, exists_or]
          rw [manyCosts_free children state coherent (fun value member => available value (by simp [EdgeValue.children, member])),
            edgeCosts_free rest state coherent (fun value member => available value (by simp [EdgeValue.children, member]))]
          simp only [List.flatMap_cons, EdgeValue.children, List.mem_append, or_and_right, exists_or]
termination_by sizeOf edges
end

/-- Closed records use zero. Open records use the least actual free-occurrence cost. -/
def rank (value : Value Symbol Guard) : Nat := ((costs value).map Prod.snd).min?.getD 0

/-- An open coherent source record has an actual minimum occurrence and a lower bound for every occurrence. -/
theorem rank_spec (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (opened : value.free ≠ []) :
    (∃ name, (name, rank value) ∈ costs value) ∧ ∀ name count, (name, count) ∈ costs value → rank value ≤ count := by
  obtain ⟨name, named⟩ := List.exists_mem_of_ne_nil value.free opened
  obtain ⟨count, present⟩ := (costs_free value state coherent available name).mpr named
  have costsNonempty : (costs value).map Prod.snd ≠ [] := by
    intro none
    have member : count ∈ (costs value).map Prod.snd := List.mem_map.mpr ⟨(name, count), present, rfl⟩
    simp [none] at member
  cases least : ((costs value).map Prod.snd).min? with
  | none => exact False.elim (costsNonempty (List.min?_eq_none_iff.mp least))
  | some minimum =>
      have spec := List.min?_eq_some_iff.mp least
      have rankEq : rank value = minimum := by simp [rank, least]
      rw [rankEq]
      constructor
      · obtain ⟨⟨name, count⟩, member, same⟩ := List.mem_map.mp spec.1
        exact ⟨name, (congrArg (fun count => (name, count)) same) ▸ member⟩
      · intro name count member
        exact spec.2 count (List.mem_map.mpr ⟨(name, count), member, rfl⟩)

/-- Every queried open Mu has positive free-occurrence rank. -/
theorem mu_positive (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state (.mu entry body depth ordinary))
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    0 < rank (.mu entry body depth ordinary) := by
  obtain ⟨name, member⟩ := (rank_spec (.mu entry body depth ordinary) state coherent available opened).1
  simp only [costs] at member
  obtain ⟨⟨actual, prior⟩, _, equal⟩ := List.mem_map.mp member
  have same := congrArg Prod.snd equal
  omega

end MicroCFTA.InternedFreeOccurrenceRank
