import MicroCFTA.InternedFreeNameHeap
import MicroCFTA.InternedCallbackTransport

/-!
# Actual free-name fields for source constructor composition

Ordinary node normalization keeps only live edges. Union normalization
keeps every operand free name. Callback normalization preserves every
name other than its supplied local. The proofs include canonical cache
readback and the original ordered source operands.
-/
namespace MicroCFTA.InternedFreeNameConstructors
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedNestedSpecialization
open InternedNestedMissReadback InternedStoredMuOrigins InternedNormalizationFree
open InternedEdgeResidency InternedFreshProbeKeys
open InternedBinderProtocol (Reference)

/-- An actual ordinary result contains exactly the free names of its live source edge children. -/
theorem node_membership [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (normal : Normal state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (name : Reference) :
    name ∈ (run (makeNode edges) state).1.free ↔
      ∃ edge ∈ edges, edge.children.any (fun child => child.referenceOf == .empty) = false ∧
        ∃ child ∈ edge.children, name ∈ child.free := by
  rw [makeNode_free edges state normal.facts.coherent normal.facts.linked resident, childFree_member]
  constructor
  · rintro ⟨child, included, present⟩
    obtain ⟨edge, selected, member⟩ := List.mem_flatMap.mp included
    have kept := canonicalEdges_member _ edge selected
    have original := List.mem_filter.mp kept
    refine ⟨edge, original.1, ?_, child, member, present⟩
    simpa using original.2
  · rintro ⟨edge, included, live, child, member, present⟩
    have kept : edge ∈ surviving edges := List.mem_filter.mpr ⟨included, by simpa using live⟩
    have selected : edge ∈ canonicalEdges (surviving edges) :=
      canonicalEdges_retains state normal.facts.coherent (surviving edges) edge
        (fun original originalKept => resident original (List.mem_filter.mp originalKept).1) kept
    exact ⟨child, List.mem_flatMap.mpr ⟨edge, selected, member⟩, present⟩

/-- Actual union normalization has the free-name set of all original operands. -/
theorem union_membership [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (normal : Normal state) (inputs : Values state values) (name : Reference) :
    name ∈ (run (makeUnion values) state).1.free ↔ ∃ value ∈ values, name ∈ value.free :=
  makeUnion_free values state normal.facts.coherent normal.facts.cached normal.facts.linked normal.live inputs name

/-- Root normalization of an actual completed body preserves each other free name. -/
theorem callback_other [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name other : Reference) (different : other ≠ name)
    (before afterRaw after : State Symbol Guard) (normal : Normal before)
    (inputs : Values before (.reference name :: environment)) (raw value : Value Symbol Guard)
    (rawDone : build body (.reference name :: environment) before = .done raw afterRaw)
    (done : callback body environment name before = .done value after) :
    other ∈ value.free ↔ other ∈ raw.free := by
  have afterNormal : Normal afterRaw := by
    simpa only [rawDone, Outcome.state] using build_normal body (.reference name :: environment) before normal inputs
  have available := (build_verified body (.reference name :: environment) before normal.facts inputs).result raw afterRaw rawDone
  have result := done
  simp only [callback, rawDone, Outcome.bind, work, Outcome.done.injEq] at result
  have filtered := result.1
  rw [← filtered]
  exact filter_free_other name other raw afterRaw afterNormal.facts.coherent afterNormal.facts.cached
    afterNormal.facts.linked afterNormal.live available different

end MicroCFTA.InternedFreeNameConstructors
