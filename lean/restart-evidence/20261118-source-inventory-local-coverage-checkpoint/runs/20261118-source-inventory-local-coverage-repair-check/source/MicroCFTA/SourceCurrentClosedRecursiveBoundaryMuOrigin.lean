import MicroCFTA.InternedStoredMuOrigins
import MicroCFTA.SourceCurrentRequiredUnionNormal
import MicroCFTA.InternedBoundaryProvenance
import MicroCFTA.InternedOrdinaryUnionReadback
import MicroCFTA.MergedOrdinaryHeight

namespace MicroCFTA.SourceCurrentClosedRecursiveBoundaryMuOrigin
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBoundaryAtoms (atoms many_member)
open InternedBinderProtocol (NodeRef)
set_option autoImplicit false

/- Note [Closed irreducible boundary origin]
Canonical unions contain no empty or nested union members.
Closedness excludes reference members. An irreducible union must therefore
contain an actual Mu member. NoNewMu retains its complete source record.
This structural argument makes no guard or language claim.
-/

theorem closed_recursive_boundary_has_source_mu
    {Symbol Guard : Type}
    (sourceHeap heap : InternedConstructorTemplates.State Symbol Guard)
    (normal : InternedStoredMuOrigins.Normal heap)
    (irreducible : SourceCurrentRequiredUnionNormal.UnionNormal heap)
    (inventory : InternedShallowHeap.NoNewMu sourceHeap heap)
    (value : InternedConstructorTemplates.Value Symbol Guard)
    (available : InternedProbeProvenance.Available heap value)
    (closed : value.free = [])
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    ∃ (key : InternedBinderProtocol.NodeKey)
      (entry : Cache.Interned InternedBinderProtocol.NodeKey)
      (body depth ordinary : InternedConstructorTemplates.Value Symbol Guard),
      sourceHeap.nodeRecords key = some (.mu entry body depth ordinary)
 := by
  classical
  cases value with
  | empty | reference | node =>
      simp [MergedOrdinaryHeight.recursiveBoundary] at boundary
  | mu entry body depth ordinary =>
      exact ⟨entry.key, entry, body, depth, ordinary,
        inventory entry.key entry body depth ordinary (available.resident entry rfl)⟩
  | union entry members depth free =>
      have flat := InternedUnionNormalForm.resident_flat heap normal.flat
        (.union entry members depth free) available.resident
      have nonempty := InternedUnionNonemptyMembers.resident_membersNonempty heap normal.members
        (.union entry members depth free) available.resident
      have noOrdinary : ordinaryEdges members = none :=
        irreducible entry.key (.union entry members depth free) (available.resident entry rfl)
      apply Classical.byContradiction
      intro missing
      have allNodes : ∀ member ∈ members, InternedOrdinaryUnionReadback.Ordinary member := by
        intro member included
        cases member with
        | empty => exact False.elim (nonempty .empty included rfl)
        | reference name =>
            have occurrence : NodeRef.ref name ∈ atoms (.union entry members depth free) := by
              simpa only [atoms] using (many_member members (.ref name)).mpr
                ⟨.reference name, included, by simp only [atoms, List.mem_singleton]⟩
            have escaped := InternedBoundaryProvenance.ref_free name
              (.union entry members depth free) heap normal.facts.coherent available occurrence
            simp only [closed, List.not_mem_nil] at escaped
        | node other edges otherDepth otherFree =>
            exact ⟨other, edges, otherDepth, otherFree, rfl⟩
        | union other otherMembers otherDepth otherFree =>
            exact False.elim (flat _ included)
        | mu other body otherDepth ordinary =>
            exact False.elim (missing ⟨other.key, other, body, otherDepth, ordinary,
              inventory other.key other body otherDepth ordinary
                ((available.children _ included).resident other rfl)⟩)
      have ordinary := InternedOrdinaryUnionReadback.ordinaryEdges_eq members allNodes
      rw [noOrdinary] at ordinary
      cases ordinary

end MicroCFTA.SourceCurrentClosedRecursiveBoundaryMuOrigin

#print axioms MicroCFTA.SourceCurrentClosedRecursiveBoundaryMuOrigin.closed_recursive_boundary_has_source_mu
