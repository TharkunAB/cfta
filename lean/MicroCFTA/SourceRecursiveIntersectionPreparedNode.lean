import MicroCFTA.InternedStoredClosedMuCompletion
import MicroCFTA.InternedOrdinaryUnionReadback

/-!
# Preparation and free names of actual ordinary node construction

Canonical row selection retains only original child records. Node readback
therefore preserves preparation without open Mu requests. If all original
child names equal one name, the returned free list is empty or that singleton.
-/
namespace MicroCFTA.SourceRecursiveIntersectionPreparedNode
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedFreshProbeKeys InternedEdgeResidency InternedNormalizationFree
open InternedStoredClosedMuCompletion (PreparedWithoutMu)
open InternedBinderProtocol (Reference)

variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual canonical node construction preserves preparation of every original row child. -/
theorem makeNode_prepared (rows : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (resident : ∀ row ∈ rows, EdgeResident state row)
    (prepared : ∀ child ∈ rows.flatMap EdgeValue.children, PreparedWithoutMu child) :
    PreparedWithoutMu (run (makeNode rows) state).1 := by
  have selected : ∀ row ∈ canonicalEdges (surviving rows), EdgeResident state row :=
    fun row member => resident row (List.mem_filter.mp (canonicalEdges_member _ row member)).1
  have selectedPrepared : ∀ child ∈ (canonicalEdges (surviving rows)).flatMap EdgeValue.children,
      PreparedWithoutMu child := by
    intro child member
    obtain ⟨row, included, inner⟩ := List.mem_flatMap.mp member
    exact prepared child (List.mem_flatMap.mpr
      ⟨row, (List.mem_filter.mp (canonicalEdges_member _ row included)).1, inner⟩)
  unfold makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa [same] using selected)
    simp only [run, exactResult, identifyNode]
    exact .node _ _ _ _ (by simpa [same] using selectedPrepared)

/-- The actual normalized node has no free names or exactly the supplied name. -/
theorem makeNode_free_empty_or_singleton (rows : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (resident : ∀ row ∈ rows, EdgeResident state row) (name : Reference)
    (only : ∀ child ∈ rows.flatMap EdgeValue.children, ∀ other ∈ child.free, other = name) :
    (run (makeNode rows) state).1.free = [] ∨ (run (makeNode rows) state).1.free = [name] := by
  rw [makeNode_free rows state facts.coherent facts.linked resident]
  unfold childFree
  let names := ((canonicalEdges (surviving rows)).flatMap EdgeValue.children).flatMap Value.free
  have onlyNames : ∀ other ∈ names, other = name := by
    intro other member
    obtain ⟨child, included, free⟩ := List.mem_flatMap.mp member
    obtain ⟨row, selected, inner⟩ := List.mem_flatMap.mp included
    exact only child (List.mem_flatMap.mpr
      ⟨row, (List.mem_filter.mp (canonicalEdges_member _ row selected)).1, inner⟩) other free
  change canonicalFree names = [] ∨ canonicalFree names = [name]
  cases namesEq : names with
  | nil =>
      left
      simp [canonicalFree]
  | cons first rest =>
      rw [namesEq] at onlyNames
      right
      apply InternedOrdinaryUnionReadback.canonicalFree_singleton _ name
      · have same := onlyNames first List.mem_cons_self
        subst first
        exact List.mem_cons_self
      · exact onlyNames

end MicroCFTA.SourceRecursiveIntersectionPreparedNode
