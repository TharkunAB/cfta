import MicroCFTA.SourceCurrentEnumerationOrder
import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.InternedGuardedLanguage

/-!
# Accepting selected edges of an actual ordinary parent

A permutation retains each accepting resident edge.
Raw interned order selects the actual stored rows.
The canonical closure also retains acceptance when its actual map or fallback
contains a permutation of those rows. Constructing that map remains separate.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectorLanguage
open InternedConstructorTemplates InternedProbeProvenance Language

/-- A permutation of an available parent's rows retains an accepting resident edge. -/
theorem selected_accepting_of_perm
    (heap : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready heap)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges selectedEdges : List (EdgeValue Symbol Guard)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (available : Available heap (.node entry edges depth free))
    (sameRows : selectedEdges.Perm edges)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (term : Term Symbol)
    (accepted : InternedGuardedLanguage.meaning holds ambient (.node entry edges depth free) term) :
    ∃ edge, edge ∈ selectedEdges ∧ edge ∈ edges ∧
      InternedEdgeResidency.EdgeResident heap edge ∧
      InternedGuardedLanguage.edgeMeaning holds ambient edge term := by
  obtain ⟨⟨edge, member⟩, edgeAccepted⟩ := accepted
  refine ⟨edge, sameRows.mem_iff.mpr member, member, ?_, edgeAccepted⟩
  exact InternedEdgeResidency.resident_edges heap ready.semantic.1.normal.facts.linked
    (.node entry edges depth free) available.resident edge member

/-- The actual raw interned selector retains an accepting edge of the current parent. -/
theorem interned_accepting
    (heap : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready heap)
    (root : Value Symbol Guard)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (available : Available heap (.node entry edges depth free))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (term : Term Symbol)
    (accepted : InternedGuardedLanguage.meaning holds ambient (.node entry edges depth free) term) :
    ∃ edge,
      edge ∈ SourceCurrentEnumerationOrder.internedEdgesOf InternedEdgeResidency.nodeEdges root
        (.node entry edges depth free) ∧ edge ∈ edges ∧
      InternedEdgeResidency.EdgeResident heap edge ∧
      InternedGuardedLanguage.edgeMeaning holds ambient edge term := by
  apply selected_accepting_of_perm heap ready entry edges _ depth free available
    (List.Perm.refl edges) holds ambient term accepted

/-- The source-shaped canonical closure retains acceptance under its actual row correspondence. -/
theorem canonical_accepting {Weight : Type}
    (heap : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready heap)
    (identity : Value Symbol Guard → Int)
    (canonicalOrder : Value Symbol Guard → Cache.Table Int (List (EdgeValue Symbol Guard)))
    (canonicalEdges : Value Symbol Guard → List (EdgeValue Symbol Guard))
    (le : Weight → Weight → Bool) (weights : Option (EdgeValue Symbol Guard → Weight))
    (root : Value Symbol Guard)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Guard)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (available : Available heap (.node entry edges depth free))
    (actualRows : ((canonicalOrder root (identity (.node entry edges depth free))).getD
      (canonicalEdges (.node entry edges depth free))).Perm edges)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (term : Term Symbol)
    (accepted : InternedGuardedLanguage.meaning holds ambient (.node entry edges depth free) term) :
    ∃ edge,
      edge ∈ SourceCurrentEnumerationOrder.canonicalEdgesOf identity canonicalOrder canonicalEdges
        le weights root (.node entry edges depth free) ∧ edge ∈ edges ∧
      InternedEdgeResidency.EdgeResident heap edge ∧
      InternedGuardedLanguage.edgeMeaning holds ambient edge term := by
  apply selected_accepting_of_perm heap ready entry edges _ depth free available
    ((SourceCurrentEnumerationOrder.canonical_perm identity canonicalOrder canonicalEdges le weights
      root (.node entry edges depth free)).trans actualRows) holds ambient term accepted

end MicroCFTA.SourcePruningEnumerationSelectorLanguage
