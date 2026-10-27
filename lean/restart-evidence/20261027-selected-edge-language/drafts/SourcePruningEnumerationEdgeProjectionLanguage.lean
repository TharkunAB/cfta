import MicroCFTA.SourcePruningEnumerationConstraint
import MicroCFTA.SourceEqualityAnnotationHeap
import MicroCFTA.SourceEqualityRequiredCache

/-!
# Language of an actual selected constraint projection

A successful projection retains the complete guard meaning. Its cached
normalization premise is separate from native record readiness. A current
annotation heap supplies that premise for an actual selected edge.
-/
namespace MicroCFTA.SourcePruningEnumerationEdgeProjectionLanguage
open Language EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance

variable {Formula : Type}

/-- A successful cached projection gives valid tries and the complete guard equivalence. -/
theorem projected_complete [DecidableEq Formula]
    (constraint : SourceSymbolicIndex.Constraint Formula)
    (cached : SourceEqualityGuardReadback.Cached constraint.equalities)
    (tries : List EqualityTrie.Trie)
    (residual : Option (SourceSymbolicIndex.Constraint Formula))
    (projected : SourcePruningEnumerationConstraint.project constraint = some (tries, residual)) :
    (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      ∀ (formulas : SourceGuards.Formulas Formula)
        (solver : SourceGuards.Entailment Formula) (term : Term (SourceObservations.Label Formula)),
        SourceEqualityPCSGuard.holds formulas solver constraint term = true ↔
          (∀ trie ∈ tries, EqualityHolds term trie) ∧
            ResidualHolds (fun guard candidate =>
              SourceEqualityPCSGuard.holds formulas solver guard candidate = true) residual term := by
  have complete := SourcePruningEnumerationConstraint.project_complete constraint cached
  cases source : SourceCompactGuards.sourceEqualities constraint with
  | none =>
      simp only [source] at complete
      have impossible := complete.1.symm.trans projected
      cases impossible
  | some classes =>
      simp only [source] at complete
      have same := Option.some.inj (complete.1.symm.trans projected)
      have triesSame := congrArg Prod.fst same
      have residualSame := congrArg Prod.snd same
      rw [← triesSame, ← residualSame]
      exact ⟨complete.2.1, complete.2.2.2⟩

/-- A current annotation heap supplies cached projection semantics for the selected resident edge. -/
theorem selected_projected_complete [DecidableEq Formula]
    (heap : State (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula)))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue (SourceObservations.Label Formula) (SourceSymbolicIndex.Constraint Formula))
    (ready : SourceEqualityRequiredCache.Ready heap)
    (annotated : SourceEqualityAnnotationHeap.Heap
      (fun guard => SourceEqualityGuardReadback.Cached guard.equalities) heap)
    (parentAvailable : Available heap (.node parentEntry edges depth free))
    (selected : edge ∈ edges)
    (tries : List EqualityTrie.Trie)
    (residual : Option (SourceSymbolicIndex.Constraint Formula))
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
    (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧
      ∀ (formulas : SourceGuards.Formulas Formula)
        (solver : SourceGuards.Entailment Formula) (term : Term (SourceObservations.Label Formula)),
        SourceEqualityPCSGuard.holds formulas solver edge.entry.key.constraint term = true ↔
          (∀ trie ∈ tries, EqualityHolds term trie) ∧
            ResidualHolds (fun guard candidate =>
              SourceEqualityPCSGuard.holds formulas solver guard candidate = true) residual term := by
  have resident : InternedEdgeResidency.EdgeResident heap edge :=
    InternedEdgeResidency.resident_edges heap ready.semantic.1.normal.facts.linked
      (.node parentEntry edges depth free) parentAvailable.resident edge selected
  exact projected_complete edge.entry.key.constraint
    (annotated edge.entry.key edge resident) tries residual projected

end MicroCFTA.SourcePruningEnumerationEdgeProjectionLanguage
