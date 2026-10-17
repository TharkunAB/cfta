import MicroCFTA.SourceCurrentStoredSubstitutionOrigins
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
namespace MicroCFTA.StoredSubstitutionOriginKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentStoredSubstitutionOrigins
private def old : Reference := .uninterned 42
private def plan : Syntax Nat Bool := .node [.mk 3 false [
  .var 0, .binder false (.node [.mk 4 true [.var 1]])]]
private def built := build plan [.reference old] empty
private def original : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def before := built.state
private theorem actual : built = .done original before := by cbv
private theorem inputs : Values (empty : State Nat Bool) [.reference old] := by
  intro value member
  cases List.mem_singleton.mp member
  exact InternedNestedProvenance.ordinary_available empty 42
private theorem semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before :=
  SourceRecursiveIntersectionSemanticHeap.source plan [.reference old] empty
    SourceRecursiveIntersectionSemanticHeap.empty_heap inputs
private theorem available : Available before original :=
  (InternedFreshOrdinaryFacts.build_verified plan [.reference old] empty InternedNestedFacts.empty_facts inputs).result
    original before actual
private theorem covered : Covered [] before :=
  InternedFreshOrdinaryCoverage.build_covered plan [.reference old] empty InternedConstructorTemplates.empty_valid
    InternedRecordCoherence.empty_correct.2 original before actual
private def nodeFields (value : Value Nat Bool) : Interned NodeKey × List (EdgeValue Nat Bool) × Nat × List Reference :=
  match value with
  | .node entry rows level free => (entry, rows, level, free)
  | _ => (⟨0,.node []⟩, [], 0, [])
private def fields := nodeFields original
private theorem nodeShape : original = .node fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 := by cbv
private def nested : Value Nat Bool → Bool
  | .node _ [row] _ _ => match row.children with | [_, .mu ..] => true | _ => false
  | _ => false
private theorem nested_original : nested original = true := by cbv
private theorem opened : fields.2.2.2 ≠ [] := by cbv; intro equal; cases equal
private def environment : InternedStoredSubstitution.Environment Nat Bool :=
  InternedStoredSubstitutionRebind.replacement old (.reference .depth)
private theorem replacements (state : State Nat Bool) : InternedStoredSubstitution.Replacements state environment := by
  intro name value found
  unfold environment InternedStoredSubstitutionRebind.replacement at found
  split at found
  · cases found
    exact InternedNestedProvenance.depth_available state
  · cases found

/-- Initial semantic facts construct a node row receipt with an actual open nested raw Mu child. -/
theorem produced_node :
    build plan [.reference old] empty = .done original before ∧ nested original = true ∧
    ∃ result after, InternedFreshOrdinaryStoredSubstitution.execute original environment before = .done result after ∧
      NodeRows (InternedStoredSubstitution.leaves original) environment fields.2.1 before result after ∧
      Nonempty (SourceCurrentNativeMuPublication.History before after) := by
  have sourceAvailable : Available before (.node fields.1 fields.2.1 fields.2.2.1 fields.2.2.2) := nodeShape ▸ available
  obtain ⟨result, after, done, _semantic, _covered, _available, history, branch⟩ :=
    node_complete fields.1 fields.2.1 fields.2.2.1 fields.2.2.2 environment before semantic covered
      sourceAvailable (replacements before)
  have rows : NodeRows (InternedStoredSubstitution.leaves original) environment fields.2.1 before result after := by
    rcases branch with closed | rebuilt
    · exact False.elim (opened closed.1)
    · simpa only [← nodeShape] using rebuilt.2
  exact ⟨actual, nested_original, result, after, by simpa only [← nodeShape] using done, rows, history⟩

private def members : List (Value Nat Bool) := [original, .reference old]
private def unionMade := run (makeUnion members) before
private def unionOriginal := unionMade.1
private def unionBefore := unionMade.2
private def unionFields (value : Value Nat Bool) : Interned NodeKey × List (Value Nat Bool) × Nat × List Reference :=
  match value with
  | .union entry values level free => (entry, values, level, free)
  | _ => (⟨0,.node []⟩, [], 0, [])
private def parts := unionFields unionOriginal
private theorem unionShape : unionOriginal = .union parts.1 parts.2.1 parts.2.2.1 parts.2.2.2 := by cbv
private theorem unionOpened : parts.2.2.2 ≠ [] := by cbv; intro equal; cases equal
private theorem membersAvailable : Values before members := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact available
  · cases List.mem_singleton.mp member
    exact InternedNestedProvenance.ordinary_available before 42
private theorem unionSemantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap unionBefore :=
  SourceRecursiveIntersectionSemanticHeap.union members before semantic membersAvailable
private theorem unionAvailable : Available unionBefore unionOriginal :=
  (InternedNestedFacts.union_verified members before semantic.1.normal.facts membersAvailable).result _ _ rfl
private theorem unionCovered : Covered [] unionBefore :=
  InternedNestedCoverage.run_covered (makeUnion members) before semantic.1.normal.facts.coherent.valid covered

/-- The actual union member sequence constructs its epsilon row origins and causal history from its initial cache. -/
theorem produced_union :
    run (makeUnion members) before = (unionOriginal, unionBefore) ∧ parts.2.1.length = 2 ∧ nested original = true ∧
    ∃ result after, InternedFreshOrdinaryStoredSubstitution.execute unionOriginal environment unionBefore = .done result after ∧
      UnionRows environment parts.2.1 unionBefore result after ∧
      Nonempty (SourceCurrentNativeMuPublication.History unionBefore after) := by
  have sourceAvailable : Available unionBefore (.union parts.1 parts.2.1 parts.2.2.1 parts.2.2.2) :=
    unionShape ▸ unionAvailable
  obtain ⟨result, after, done, _semantic, _covered, _available, history, branch⟩ :=
    union_complete parts.1 parts.2.1 parts.2.2.1 parts.2.2.2 environment unionBefore unionSemantic unionCovered
      sourceAvailable (replacements unionBefore)
  have rows : UnionRows environment parts.2.1 unionBefore result after := by
    rcases branch with closed | rebuilt
    · exact False.elim (unionOpened closed.1)
    · exact rebuilt.2
  exact ⟨rfl, by cbv, nested_original, result, after, by simpa only [← unionShape] using done, rows, history⟩
end MicroCFTA.StoredSubstitutionOriginKernels
#check @MicroCFTA.StoredSubstitutionOriginKernels.produced_node
#print axioms MicroCFTA.StoredSubstitutionOriginKernels.produced_node
#check @MicroCFTA.StoredSubstitutionOriginKernels.produced_union
#print axioms MicroCFTA.StoredSubstitutionOriginKernels.produced_union
