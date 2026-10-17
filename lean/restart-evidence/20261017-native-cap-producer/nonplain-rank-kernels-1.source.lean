import MicroCFTA.SourceCurrentConstrainedCapNonplainRank

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.NonplainRankChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentHereditaryNativeScope (Bindings)
open SourceCurrentConstrainedCapNonplainRank
variable {Symbol Guard : Type}

/-- A constrained shell with an actual hereditary Mu child has strict child and union descent. -/
theorem mixed_shell (annotation : Guard → Prop) (nodeEntry unionEntry : Interned NodeKey)
    (rowEntry : Interned (EdgeKey Symbol Guard)) (muEntry : Interned NodeKey)
    (body probe ordinary : Value Symbol Guard) (level : Nat) (free : List Reference)
    (muAnnotated : Annotated annotation (.mu muEntry body probe ordinary))
    (badGuard : ¬ annotation rowEntry.key.constraint) :
    let atom : Value Symbol Guard := .mu muEntry body probe ordinary
    let row : EdgeValue Symbol Guard := .mk rowEntry [atom]
    let shell : Value Symbol Guard := .node nodeEntry [row] level free
    let alternatives : Value Symbol Guard := .union unionEntry [shell, atom] level free
    Cap annotation 1 shell ∧ Cap annotation 1 alternatives ∧
      rank annotation atom = 0 ∧ 0 < rank annotation shell ∧
      pairRank annotation atom atom < pairRank annotation shell shell ∧
      pairRank annotation shell atom < pairRank annotation alternatives atom := by
  dsimp only
  let atom : Value Symbol Guard := .mu muEntry body probe ordinary
  let row : EdgeValue Symbol Guard := .mk rowEntry [atom]
  let shell : Value Symbol Guard := .node nodeEntry [row] level free
  have nonplain : ¬ Annotated annotation shell := by
    intro annotated
    have inherited := SourceCurrentHereditaryConstructors.node_edge annotated row (by simp [shell, nodeEdges])
    exact badGuard inherited.1
  have cap : Cap annotation 1 shell := by
    apply Cap.node 0
    intro child member
    have same : child = atom := by simpa only [List.flatMap_cons, List.flatMap_nil, EdgeValue.children, List.append_nil, List.mem_singleton] using member
    exact same ▸ Cap.plain 0 muAnnotated
  have unionCap : Cap annotation 1 (.union unionEntry [shell, atom] level free) := by
    apply Cap.union 1
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact cap
    · exact List.mem_singleton.mp member ▸ Cap.plain 1 muAnnotated
  have unionNonplain : ¬ Annotated annotation (.union unionEntry [shell, atom] level free) := by
    intro annotated
    exact nonplain (SourceCurrentHereditaryConstructors.union_member annotation _ annotated shell (by simp [unionMembers]))
  have zipped := zip_pair_lt annotation shell shell (Or.inl nonplain) row row
    (by simp [shell, nodeEdges]) (by simp [shell, nodeEdges]) (atom, atom) (by simp [row, EdgeValue.children])
  exact ⟨cap, unionCap, rank_zero annotation atom muAnnotated, (rank_pos_iff annotation shell).mpr nonplain,
    zipped, left_union_pair_lt annotation unionEntry [shell, atom] level free unionNonplain shell List.mem_cons_self atom⟩

/-- A legitimate source read preserves the rank of the literal reference request, despite a larger stored Mu. -/
theorem source_reference (annotation : Guard → Prop) (source current : State Symbol Guard)
    (facts : InternedNestedFacts.Facts current) (growth : Grows source current)
    (history : Extends source.nodes.issued current.nodes.issued) (domain : DomainKey)
    (known : Bindings annotation source domain) (name : Nat)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain) (other : Value Symbol Guard) :
    ∃ value, SourcePreparedSharedRows.read current name = some value ∧ Available source value ∧ Available current value ∧
      value.referenceOf = .mu name ∧ rank annotation value = 0 ∧
      pairRank annotation (.reference (.interned name)) other = pairRank annotation value other := by
  obtain ⟨value, found, original, available, named, zero⟩ := binding_read_zero annotation source current facts growth history domain known name member
  exact ⟨value, found, original, available, named, zero,
    hereditary_left_eq annotation _ value other (.reference _) ((rank_zero_iff annotation value).mp zero)⟩

end MicroCFTA.NonplainRankChecks

#print axioms MicroCFTA.NonplainRankChecks.mixed_shell
#check @MicroCFTA.NonplainRankChecks.mixed_shell
#print axioms MicroCFTA.NonplainRankChecks.source_reference
#check @MicroCFTA.NonplainRankChecks.source_reference
