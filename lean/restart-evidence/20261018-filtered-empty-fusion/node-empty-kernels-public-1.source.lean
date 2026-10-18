import MicroCFTA.SourceCurrentGeneratedNodeEmpty

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.NodeEmptyKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input)
open InternedStoredSubstitution (Environment Replacements)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentGeneratedNodeEmpty (Fusion)

private def leaf (symbol : Nat) : Syntax Nat Bool := .node [.mk symbol true []]
private def rows : List (EdgeSyntax Nat Bool) := [
  .mk 9 true [leaf 0,.node []], .mk 10 false [leaf 1], .mk 11 true []]
private def source : Syntax Nat Bool := .node rows
private def val (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def built := build source [] empty
private def raw := val built
private def reader := built.state
private def lexical : List (Sum (Value Nat Bool) Unit) := []
private def names : Unit → InternedBinderProtocol.Reference := fun _ => .depth
private def environment : Environment Nat Bool := fun _ => none
private def row := (nodeEdges raw)[0]?.getD (.mk ⟨0,.mk 0 [] false⟩ [])

private theorem actual : build source [] empty = .done raw reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source raw reader actual
private theorem available : Available reader raw :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result raw reader actual
private theorem context : Context reader [] := by
  simpa only [actual,Outcome.state] using SourceCurrentConstrainedCapSourceHistory.empty_context.build source
private theorem repeated : build source [] reader = .done raw reader := by cbv
private theorem reconstructed : execute raw environment reader = .done raw reader := by cbv
private theorem replacements : Replacements reader environment := by
  intro name value found
  cases found
private theorem leaf_fusion (symbol : Nat) : Fusion (leaf symbol) := by
  apply SourceCurrentGeneratedNodeEmpty.node
  intro own guard children member
  obtain equal := List.mem_singleton.mp member
  cases equal
  intro child impossible
  cases impossible
private theorem empty_fusion : Fusion (.node [] : Syntax Nat Bool) :=
  SourceCurrentGeneratedNodeEmpty.node [] (by intro symbol guard children impossible; cases impossible)
private theorem child_fusion : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ rows →
    ∀ child ∈ children, Fusion child := by
  intro symbol guard children member
  rcases List.mem_cons.mp member with equal | member
  · cases equal
    intro child found
    rcases List.mem_cons.mp found with rfl | found
    · exact leaf_fusion 0
    · obtain rfl := List.mem_singleton.mp found
      exact empty_fusion
  · rcases List.mem_cons.mp member with equal | member
    · cases equal
      intro child found
      obtain rfl := List.mem_singleton.mp found
      exact leaf_fusion 1
    · obtain equal := List.mem_singleton.mp member
      cases equal
      intro child impossible
      cases impossible

private theorem checked_witness :
    build source [] empty = .done raw reader ∧ Ready reader ∧
    0 < reader.nodes.next ∧ (nodeEdges raw).length = 2 ∧
    execute raw environment reader = .done raw reader ∧
    (raw.referenceOf == .empty) = (raw.referenceOf == .empty) ∧
    ∃ other ∈ nodeEdges raw,
      row.entry.key.symbol = other.entry.key.symbol ∧ row.entry.key.constraint = other.entry.key.constraint ∧
      All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) row.children other.children := by
  have aliases : SourceCurrentUsedBinderAliasTransport.Aliases source lexical names names := by
    intro a ha b hb
    rfl
  have paired : SourceCurrentRetainedMuDirectedCase.Inputs reader environment environment
      (lexical.map (input names)) (lexical.map (input names)) := .nil _ _
  have fused := SourceCurrentGeneratedNodeEmpty.node rows child_fusion lexical names names environment environment
    reader empty reader reader reader ready SourceCurrentConstrainedCapSourceHistory.empty_context context
    aliases paired replacements replacements raw raw raw raw actual repeated (grows_refl _) (grows_refl _)
    available available reconstructed reconstructed
  have retained := SourceCurrentGeneratedNodeEmpty.row rows child_fusion lexical names names environment environment
    reader empty reader reader reader ready SourceCurrentConstrainedCapSourceHistory.empty_context context
    aliases paired replacements replacements raw raw raw raw actual repeated (grows_refl _) (grows_refl _)
    available available reconstructed reconstructed row (by cbv; exact List.mem_cons_self)
  exact ⟨actual,ready,by cbv,by cbv,reconstructed,fused,retained⟩

/-- A cold node erases its dead row and derives opposite stored-row survival from strict child fusion. -/
theorem cold_node :
    build source [] empty = .done raw reader ∧ Ready reader ∧
    0 < reader.nodes.next ∧ (nodeEdges raw).length = 2 ∧
    execute raw environment reader = .done raw reader ∧
    (raw.referenceOf == .empty) = (raw.referenceOf == .empty) ∧
    ∃ other ∈ nodeEdges raw,
      row.entry.key.symbol = other.entry.key.symbol ∧ row.entry.key.constraint = other.entry.key.constraint ∧
      All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) row.children other.children := checked_witness

end MicroCFTA.NodeEmptyKernels

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

#check @MicroCFTA.NodeEmptyKernels.cold_node
#print MicroCFTA.NodeEmptyKernels.cold_node
#print axioms MicroCFTA.NodeEmptyKernels.cold_node
