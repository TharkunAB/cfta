import MicroCFTA.SourceCurrentBoundedFilteredNodeFusion
import MicroCFTA.InternedFreshOrdinarySourceFreeNames

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.BoundedNodeKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input)
open InternedStoredSubstitution (Environment Replacements)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentBoundedFilteredFusion (Fusion)

private def leaf (symbol : Nat) : Syntax Nat Bool := .node [.mk symbol true []]
private def nested : Syntax Nat Bool := .binder true (.node [.mk 7 true [],.mk 9 false [.var 0]])
private def nestedUsed : Bool :=
  match build nested [] (empty (Symbol := Nat) (Guard := Bool)) with
  | .done (.mu _ _ depth ordinary) _ => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary
  | _ => false
private def rows : List (EdgeSyntax Nat Bool) := [
  .mk 9 true [leaf 0,.node []], .mk 10 false [nested], .mk 11 true []]
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
private theorem leaf_fusion (symbol : Nat) : Fusion 1 (leaf symbol) := by
  apply SourceCurrentBoundedFilteredNodeFusion.node 1
  intro own guard children member
  obtain equal := List.mem_singleton.mp member
  cases equal
  intro child impossible
  cases impossible
private theorem empty_fusion : Fusion 1 (.node [] : Syntax Nat Bool) :=
  SourceCurrentBoundedFilteredNodeFusion.node 1 [] (by intro symbol guard children impossible; cases impossible)
private theorem filter_closed (reader : State Nat Bool) (ready : Ready reader)
    (raw : Value Nat Bool) (available : Available reader raw) (closed : raw.free = [])
    (own : InternedBinderProtocol.Reference) : run (withoutSelfReference own raw) reader = (raw,reader) := by
  cases raw with
  | empty | reference | node | mu => rfl
  | union entry members level free =>
      rw [withoutSelfReference_absent]
      intro member
      have present := (InternedNormalizationFree.unionMembers_free reader ready.semantic.1.normal.facts.coherent
        (.union entry members level free) available own).mpr
          ⟨.reference own,member,List.mem_singleton_self _⟩
      rw [closed] at present
      cases present

private theorem nested_fusion : Fusion 1 nested := by
  intro Atom reader ready inputs firstNames secondNames firstOwn secondOwn first second before later after final
    rawFirst rawSecond filteredFirst filteredSecond left right _firstDepth _secondDepth firstContext secondContext
    _aliases _tests _paired firstReplacements secondReplacements firstAvailable secondAvailable firstBuild secondBuild
    _firstGrowth _secondGrowth firstFilter secondFilter firstDone secondDone
  have independent (environment : List (Value Nat Bool)) (state : State Nat Bool) :
      build nested environment state = build nested [] state := by
    apply InternedFreshOrdinaryDependencies.build_congr
    intro index member
    have noInputs : InternedNestedDependencies.inputs nested = [] := by cbv
    rw [noInputs] at member
    cases member
  have closed (environment : List (Value Nat Bool)) (before after : State Nat Bool)
      (context : Context before environment) (raw : Value Nat Bool)
      (actual : build nested environment before = .done raw after) : raw.free = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name member
    have called : build nested [] before = .done raw after := (independent environment before).symm.trans actual
    obtain ⟨value,impossible,_⟩ := InternedFreshOrdinarySourceFreeNames.build_free_origins nested [] before
      context.base.normal (by intro value impossible; cases impossible) context.base.freeNames
      context.base.profiles raw after called name member
    cases impossible
  have firstClosed := closed _ before after firstContext rawFirst firstBuild
  have secondClosed := closed _ later final secondContext rawSecond secondBuild
  have firstSame : rawFirst = filteredFirst := congrArg Prod.fst
    ((filter_closed reader ready rawFirst firstAvailable firstClosed firstOwn).symm.trans firstFilter)
  have secondSame : rawSecond = filteredSecond := congrArg Prod.fst
    ((filter_closed reader ready rawSecond secondAvailable secondClosed secondOwn).symm.trans secondFilter)
  exact SourceCurrentFilteredSourceFusion.nonempty_maps nested inputs firstNames secondNames firstOwn secondOwn first second
    before later after final reader rawFirst rawSecond filteredFirst filteredSecond left right firstContext secondContext
    firstBuild secondBuild ready firstAvailable secondAvailable firstReplacements secondReplacements firstFilter secondFilter
    firstDone secondDone (by intro name member; rw [←firstSame,firstClosed] at member; cases member)
    (by intro name member; rw [←secondSame,secondClosed] at member; cases member)

private theorem child_fusion : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ rows →
    ∀ child ∈ children, Fusion 1 child := by
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
      exact nested_fusion
    · obtain equal := List.mem_singleton.mp member
      cases equal
      intro child impossible
      cases impossible

private theorem checked_witness :
    build source [] empty = .done raw reader ∧ Ready reader ∧
    raw.depth = 1 ∧ nestedUsed = true ∧
    0 < reader.nodes.next ∧ (nodeEdges raw).length = 2 ∧
    execute raw environment reader = .done raw reader ∧
    (raw.referenceOf == .empty) = (raw.referenceOf == .empty) ∧
    ∃ other ∈ nodeEdges raw,
      row.entry.key.symbol = other.entry.key.symbol ∧ row.entry.key.constraint = other.entry.key.constraint ∧
      All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) row.children other.children := by
  have aliases : SourceCurrentUsedBinderAliasTransport.Aliases source lexical names names := by
    intro a ha b hb
    rfl
  have paired : SourceCurrentReaderReplacementSlots.Paired
      (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) environment environment
      (lexical.map (input names)) (lexical.map (input names)) := .nil
  have tests : ∀ label ∈ SourceCurrentUsedBinderAliasTransport.Scope source lexical,
      Sum.elim id names label = .depth ↔ Sum.elim id names label = .depth := by
    intro label member
    rfl
  have filter : run (withoutSelfReference .depth raw) reader = (raw,reader) := by cbv
  have fused := SourceCurrentBoundedFilteredNodeFusion.node 1 rows child_fusion reader ready lexical names names
    .depth .depth environment environment empty reader reader reader raw raw raw raw raw raw
    (by cbv) (by cbv) SourceCurrentConstrainedCapSourceHistory.empty_context context aliases tests paired
    replacements replacements available available actual repeated (grows_refl _) (grows_refl _)
    filter filter reconstructed reconstructed
  have retained := SourceCurrentBoundedFilteredNodeFusion.row 1 rows child_fusion lexical names names environment environment
    reader empty reader reader reader ready SourceCurrentConstrainedCapSourceHistory.empty_context context
    aliases paired replacements replacements raw raw raw raw (by cbv) (by cbv) actual repeated (grows_refl _) (grows_refl _)
    available available reconstructed reconstructed row (by cbv; exact List.mem_cons_self)
  exact ⟨actual,ready,by cbv,by cbv,by cbv,by cbv,reconstructed,fused,retained⟩

/-- A cold positive-depth node with a nested used Mu derives opposite row survival from bounded child fusion. -/
theorem positive_node :
    build source [] empty = .done raw reader ∧ Ready reader ∧
    raw.depth = 1 ∧ nestedUsed = true ∧
    0 < reader.nodes.next ∧ (nodeEdges raw).length = 2 ∧
    execute raw environment reader = .done raw reader ∧
    (raw.referenceOf == .empty) = (raw.referenceOf == .empty) ∧
    ∃ other ∈ nodeEdges raw,
      row.entry.key.symbol = other.entry.key.symbol ∧ row.entry.key.constraint = other.entry.key.constraint ∧
      All₂ (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) row.children other.children := checked_witness

end MicroCFTA.BoundedNodeKernels
