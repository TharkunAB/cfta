import MicroCFTA.SourceCurrentOuterPlainRowShapes
import MicroCFTA.SourceCurrentOuterUntouchedProgress
import MicroCFTA.InternedValueMass

/-!
# Plain row dispatch excludes an active ordinary owner

Actual returned cells retain the child shape of their captured plain row.
An original child has smaller structural mass than its ordinary owner.
Erasure and rejection return Empty. The actual indexed dispatch therefore
has a different value reference and a different complete cache key.
Earlier siblings can return. The enclosing owner need not return.
This result does not cover rows with nonempty effective own equalities.
-/
namespace MicroCFTA.SourceCurrentOuterPlainOwnerProgress
open Cache InternedConstructorTemplates InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached Step)
open SourceCurrentOuterPrefixInvariants (Good NodeReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
local notation "prefixState" => SourceCurrentAllocatedPartialGraph.prefixState
local notation "Origins" => SourceCurrentOuterPlainRowShapes.Origins

private theorem shape_child_ne {entry rows depth free original returned value}
    (member : (original : Edge) ∈ rows)
    (shape : SourceCurrentAllocatedPartialReturnedDomain.Shape original returned)
    (selected : value ∈ returned.children) : value ≠ (Value.node entry rows depth free : Node) := by
  rcases shape with unchanged | erased | sentinel
  · rw [unchanged] at selected
    have smaller := InternedValueMass.node_child_lt entry rows depth free original member value selected
    intro same
    rw [same] at smaller
    omega
  · rw [erased] at selected
    obtain ⟨_,_,same⟩ := List.mem_map.mp selected
    cases same
    intro impossible
    cases impossible
  · rw [sentinel] at selected
    cases List.mem_singleton.mp selected
    intro impossible
    cases impossible

section Workers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {width : Nat}

/-- A literal plain row dispatch has a different reference and key from its active ordinary owner. -/
theorem dispatch {g s r e p h m c n budget ownerFuel fuel slot handle : Nat}
    {owner : NodeRequest} {entry rows depth free} {running before afterParent start : Caller width}
    {original parented : Edge} {rest : List Edge} {combined : EqValue}
    {earlier : List Node} {value : Node}
    (ordinary : owner.value = .node entry rows depth free)
    (good : Good running) (ready : NodeReady running owner)
    (active : running.nodeResults.cells handle = some ⟨owner,.evaluating⟩)
    (origins : Origins running)
    (past : Reached g s r e p h m c n budget (.body ownerFuel owner running)
      (.rows (fuel + slot + 2) owner.inherited (original :: rest) before))
    (member : original ∈ rows)
    (plain : SourceCompactGuards.sourceEqualities original.entry.key.constraint = some [])
    (parent : edgeCall (fuel + slot + 1) g s r e p h m c n budget
      ⟨owner.inherited,original⟩ before = .done parented afterParent)
    (combinedAt : (SourceCurrentAllocatedInheritedPrefix.run parented.entry.key.constraint owner.inherited
      afterParent.checked.operations).1 = .ok (some combined))
    (live : combined ≠ .contradiction)
    (earlierCalls : walk (fuel + slot + 1) g s r e p h m c n budget combined 0
      (parented.children.take slot) (prefixState afterParent parented owner.inherited) = .done earlier start)
    (selected : parented.children[slot]? = some value) :
    Reached g s r e p h m c n budget (.body ownerFuel owner running)
      (.node fuel ⟨(descend start combined slot).1,value⟩ (descend start combined slot).2) ∧
    value.referenceOf ≠ owner.value.referenceOf ∧
      (NodeRequest.mk (descend start combined slot).1 value).key ≠ owner.key := by
  have current := SourceCurrentOuterPrefixInvariants.reached past good ready
  have retained := SourceCurrentOuterPlainRowShapes.reached past good ready origins
  have shape := (SourceCurrentOuterPlainRowShapes.edge_call parent current.1
    ⟨current.2.1,current.2.2 _ List.mem_cons_self⟩ retained).2 plain
  have different : value ≠ owner.value := by
    rw [ordinary]
    exact shape_child_ne member shape (List.mem_of_getElem? selected)
  have rowStep : Reached g s r e p h m c n budget
      (.rows (fuel + slot + 2) owner.inherited (original :: rest) before)
      (.descendants (fuel + slot + 1) owner.inherited parented afterParent) :=
    .snoc (.refl _) (.rows_edge parent)
  have walkStep := ((past.trans rowStep).snoc (Step.descendants_children combinedAt)).snoc
    (Step.children_walk live)
  have entered := SourceCurrentOuterUntouchedProgress.walk_prefix earlierCalls selected
  have reached : Reached g s r e p h m c n budget (.body ownerFuel owner running)
      (.node fuel ⟨(descend start combined slot).1,value⟩ (descend start combined slot).2) :=
    walkStep.trans (by simpa only [Nat.zero_add] using entered)
  have final := SourceCurrentOuterPrefixInvariants.reached reached good ready
  have valid : SourceCurrentOuterExecutionAncestry.NodeValid running :=
    FlatMemoThunk.Valid.map _ _ _ _ good.nodes (fun _ _ => trivial)
  have ownerCell := reached.running valid handle owner active
  have ownerReady := (final.1.nodes.checked _ _ ownerCell).1
  have references : value.referenceOf ≠ owner.value.referenceOf := by
    intro same
    exact different (InternedFreshProbeKeys.resident_reference_injective _
      final.1.checked.heap.semantic.1.normal.facts.coherent value owner.value
      final.2.2.resident ownerReady.2.resident same)
  exact ⟨reached,references,fun same => references (congrArg Prod.snd same)⟩

end Workers
end MicroCFTA.SourceCurrentOuterPlainOwnerProgress
