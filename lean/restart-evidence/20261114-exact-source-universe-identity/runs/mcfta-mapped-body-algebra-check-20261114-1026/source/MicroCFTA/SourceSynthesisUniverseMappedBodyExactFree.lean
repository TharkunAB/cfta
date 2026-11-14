import MicroCFTA.SourceSynthesisUniverseMappedBodyCanonical
import MicroCFTA.InternedOrdinaryUnionReadback

/-!
# Exact free name of a mapped-symbol body product

The actual retained arrow supplies the pending diagonal name.
The ordered targets retain the same closed source marker.
Canonical construction therefore has depth zero and exactly that free name.
The proof derives the native product and both complete row readbacks.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceSynthesisUniverseMappedBodyExactFree
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol InternedEdgeResidency InternedStoredClosedMuCompletion
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl (second secondState)
open SourceSynthesisUniverseRowTransform (Readback)

variable {Symbol Guard : Type}

private theorem aligned_members {A B : Type} {relation : A → B → Prop}
    {inputs : List A} {outputs : List B} (aligned : All₂ relation inputs outputs) :
    (∀ input ∈ inputs, ∃ output ∈ outputs, relation input output) ∧
    (∀ output ∈ outputs, ∃ input ∈ inputs, relation input output) := by
  induction aligned with
  | nil => constructor <;> intro selected member <;> cases member
  | @cons input output inputs outputs own tail ih =>
      constructor
      · intro selected member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨output, List.mem_cons_self, own⟩
        · obtain ⟨target, present, related⟩ := ih.1 selected later
          exact ⟨target, List.mem_cons_of_mem _ present, related⟩
      · intro selected member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨input, List.mem_cons_self, own⟩
        · obtain ⟨source, present, related⟩ := ih.2 selected later
          exact ⟨source, List.mem_cons_of_mem _ present, related⟩

/-- Source fields derive the exact canonical node and its sole pending diagonal name. -/
theorem node_target_readback [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (arrowSymbol : Symbol) (literal : String → Symbol) (top : Guard)
    (u b m : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (markerRow : EdgeValue Symbol Guard) (depth ordinary : Value Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (original : Machine Symbol Guard) (facts : Facts original.heap)
    (cacheValid : Cache.Valid original.domains)
    (universeAvailable : Available original.heap
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (markerAvailable : Available original.heap (.node m [markerRow] 0 []))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (kinds : ∀ source ∈ bodyRows,
      (source.children = [.node m [markerRow] 0 [], .reference (.interned u.identity), .reference (.interned u.identity)] ∧
        source.entry.key = ⟨arrowSymbol, [(Value.node m [markerRow] 0 []).referenceOf,
          .ref (.interned u.identity), .ref (.interned u.identity)], top⟩) ∨
      ∃ descriptor : String × Nat,
        source.children = List.replicate descriptor.2 (.reference (.interned u.identity)) ∧
        source.entry.key = ⟨literal descriptor.1,
          List.replicate descriptor.2 (.ref (.interned u.identity)), top⟩)
    (arrow : EdgeValue Symbol Guard) (arrowMember : arrow ∈ bodyRows)
    (arrowChildren : arrow.children = [.node m [markerRow] 0 [],
      .reference (.interned u.identity), .reference (.interned u.identity)])
    (arrowKey : arrow.entry.key = ⟨arrowSymbol, [(Value.node m [markerRow] 0 []).referenceOf,
      .ref (.interned u.identity), .ref (.interned u.identity)], top⟩) :
    ∃ value final entry targets,
      node emptyGuard conjoin
        (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1)
        bodyRows bodyRows (secondState u b bodyRows depth ordinary original) = .done value final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧
      Extension (secondState u b bodyRows depth ordinary original) final ∧
      Available final.heap value ∧ PreparedWithoutMu value ∧
      value = .node entry (canonicalEdges targets) 0 [.intersection (pair u.identity u.identity).1
        (pair u.identity u.identity).2] ∧
      All₂ (Readback top u.identity) bodyRows targets ∧
      (∀ target ∈ targets, EdgeResident final.heap target) ∧
      (∀ target ∈ targets, EqualityLeafProjectionPhysical.dead target = false) ∧
      (∀ target ∈ targets, target.entry.key.constraint = top) ∧
      (∀ target ∈ targets, ∀ child ∈ target.children,
        child = .node m [markerRow] 0 [] ∨ child = repeatedValue (pair u.identity u.identity)) ∧
      Available final.heap (.node m [markerRow] 0 []) ∧
      run (makeNode targets) final.heap = (value, final.heap) := by
  obtain ⟨value, final, _products, targets, done, finalValid, growth, available, prepared, _free,
      aligned, _hits, _productResident, _retained, targetResident, targetLive, _exactRows, _same, pureNode⟩ :=
    SourceSynthesisUniverseMappedBodyCanonical.node_canonical arrowSymbol literal top u b m bodyRows
      markerRow depth ordinary emptyGuard conjoin conjoinTop original facts cacheValid universeAvailable
      markerAvailable leaf markerTop kinds arrow arrowMember arrowChildren arrowKey
  have bodyChildren : ∀ source ∈ bodyRows, ∀ child ∈ source.children,
      child = .node m [markerRow] 0 [] ∨ child = .reference (.interned u.identity) := by
    intro source member child included
    rcases kinds source member with arrowKind | ⟨descriptor, catalogRow⟩
    · rw [arrowKind.1] at included
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
    · rw [catalogRow.1] at included
      exact Or.inr (List.eq_of_mem_replicate included)
  let marker : Value Symbol Guard := .node m [markerRow] 0 []
  have members := aligned_members aligned
  have targetTop : ∀ target ∈ targets, target.entry.key.constraint = top := by
    intro target member
    obtain ⟨source, _included, readback⟩ := members.2 target member
    rw [readback.2]
  have targetChildren : ∀ target ∈ targets, ∀ child ∈ target.children,
      child = marker ∨ child = repeatedValue (pair u.identity u.identity) := by
    intro target member child present
    obtain ⟨source, included, readback⟩ := members.2 target member
    rw [readback.1, SourceSynthesisUniverseRowTransform.children] at present
    obtain ⟨originalChild, originalMember, rfl⟩ := List.mem_map.mp present
    rcases bodyChildren source included originalChild originalMember with same | same
    · left
      rw [same]
      exact InternedStoredSubstitutionScope.input_closed marker _ rfl
    · right
      rw [same]
      simp [InternedStoredSubstitution.input, InternedStoredSubstitutionRebind.replacement]
  obtain ⟨arrowTarget, arrowTargetMember, arrowRead⟩ := members.1 arrow arrowMember
  have arrowTargetChildren : arrowTarget.children =
      [marker, repeatedValue (pair u.identity u.identity), repeatedValue (pair u.identity u.identity)] :=
    arrowRead.1.trans
      (SourceSynthesisUniverseRowTransform.arrow_children u.identity m [markerRow] 0 arrow arrowChildren)
  have zero : ∀ child ∈ targets.flatMap EdgeValue.children, child.depth = 0 := by
    intro child present
    obtain ⟨target, member, childMember⟩ := List.mem_flatMap.mp present
    rcases targetChildren target member child childMember with same | same
    · rw [same]
      rfl
    · rw [same]
      rfl
  have only : ∀ child ∈ targets.flatMap EdgeValue.children, ∀ name ∈ child.free,
      name = .intersection (pair u.identity u.identity).1 (pair u.identity u.identity).2 := by
    intro child present name named
    obtain ⟨target, member, childMember⟩ := List.mem_flatMap.mp present
    rcases targetChildren target member child childMember with same | same
    · rw [same] at named
      cases named
    · simpa only [same, repeatedValue, Value.free, List.mem_singleton] using named
  have witness : ∃ target ∈ targets, EqualityLeafProjectionPhysical.dead target = false ∧
      ∃ child ∈ target.children,
        .intersection (pair u.identity u.identity).1 (pair u.identity u.identity).2 ∈ child.free := by
    refine ⟨arrowTarget, arrowTargetMember, targetLive arrowTarget arrowTargetMember,
      repeatedValue (pair u.identity u.identity), ?_, ?_⟩
    · rw [arrowTargetChildren]
      simp
    · simp [repeatedValue, Value.free]
  obtain ⟨entry, nodeRead⟩ := InternedOrdinaryUnionReadback.makeNode_zero_singleton
    targets final.heap finalValid.1.coherent finalValid.1.linked targetResident
    (.intersection (pair u.identity u.identity).1 (pair u.identity u.identity).2) zero only witness
  have valueRead : value = .node entry (canonicalEdges (surviving targets)) 0
      [.intersection (pair u.identity u.identity).1 (pair u.identity u.identity).2] := by
    simpa only [pureNode] using nodeRead
  have survivingTargets : surviving targets = targets := by
    unfold surviving
    apply List.filter_eq_self.mpr
    intro row member
    change (!EqualityLeafProjectionPhysical.dead row) = true
    simp only [targetLive row member, Bool.not_false]
  rw [survivingTargets] at valueRead
  exact ⟨value, final, entry, targets, done, finalValid, growth, available, prepared,
    valueRead, aligned, targetResident, targetLive, targetTop, targetChildren,
    growth.available _ markerAvailable, pureNode⟩

end MicroCFTA.SourceSynthesisUniverseMappedBodyExactFree

#print axioms MicroCFTA.SourceSynthesisUniverseMappedBodyExactFree.node_target_readback
