import MicroCFTA.SourceSynthesisUniverseBodyCanonical
import MicroCFTA.InternedOrdinaryUnionReadback

/-!
# Exact free name of the actual universe-body product

The retained arrow self row contains the diagonal cutoff. Canonical node
construction retains that live row. Every other child is the same cutoff
or the original closed marker. The result is therefore an ordinary node
with depth zero and exactly the pending diagonal name.
-/
namespace MicroCFTA.SourceSynthesisUniverseBodyExactFree
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol InternedEdgeResidency InternedStoredClosedMuCompletion
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBody (Shape RowReadback)
open SourceSynthesisUniverseBodyReferenceControl (second secondState)
open SourceSynthesisUniverseRowTransform (Readback)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

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

/-- The actual body product retains its marker and has exactly the pending diagonal name. -/
theorem node_exact_free (top : Guard) (catalog : List (String × Nat))
    (u b : Interned NodeKey) (bodyRows : List (EdgeValue String Guard))
    (depth ordinary : Value String Guard) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (original : Machine String Guard) (facts : Facts original.heap)
    (cacheValid : Cache.Valid original.domains)
    (universeAvailable : Available original.heap
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (shape : Shape top catalog (.interned u.identity) (.node b bodyRows 0 [.interned u.identity])) :
    ∃ value final entry rows m markerRow,
      node emptyGuard conjoin
        (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1)
        bodyRows bodyRows (secondState u b bodyRows depth ordinary original) = .done value final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧
      Extension (secondState u b bodyRows depth ordinary original) final ∧
      Available final.heap value ∧ PreparedWithoutMu value ∧
      value = .node entry rows 0 [.intersection (pair u.identity u.identity).1
        (pair u.identity u.identity).2] ∧
      RowReadback "(->)" top [] (.node m [markerRow] 0 []) ∧
      Available final.heap (.node m [markerRow] 0 []) ∧
      (∀ row ∈ rows, row.entry.key.constraint = top) ∧
      (∀ row ∈ rows, ∀ child ∈ row.children,
        child = .node m [markerRow] 0 [] ∨ child = repeatedValue (pair u.identity u.identity)) := by
  obtain ⟨value, final, _products, targets, done, finalValid, growth, available, prepared, _free,
      aligned, _hits, _productResident, _retained, targetResident, targetLive, _exactRows, _same, pureNode⟩ :=
    SourceSynthesisUniverseBodyCanonical.node_canonical top catalog u b bodyRows depth ordinary emptyGuard
      conjoin conjoinTop original facts cacheValid universeAvailable shape
  obtain ⟨m, markerRow, arrow, markerRead, _leaf, _markerTop, markerAvailable,
      arrowMember, arrowChildren, _arrowKey, _kinds, _bodyTop, bodyChildren⟩ :=
    SourceSynthesisUniverseBodyEvidence.of_shape top catalog u b bodyRows depth ordinary
      original.heap universeAvailable shape
  let marker : Value String Guard := .node m [markerRow] 0 []
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
  have originalRow : ∀ row ∈ canonicalEdges (surviving targets), row ∈ targets := by
    intro row member
    exact (List.mem_filter.mp (canonicalEdges_member _ row member)).1
  refine ⟨value, final, entry, canonicalEdges (surviving targets), m, markerRow,
    done, finalValid, growth, available, prepared, valueRead, markerRead,
    growth.available _ markerAvailable, ?_, ?_⟩
  · intro row member
    exact targetTop row (originalRow row member)
  · intro row member child present
    exact targetChildren row (originalRow row member) child present

end MicroCFTA.SourceSynthesisUniverseBodyExactFree
