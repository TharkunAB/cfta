import MicroCFTA.SourceRecursiveIntersectionInputExact
import MicroCFTA.SourceRecursiveIntersectionNativeActiveBounds

namespace MicroCFTA.SourceRecursiveIntersectionOriginalRowCompletion
open Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionInputView IntersectSchedule
variable {Symbol Guard : Type}

private theorem original_of_readback
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (value : Value Symbol Guard) (input : Input) (available : Available source value)
    (complete : IntersectionFlatMemoKey.input value.referenceOf = some input)
    (original : OriginalInput source input) : Original value := by
  obtain ⟨witness, witnessOriginal, witnessAvailable, witnessCodec⟩ := original
  have witnessRead := payload_readback source facts witness witnessAvailable input witnessCodec
  have actualRead := payload_readback source facts value available input complete
  have same : witness = value := witnessRead.symm.trans actualRead
  exact same ▸ witnessOriginal

/-- Derive semantic completion for rows of the same source's actual closed original parents. -/
theorem edge_complete [DecidableEq Symbol]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (leftParent rightParent : Value Symbol Guard)
    (leftOriginal : OriginalInput source (inputOf leftParent))
    (rightOriginal : OriginalInput source (inputOf rightParent))
    (leftAvailable : Available source leftParent) (rightAvailable : Available source rightParent)
    (leftClosed : leftParent.free = []) (rightClosed : rightParent.free = [])
    (left right : EdgeValue Symbol Guard)
    (leftMember : left ∈ InternedEdgeResidency.nodeEdges leftParent)
    (rightMember : right ∈ InternedEdgeResidency.nodeEdges rightParent) :
    Completes (view source holds)
      (SourceRecursiveIntersectionNative.edgeSemantic holds
        ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) := by
  cases leftParent with
  | empty | reference | union | mu => cases leftMember
  | node first leftEdges leftDepth leftFree =>
      cases rightParent with
      | empty | reference | union | mu => cases rightMember
      | node second rightEdges rightDepth rightFree =>
          change left ∈ leftEdges at leftMember
          change right ∈ rightEdges at rightMember
          have firstOriginal : Original (.node first leftEdges leftDepth leftFree) :=
            original_of_readback source facts _ (.node first.identity) leftAvailable rfl leftOriginal
          have secondOriginal : Original (.node second rightEdges rightDepth rightFree) :=
            original_of_readback source facts _ (.node second.identity) rightAvailable rfl rightOriginal
          have firstClosed : closed (view source holds) (.node first.identity) = true := by
            change closed (view source holds) (inputOf (.node first leftEdges leftDepth leftFree)) = true
            rw [closed_readback source facts holds _ firstOriginal leftAvailable, leftClosed]
            rfl
          have secondClosed : closed (view source holds) (.node second.identity) = true := by
            change closed (view source holds) (inputOf (.node second rightEdges rightDepth rightFree)) = true
            rw [closed_readback source facts holds _ secondOriginal rightAvailable, rightClosed]
            rfl
          let inputs := finiteInput source facts holds (.node first.identity) (.node second.identity)
            leftOriginal rightOriginal firstClosed secondClosed
          let bounds := inputBounds source facts holds (.node first.identity) (.node second.identity)
            leftOriginal rightOriginal firstClosed secondClosed
          let roots : ClosedRoots (view source holds) inputs :=
            ⟨.node first.identity, .node second.identity, .inl .root, .inr .root,
              firstClosed, secondClosed⟩
          have ready : NodeReady roots {} (.node first.identity) (.node second.identity) :=
            roots_ready (view source holds) inputs roots
          have leftRow : row holds left ∈ (view source holds).rows first.identity := by
            rw [rows_readback source facts holds first leftEdges leftDepth leftFree leftAvailable]
            exact List.mem_map.mpr ⟨left, leftMember, rfl⟩
          have rightRow : row holds right ∈ (view source holds).rows second.identity := by
            rw [rows_readback source facts holds second rightEdges rightDepth rightFree rightAvailable]
            exact List.mem_map.mpr ⟨right, rightMember, rfl⟩
          have rowsReady : WorkReady bounds roots (.edge {} (row holds left) (row holds right)) :=
            ready_rows (view source holds) inputs (free_correct source facts holds) bounds roots {}
              first.identity second.identity ready (row holds left) (row holds right) leftRow rightRow
          obtain ⟨fuel, result, done⟩ :=
            call_eventual (view source holds) inputs (free_correct source facts holds) bounds roots
              (.edge {} (row holds left) (row holds right)) rowsReady
          have empty : SourceRecursiveIntersectionSchedule.domain
              IntersectionEmptyDomain.emptyDomain.key = ({} : Domain) := rfl
          refine ⟨fuel, result, ?_⟩
          simpa only [SourceRecursiveIntersectionNative.edgeSemantic, empty] using
            done fuel (Nat.le_refl _)

end MicroCFTA.SourceRecursiveIntersectionOriginalRowCompletion

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceRecursiveIntersectionOriginalRowCompletion.edge_complete
#print MicroCFTA.SourceRecursiveIntersectionOriginalRowCompletion.edge_complete
#print axioms MicroCFTA.SourceRecursiveIntersectionOriginalRowCompletion.edge_complete
