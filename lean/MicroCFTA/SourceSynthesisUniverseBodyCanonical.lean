import MicroCFTA.SourceSynthesisUniverseBodyEvidence
import MicroCFTA.SourceSynthesisUniverseBodyWalkReplay
import MicroCFTA.SourceSynthesisUniverseRowNormalization
import MicroCFTA.SourceSynthesisUniverseSelfRowSet
import MicroCFTA.SourceSynthesisUniverseCanonicalRows

/-!
# Canonical source-substitution rows of the actual universe product

Every target comes from an actual self pair in the complete ordered product.
Every other live output has one of those targets. Resident key uniqueness
therefore gives the same complete node request. Each target edge and the
final node replay in the actual final cache without further allocation.
-/
namespace MicroCFTA.SourceSynthesisUniverseBodyCanonical
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol InternedEdgeResidency
open InternedStoredClosedMuCompletion SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionControl
open SourceSynthesisUniverseBody (Shape RowKeys)
open SourceSynthesisUniverseBodyReferenceControl (second secondState second_seen)
open SourceSynthesisUniverseRowTransform (Readback)
open EqualityLeafProjectionPhysical (dead)

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- Actual body construction and the whole product derive its exact canonical transformed row set. -/
theorem node_canonical (top : Guard) (catalog : List (String × Nat))
    (u b : Interned NodeKey) (bodyRows : List (EdgeValue String Guard))
    (depth ordinary : Value String Guard) (emptyGuard : Guard)
    (conjoin : Guard → Guard → Guard) (conjoinTop : conjoin top top = top)
    (original : Machine String Guard) (facts : Facts original.heap)
    (cacheValid : Cache.Valid original.domains)
    (universeAvailable : Available original.heap
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (shape : Shape top catalog (.interned u.identity) (.node b bodyRows 0 [.interned u.identity])) :
    ∃ value final products targets,
      node emptyGuard conjoin
        (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1)
        bodyRows bodyRows (secondState u b bodyRows depth ordinary original) = .done value final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧
      Extension (secondState u b bodyRows depth ordinary original) final ∧
      Available final.heap value ∧ PreparedWithoutMu value ∧
      (value.free = [] ∨ value.free = [.intersection (pair u.identity u.identity).1
        (pair u.identity u.identity).2]) ∧
      All₂ (Readback top u.identity) bodyRows targets ∧
      All₂ (fun (source : EdgeValue String Guard) target => SourceRecursiveIntersectionKernel.work
        (makeEdge source.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children u.identity source))
        final = .done target final) bodyRows targets ∧
      (∀ row ∈ products, EdgeResident final.heap row) ∧
      (∀ target ∈ targets, target ∈ products) ∧
      (∀ target ∈ targets, EdgeResident final.heap target) ∧
      (∀ target ∈ targets, dead target = false) ∧
      nodeEdges value = canonicalEdges (surviving products) ∧
      makeNode products = makeNode targets ∧
      run (makeNode targets) final.heap = (value, final.heap) := by
  obtain ⟨m, markerRow, arrow, markerRead, leaf, markerTop, markerAvailable,
      arrowMember, arrowChildren, arrowKey, kinds, bodyTop, bodyChildren⟩ :=
    SourceSynthesisUniverseBodyEvidence.of_shape top catalog u b bodyRows depth ordinary
      original.heap universeAvailable shape
  obtain ⟨value, final, products, done, finalValid, growth, available, prepared, free,
      productResident, replayed, exactRows, nodeReplay, members⟩ :=
    SourceSynthesisUniverseBodyWalkReplay.node_complete u b m bodyRows markerRow depth ordinary
      emptyGuard conjoin top conjoinTop original facts cacheValid universeAvailable markerAvailable
      leaf markerTop bodyTop bodyChildren
  let domain := (second u b bodyRows depth ordinary original).1
  have seen : pair u.identity u.identity ∈ domain.key.seen :=
    (second_seen u b bodyRows depth ordinary original cacheValid _).mpr (Or.inr rfl)
  have markerFinal : Available final.heap (.node m [markerRow] 0 []) := growth.available _ markerAvailable
  have shapes : ∀ source ∈ bodyRows,
      source.children = [.node m [markerRow] 0 [], .reference (.interned u.identity),
        .reference (.interned u.identity)] ∨
      ∃ arity, source.children = List.replicate arity (.reference (.interned u.identity)) := by
    intro source member
    rcases kinds source member with literal | ⟨descriptor, _, catalogRow⟩
    · exact Or.inl literal.1
    · exact Or.inr ⟨descriptor.2, catalogRow.1⟩
  obtain ⟨targets, aligned, hits, retained, targetResident, targetLive, _⟩ :=
    SourceSynthesisUniverseSelfRowSet.from_replay emptyGuard top conjoin conjoinTop domain u.identity
      m [markerRow] 0 bodyRows products final finalValid markerFinal seen bodyTop shapes productResident replayed
  have origins : ∀ row ∈ products, dead row = false →
      ∃ source ∈ bodyRows, Readback top u.identity source row := by
    intro row present live
    obtain ⟨matched, matchedMember, returned⟩ := (members row).mp present
    have selected := (pairs_member bodyRows bodyRows matched).mp matchedMember
    have classified := SourceSynthesisUniverseRowNormalization.row_normalizes u b m bodyRows markerRow
      depth ordinary emptyGuard conjoin top conjoinTop original final facts cacheValid universeAvailable
      markerAvailable leaf markerTop
      (fun source member => (kinds source member).elim Or.inl
        (fun ⟨descriptor, _, related⟩ => Or.inr ⟨descriptor, related⟩))
      arrow arrowMember arrowChildren arrowKey finalValid growth matched.1 matched.2
      selected.1 selected.2.1 selected.2.2 row final returned
    rcases classified with impossible | source
    · simp only [live, Bool.false_eq_true] at impossible
    · exact source
  have same := SourceSynthesisUniverseCanonicalRows.makeNode_eq top u.identity bodyRows products targets
    final.heap finalValid.1 productResident targetResident aligned targetLive origins retained
  have targetReplay : run (makeNode targets) final.heap = (value, final.heap) := by
    rw [← same]
    exact nodeReplay
  exact ⟨value, final, products, targets, done, finalValid, growth, available, prepared, free,
    aligned, hits, productResident, retained, targetResident, targetLive, exactRows, same, targetReplay⟩

end MicroCFTA.SourceSynthesisUniverseBodyCanonical
