import MicroCFTA.SourceSynthesisUniverseBodyWalkReplay
import MicroCFTA.SourceSynthesisUniverseMappedRowNormalization
import MicroCFTA.SourceSynthesisUniverseSelfRowSet
import MicroCFTA.SourceSynthesisUniverseCanonicalRows

/-!
# Canonical body products with mapped source symbols

The source row fields classify every actual matched pair.
The complete native body walk supplies the product and its row receipts.
Resident key uniqueness identifies its canonical target request.
The source and target lists keep their order and duplicate occurrences.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceSynthesisUniverseMappedBodyCanonical
open Cache Language InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol InternedEdgeResidency
open InternedStoredClosedMuCompletion SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionControl
open SourceSynthesisUniverseBodyReferenceControl (second secondState second_seen)
open SourceSynthesisUniverseRowTransform (Readback)
open EqualityLeafProjectionPhysical (dead)

variable {Symbol Guard : Type}

/-- The source descriptor relation classifies every retained row after canonical ordering. -/
theorem canonical_row_kinds [DecidableEq (EdgeKey Symbol Guard)]
    (arrowSymbol : Symbol) (literal : String → Symbol) (top : Guard) (uId : Nat)
    (marker : Value Symbol Guard) (arrow : EdgeValue Symbol Guard)
    (descriptors : List (String × Nat)) (rows : List (EdgeValue Symbol Guard))
    (arrowChildren : arrow.children = [marker, .reference (.interned uId), .reference (.interned uId)])
    (arrowKey : arrow.entry.key = ⟨arrowSymbol,
      [marker.referenceOf, .ref (.interned uId), .ref (.interned uId)], top⟩)
    (catalogRows : All₂ (fun (descriptor : String × Nat) (row : EdgeValue Symbol Guard) =>
      row.children = List.replicate descriptor.2 (.reference (.interned uId)) ∧
      row.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref (.interned uId)), top⟩)
      descriptors rows) :
    ∀ source ∈ canonicalEdges (arrow :: rows),
      (source.children = [marker, .reference (.interned uId), .reference (.interned uId)] ∧
        source.entry.key = ⟨arrowSymbol,
          [marker.referenceOf, .ref (.interned uId), .ref (.interned uId)], top⟩) ∨
      ∃ descriptor ∈ descriptors,
        source.children = List.replicate descriptor.2 (.reference (.interned uId)) ∧
        source.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref (.interned uId)), top⟩ := by
  have origins : ∀ source ∈ rows, ∃ descriptor ∈ descriptors,
      source.children = List.replicate descriptor.2 (.reference (.interned uId)) ∧
      source.entry.key = ⟨literal descriptor.1, List.replicate descriptor.2 (.ref (.interned uId)), top⟩ := by
    induction catalogRows with
    | nil => intro source member; cases member
    | @cons descriptor row descriptors rows own tail ih =>
        intro source member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨descriptor, List.mem_cons_self, own⟩
        · obtain ⟨descriptor, present, related⟩ := ih source later
          exact ⟨descriptor, List.mem_cons_of_mem _ present, related⟩
  intro source member
  rcases List.mem_cons.mp (canonicalEdges_member (arrow :: rows) source member) with rfl | later
  · exact Or.inl ⟨arrowChildren, arrowKey⟩
  · exact Or.inr (origins source later)

/-- Source row fields derive the complete canonical body product and its cache replay. -/
theorem node_canonical [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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
      All₂ (fun (source : EdgeValue Symbol Guard) target => SourceRecursiveIntersectionKernel.work
        (makeEdge source.entry.key.symbol top (SourceSynthesisUniverseRowTransform.children u.identity source))
        final = .done target final) bodyRows targets ∧
      (∀ row ∈ products, EdgeResident final.heap row) ∧
      (∀ target ∈ targets, target ∈ products) ∧
      (∀ target ∈ targets, EdgeResident final.heap target) ∧
      (∀ target ∈ targets, dead target = false) ∧
      nodeEdges value = canonicalEdges (surviving products) ∧
      makeNode products = makeNode targets ∧
      run (makeNode targets) final.heap = (value, final.heap) := by
  have bodyTop : ∀ source ∈ bodyRows, source.entry.key.constraint = top := by
    intro source member
    rcases kinds source member with arrowKind | ⟨descriptor, catalogRow⟩
    · exact congrArg EdgeKey.constraint arrowKind.2
    · exact congrArg EdgeKey.constraint catalogRow.2
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
    rcases kinds source member with literal | ⟨descriptor, catalogRow⟩
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
    have classified := SourceSynthesisUniverseMappedRowNormalization.row_normalizes arrowSymbol literal u b m bodyRows markerRow
      depth ordinary emptyGuard conjoin top conjoinTop original final facts cacheValid universeAvailable
      markerAvailable leaf markerTop
      kinds
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

end MicroCFTA.SourceSynthesisUniverseMappedBodyCanonical
