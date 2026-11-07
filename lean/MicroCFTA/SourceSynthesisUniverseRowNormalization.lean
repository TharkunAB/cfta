import MicroCFTA.SourceSynthesisUniverseRowTransform
import MicroCFTA.SourceSynthesisUniverseCrossRowIdentity
import MicroCFTA.SourceSynthesisUniverseDomainReplay

/-!
# Source-substitution origins of actual matched universe rows

Each completed matched row is dead or reads back a transformed original row.
Catalog descriptors need not be unique. The retained distinguished arrow
supplies the origin of live cross rows. Later machines replay the original
second domain. The final body walk derives the internal row execution premise.
-/
namespace MicroCFTA.SourceSynthesisUniverseRowNormalization
open Cache InternedConstructorTemplates InternedBinderProtocol
open InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl (second secondState second_seen)
open SourceSynthesisUniverseBody (RowKeys)
open SourceSynthesisUniverseRowTransform (Readback)
open EqualityLeafProjectionPhysical (dead)

private theorem mismatch_dead {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (left right : EdgeValue Symbol Guard) (before : Machine Symbol Guard)
    (row : EdgeValue Symbol Guard) (after : Machine Symbol Guard) (facts : Facts before.heap)
    (different : left.children.length ≠ right.children.length)
    (returned : edge emptyGuard conjoin call left right before = .done row after) : dead row = true := by
  have actual : work (makeEdge left.entry.key.symbol emptyGuard [.empty]) before = .done row after := by
    simpa only [edge, different, ite_false] using returned
  change (Result.done (InternedConstructorTemplates.run
    (makeEdge left.entry.key.symbol emptyGuard [.empty]) before.heap).1
    {before with heap := (InternedConstructorTemplates.run
      (makeEdge left.entry.key.symbol emptyGuard [.empty]) before.heap).2}) = .done row after at actual
  have same := (Result.done.inj actual).1
  have children := InternedShallowValues.makeEdge_children left.entry.key.symbol emptyGuard [.empty]
    before.heap facts.coherent facts.cached (by
      intro value member
      have empty := List.mem_singleton.mp member
      subst value
      exact empty_available before.heap)
  unfold dead
  rw [← same, children]
  rfl

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- Every actual matched output is dead or has a source-substitution origin among retained input rows. -/
theorem row_normalizes
    (u b m : Interned NodeKey) (bodyRows : List (EdgeValue String Guard))
    (markerRow : EdgeValue String Guard) (depth ordinary : Value String Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (top : Guard)
    (conjoinTop : conjoin top top = top) (original before : Machine String Guard)
    (_facts : Facts original.heap) (cacheValid : Cache.Valid original.domains)
    (universeAvailable : Available original.heap
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (markerAvailable : Available original.heap (.node m [markerRow] 0 []))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (kinds : ∀ source ∈ bodyRows,
      (source.children = [.node m [markerRow] 0 [], .reference (.interned u.identity), .reference (.interned u.identity)] ∧
        source.entry.key = ⟨"->", [(Value.node m [markerRow] 0 []).referenceOf,
          .ref (.interned u.identity), .ref (.interned u.identity)], top⟩) ∨
      ∃ descriptor : String × Nat, RowKeys top (.interned u.identity) descriptor source)
    (arrow : EdgeValue String Guard) (arrowMember : arrow ∈ bodyRows)
    (arrowChildren : arrow.children = [.node m [markerRow] 0 [],
      .reference (.interned u.identity), .reference (.interned u.identity)])
    (arrowKey : arrow.entry.key = ⟨"->", [(Value.node m [markerRow] 0 []).referenceOf,
      .ref (.interned u.identity), .ref (.interned u.identity)], top⟩)
    (beforeValid : SourceRecursiveIntersectionKernel.Valid before)
    (growth : Extension (secondState u b bodyRows depth ordinary original) before)
    (left right : EdgeValue String Guard) (leftMember : left ∈ bodyRows) (rightMember : right ∈ bodyRows)
    (sameSymbol : left.entry.key.symbol = right.entry.key.symbol)
    (row : EdgeValue String Guard) (after : Machine String Guard)
    (returned : edge emptyGuard conjoin
      (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1) left right before = .done row after) :
    dead row = true ∨ ∃ source ∈ bodyRows, Readback top u.identity source row := by
  let domain := (second u b bodyRows depth ordinary original).1
  have bodyTop : ∀ source ∈ bodyRows, source.entry.key.constraint = top := by
    intro source member
    rcases kinds source member with literal | ⟨descriptor, catalog⟩
    · exact congrArg EdgeKey.constraint literal.2
    · exact congrArg EdgeKey.constraint catalog.2
  have leftTop := bodyTop left leftMember
  have rightTop := bodyTop right rightMember
  have markerBefore : Available before.heap (.node m [markerRow] 0 []) := growth.available _ markerAvailable
  have universeBefore : Available before.heap
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary) := growth.available _ universeAvailable
  have seen : pair u.identity u.identity ∈ domain.key.seen :=
    (second_seen u b bodyRows depth ordinary original cacheValid _).mpr (Or.inr rfl)
  have sameDomain : (second u b bodyRows depth ordinary before).1 = domain := by
    have replay := SourceSynthesisUniverseDomainReplay.second_replay u b bodyRows depth ordinary
      original before cacheValid growth
    have projected := congrArg (fun result : Interned DomainKey × Cache.State DomainKey => result.1) replay
    exact projected
  have sameState : secondState u b bodyRows depth ordinary before = before :=
    SourceSynthesisUniverseDomainReplay.secondState_replay u b bodyRows depth ordinary original before cacheValid growth
  have self_normalizes (sameChildren : left.children = right.children)
      (shape : left.children = [.node m [markerRow] 0 [], .reference (.interned u.identity),
          .reference (.interned u.identity)] ∨
        ∃ arity, left.children = List.replicate arity (.reference (.interned u.identity))) :
      dead row = true ∨ ∃ source ∈ bodyRows, Readback top u.identity source row := by
    obtain ⟨result, final, completed, _, _, _, readback, _⟩ :=
      SourceSynthesisUniverseRowTransform.edge_self_complete emptyGuard top conjoin conjoinTop domain u.identity
        m [markerRow] 0 left before beforeValid markerBefore leftTop seen shape
    have sameCall : edge emptyGuard conjoin (execute emptyGuard conjoin 8 domain) left right before =
        edge emptyGuard conjoin (execute emptyGuard conjoin 8 domain) left left before := by
      simp only [edge, ← sameChildren, leftTop, rightTop]
    have identical : (Result.done result final : Result String Guard (EdgeValue String Guard)) = .done row after :=
      (sameCall.trans completed).symm.trans returned
    cases identical
    exact Or.inr ⟨left, leftMember, readback⟩
  have cross_normalizes
      (classified : dead row = true ∨
        (row.children = [.node m [markerRow] 0 [], repeatedValue (pair u.identity u.identity),
          repeatedValue (pair u.identity u.identity)] ∧
        row.entry.key = ⟨"->", [.node m [markerRow] 0 [], repeatedValue (pair u.identity u.identity),
          repeatedValue (pair u.identity u.identity)].map Value.referenceOf, top⟩ ∧ dead row = false)) :
      dead row = true ∨ ∃ source ∈ bodyRows, Readback top u.identity source row := by
    rcases classified with deadRow | ⟨children, key, _⟩
    · exact Or.inl deadRow
    · right
      refine ⟨arrow, arrowMember, ?_⟩
      unfold Readback
      rw [SourceSynthesisUniverseRowTransform.arrow_children u.identity m [markerRow] 0 arrow arrowChildren]
      refine ⟨children, ?_⟩
      rw [congrArg EdgeKey.symbol arrowKey]
      exact key
  rcases kinds left leftMember with leftArrow | ⟨leftDescriptor, leftCatalog⟩
  · rcases kinds right rightMember with rightArrow | ⟨rightDescriptor, rightCatalog⟩
    · exact self_normalizes (leftArrow.1.trans rightArrow.1.symm) (Or.inl leftArrow.1)
    · by_cases arity : rightDescriptor.2 = 3
      · have rightThree : right.children = List.replicate 3 (.reference (.interned u.identity)) := by
          simpa only [arity] using rightCatalog.1
        obtain ⟨result, final, completed, _, _, classified, _⟩ :=
          SourceSynthesisUniverseCrossRowIdentity.arrow_catalog_identity u b m bodyRows markerRow depth ordinary
            emptyGuard conjoin top conjoinTop before beforeValid.1 beforeValid.2 universeBefore markerBefore
            leaf markerTop bodyTop left right leftArrow.1 rightThree leftTop rightTop
        rw [sameState, sameDomain] at completed
        have identical : (Result.done result final : Result String Guard (EdgeValue String Guard)) = .done row after :=
          completed.symm.trans returned
        cases identical
        apply cross_normalizes
        have leftLabel := congrArg EdgeKey.symbol leftArrow.2
        change left.entry.key.symbol = "->" at leftLabel
        rw [leftLabel] at classified
        exact classified
      · have different : left.children.length ≠ right.children.length := by
          rw [leftArrow.1, rightCatalog.1, List.length_replicate]
          change 3 ≠ rightDescriptor.2
          exact Ne.symm arity
        exact Or.inl (mismatch_dead emptyGuard conjoin (execute emptyGuard conjoin 8 domain)
          left right before row after beforeValid.1 different returned)
  · rcases kinds right rightMember with rightArrow | ⟨rightDescriptor, rightCatalog⟩
    · by_cases arity : leftDescriptor.2 = 3
      · have leftThree : left.children = List.replicate 3 (.reference (.interned u.identity)) := by
          simpa only [arity] using leftCatalog.1
        obtain ⟨result, final, completed, _, _, classified, _⟩ :=
          SourceSynthesisUniverseCrossRowIdentity.catalog_arrow_identity u b m bodyRows markerRow depth ordinary
            emptyGuard conjoin top conjoinTop before beforeValid.1 beforeValid.2 universeBefore markerBefore
            leaf markerTop bodyTop left right leftThree rightArrow.1 sameSymbol leftTop rightTop
        rw [sameState, sameDomain] at completed
        have identical : (Result.done result final : Result String Guard (EdgeValue String Guard)) = .done row after :=
          completed.symm.trans returned
        cases identical
        apply cross_normalizes
        have rightLabel := congrArg EdgeKey.symbol rightArrow.2
        change right.entry.key.symbol = "->" at rightLabel
        rw [rightLabel] at classified
        exact classified
      · have different : left.children.length ≠ right.children.length := by
          rw [leftCatalog.1, rightArrow.1, List.length_replicate]
          change leftDescriptor.2 ≠ 3
          exact arity
        exact Or.inl (mismatch_dead emptyGuard conjoin (execute emptyGuard conjoin 8 domain)
          left right before row after beforeValid.1 different returned)
    · by_cases arity : leftDescriptor.2 = rightDescriptor.2
      · have sameChildren : left.children = right.children := by
          simp only [leftCatalog.1, rightCatalog.1, arity]
        exact self_normalizes sameChildren (Or.inr ⟨leftDescriptor.2, leftCatalog.1⟩)
      · have different : left.children.length ≠ right.children.length := by
          simpa [leftCatalog.1, rightCatalog.1] using arity
        exact Or.inl (mismatch_dead emptyGuard conjoin (execute emptyGuard conjoin 8 domain)
          left right before row after beforeValid.1 different returned)

end MicroCFTA.SourceSynthesisUniverseRowNormalization
