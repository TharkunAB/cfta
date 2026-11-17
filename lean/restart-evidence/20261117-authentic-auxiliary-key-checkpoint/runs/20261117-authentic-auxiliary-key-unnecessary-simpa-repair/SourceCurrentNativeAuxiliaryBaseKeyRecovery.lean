import MicroCFTA.SourceRecursiveIntersectionDomain
import MicroCFTA.SourceSynthesisUniverseMixedDescendantFreshness

/-!
# Original base keys in actual auxiliary source domains

The keys have one authentic singleton base and the actual auxiliary pairs.
The old parent pair is distinct from both auxiliary pairs. Equal resulting
keys therefore retain the same base pair. One coherent reader derives the
required distinctions from the actual closed pattern, open body, and Mu.
-/
namespace MicroCFTA.SourceCurrentNativeAuxiliaryBaseKeyRecovery
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
set_option autoImplicit false

/- Note [Recover the original base pair]
Do not cancel extensions of arbitrary domain keys. The four keys below
extend the same singleton empty base by the actual body/diagonal pairs.
The old parent pair survives in seen. The source records exclude it from
both auxiliary pairs. Equality then identifies the new parent pair.
The open body uses actual physical readback; it need not be closed.
-/

private theorem pair_fixed_owner_injective (owner first second : Nat)
    (same : pair owner first = pair owner second) : first = second := by
  simp only [pair, Prod.mk.injEq] at same
  omega

private theorem ordinary_reference {Symbol Guard : Type}
    (value : Value Symbol Guard) (valueId : Nat)
    (identified : identity value = some valueId) (kind : tag value = 1 ∨ tag value = 3) :
    SourcePreparedSharedRows.reference value = some valueId := by
  cases value with
  | node entry rows depth free =>
      simpa only [identity, SourcePreparedSharedRows.reference] using identified
  | union entry members depth free =>
      simpa only [identity, SourcePreparedSharedRows.reference] using identified
  | empty | reference | mu => simp [tag] at kind

/-- Equal auxiliary keys with the authentic shapes identify their original base pair. -/
theorem auxiliary_key_eq_recovers_singleton_base
    (owner : Nat) (oldParent newParent extra diagonal : Nat × Nat)
    (oldKey newKey : IntersectionFlatMemoKeyDomain.DomainKey)
    (oldApartExtra : oldParent ≠ extra) (oldApartDiagonal : oldParent ≠ diagonal)
    (oldShape :
      (oldKey = extend (extend IntersectionEmptyDomain.emptyKey [owner] oldParent) [owner] extra ∨
      oldKey = extend (extend (extend IntersectionEmptyDomain.emptyKey [owner] oldParent) [owner] extra) [owner] diagonal ∨
      oldKey = extend (extend IntersectionEmptyDomain.emptyKey [owner] oldParent) [owner] diagonal ∨
      oldKey = extend (extend (extend IntersectionEmptyDomain.emptyKey [owner] oldParent) [owner] diagonal) [owner] extra))
    (newShape :
      (newKey = extend (extend IntersectionEmptyDomain.emptyKey [owner] newParent) [owner] extra ∨
      newKey = extend (extend (extend IntersectionEmptyDomain.emptyKey [owner] newParent) [owner] extra) [owner] diagonal ∨
      newKey = extend (extend IntersectionEmptyDomain.emptyKey [owner] newParent) [owner] diagonal ∨
      newKey = extend (extend (extend IntersectionEmptyDomain.emptyKey [owner] newParent) [owner] diagonal) [owner] extra))
    (same : oldKey = newKey) :
    oldParent = newParent ∧
      extend IntersectionEmptyDomain.emptyKey [owner] oldParent =
        extend IntersectionEmptyDomain.emptyKey [owner] newParent := by
  have oldMember : oldParent ∈ oldKey.seen := by
    rcases oldShape with rfl | rfl | rfl | rfl
    all_goals simp [extend_seen, IntersectionEmptyDomain.emptyKey]
  have newMember : oldParent ∈ newKey.seen := by
    simpa only [same] using oldMember
  have parentSame : oldParent = newParent := by
    rcases newShape with rfl | rfl | rfl | rfl
    · simpa only [extend_seen, IntersectionEmptyDomain.emptyKey, List.not_mem_nil,
        or_false, oldApartExtra, false_or] using newMember
    · simpa only [extend_seen, IntersectionEmptyDomain.emptyKey, List.not_mem_nil,
        or_false, oldApartExtra, oldApartDiagonal, false_or] using newMember
    · simpa only [extend_seen, IntersectionEmptyDomain.emptyKey, List.not_mem_nil,
        or_false, oldApartDiagonal, false_or] using newMember
    · simpa only [extend_seen, IntersectionEmptyDomain.emptyKey, List.not_mem_nil,
        or_false, oldApartExtra, oldApartDiagonal, false_or] using newMember
  exact ⟨parentSame, congrArg (fun parent =>
    extend IntersectionEmptyDomain.emptyKey [owner] parent) parentSame⟩

/-- Actual closed pattern and open-body records separate the parent pair from both auxiliary pairs. -/
theorem source_parent_pair_avoids_auxiliary
    {Symbol Guard : Type} (heap : State Symbol Guard) (facts : Facts heap)
    (universeEntry bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard)
    (universeAvailable : Available heap
      (.mu universeEntry (.node bodyEntry bodyRows 0 [.interned universeEntry.identity]) depth ordinary))
    (pattern : Value Symbol Guard) (patternId : Nat)
    (patternAvailable : Available heap pattern) (patternClosed : pattern.free = [])
    (patternIdentity : identity pattern = some patternId)
    (patternKind : tag pattern = 1 ∨ tag pattern = 3) :
    pair universeEntry.identity patternId ≠ pair bodyEntry.identity universeEntry.identity ∧
      pair universeEntry.identity patternId ≠ pair universeEntry.identity universeEntry.identity := by
  have bodyAvailable : Available heap
      (.node bodyEntry bodyRows 0 [.interned universeEntry.identity]) :=
    universeAvailable.children _ (by simp [children])
  have patternRead := SourcePreparedSharedRows.read_identity heap facts pattern patternAvailable
    patternId (ordinary_reference pattern patternId patternIdentity patternKind)
  have bodyRead := SourcePreparedSharedRows.read_identity heap facts
    (.node bodyEntry bodyRows 0 [.interned universeEntry.identity]) bodyAvailable bodyEntry.identity rfl
  have universeRead := SourcePreparedSharedRows.read_identity heap facts
    (.mu universeEntry (.node bodyEntry bodyRows 0 [.interned universeEntry.identity]) depth ordinary)
    universeAvailable universeEntry.identity rfl
  have apartBody : patternId ≠ bodyEntry.identity := by
    intro same
    have patternAtBody : SourcePreparedSharedRows.read heap bodyEntry.identity = some pattern := by
      simpa only [same] using patternRead
    have valueSame : pattern = .node bodyEntry bodyRows 0 [.interned universeEntry.identity] :=
      Option.some.inj (patternAtBody.symm.trans bodyRead)
    have impossible : ([.interned universeEntry.identity] : List Reference) = [] := by
      simpa only [Value.free] using (congrArg Value.free valueSame).symm.trans patternClosed
    cases impossible
  have apartUniverse : patternId ≠ universeEntry.identity := by
    intro same
    have patternAtUniverse : SourcePreparedSharedRows.read heap universeEntry.identity = some pattern := by
      simpa only [same] using patternRead
    have valueSame : pattern =
        .mu universeEntry (.node bodyEntry bodyRows 0 [.interned universeEntry.identity]) depth ordinary :=
      Option.some.inj (patternAtUniverse.symm.trans universeRead)
    have sameKind := patternKind
    rw [valueSame] at sameKind
    simp [tag] at sameKind
  constructor
  · intro same
    have symmetric : pair bodyEntry.identity universeEntry.identity =
        pair universeEntry.identity bodyEntry.identity := by
      simp only [pair, Nat.min_comm, Nat.max_comm]
    exact apartBody (pair_fixed_owner_injective universeEntry.identity patternId bodyEntry.identity
      (same.trans symmetric))
  · intro same
    exact apartUniverse (pair_fixed_owner_injective universeEntry.identity patternId universeEntry.identity same)

/-- One coherent source reader recovers the complete parent pattern from equal auxiliary keys. -/
theorem source_auxiliary_key_eq_recovers_full_pattern
    {Symbol Guard : Type} (heap : State Symbol Guard) (facts : Facts heap)
    (universeEntry bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (depth ordinary : Value Symbol Guard)
    (universeAvailable : Available heap
      (.mu universeEntry (.node bodyEntry bodyRows 0 [.interned universeEntry.identity]) depth ordinary))
    (oldPattern newPattern : Value Symbol Guard) (oldPatternId newPatternId : Nat)
    (oldAvailable : Available heap oldPattern) (newAvailable : Available heap newPattern)
    (oldClosed : oldPattern.free = []) (newClosed : newPattern.free = [])
    (oldIdentity : identity oldPattern = some oldPatternId)
    (newIdentity : identity newPattern = some newPatternId)
    (oldKind : tag oldPattern = 1 ∨ tag oldPattern = 3)
    (oldKey newKey : IntersectionFlatMemoKeyDomain.DomainKey)
    (oldShape :
      (oldKey = extend (extend IntersectionEmptyDomain.emptyKey [universeEntry.identity] (pair universeEntry.identity oldPatternId)) [universeEntry.identity] (pair bodyEntry.identity universeEntry.identity) ∨
      oldKey = extend (extend (extend IntersectionEmptyDomain.emptyKey [universeEntry.identity] (pair universeEntry.identity oldPatternId)) [universeEntry.identity] (pair bodyEntry.identity universeEntry.identity)) [universeEntry.identity] (pair universeEntry.identity universeEntry.identity) ∨
      oldKey = extend (extend IntersectionEmptyDomain.emptyKey [universeEntry.identity] (pair universeEntry.identity oldPatternId)) [universeEntry.identity] (pair universeEntry.identity universeEntry.identity) ∨
      oldKey = extend (extend (extend IntersectionEmptyDomain.emptyKey [universeEntry.identity] (pair universeEntry.identity oldPatternId)) [universeEntry.identity] (pair universeEntry.identity universeEntry.identity)) [universeEntry.identity] (pair bodyEntry.identity universeEntry.identity)))
    (newShape :
      (newKey = extend (extend IntersectionEmptyDomain.emptyKey [universeEntry.identity] (pair universeEntry.identity newPatternId)) [universeEntry.identity] (pair bodyEntry.identity universeEntry.identity) ∨
      newKey = extend (extend (extend IntersectionEmptyDomain.emptyKey [universeEntry.identity] (pair universeEntry.identity newPatternId)) [universeEntry.identity] (pair bodyEntry.identity universeEntry.identity)) [universeEntry.identity] (pair universeEntry.identity universeEntry.identity) ∨
      newKey = extend (extend IntersectionEmptyDomain.emptyKey [universeEntry.identity] (pair universeEntry.identity newPatternId)) [universeEntry.identity] (pair universeEntry.identity universeEntry.identity) ∨
      newKey = extend (extend (extend IntersectionEmptyDomain.emptyKey [universeEntry.identity] (pair universeEntry.identity newPatternId)) [universeEntry.identity] (pair universeEntry.identity universeEntry.identity)) [universeEntry.identity] (pair bodyEntry.identity universeEntry.identity)))
    (same : oldKey = newKey) :
    oldPatternId = newPatternId ∧ oldPattern = newPattern ∧
      extend IntersectionEmptyDomain.emptyKey [universeEntry.identity]
        (pair universeEntry.identity oldPatternId) =
      extend IntersectionEmptyDomain.emptyKey [universeEntry.identity]
        (pair universeEntry.identity newPatternId) := by
  obtain ⟨apartExtra, apartDiagonal⟩ := source_parent_pair_avoids_auxiliary
    heap facts universeEntry bodyEntry bodyRows depth ordinary universeAvailable
    oldPattern oldPatternId oldAvailable oldClosed oldIdentity oldKind
  obtain ⟨parentSame, baseSame⟩ := auxiliary_key_eq_recovers_singleton_base
    universeEntry.identity (pair universeEntry.identity oldPatternId)
    (pair universeEntry.identity newPatternId) (pair bodyEntry.identity universeEntry.identity)
    (pair universeEntry.identity universeEntry.identity) oldKey newKey apartExtra apartDiagonal
    oldShape newShape same
  have identitySame : oldPatternId = newPatternId :=
    pair_fixed_owner_injective universeEntry.identity oldPatternId newPatternId parentSame
  have valueSame : oldPattern = newPattern :=
    SourceSynthesisUniverseMixedDescendantFreshness.closed_identity_injective heap facts
      oldPattern newPattern oldAvailable newAvailable oldClosed newClosed oldPatternId oldIdentity
      (by simpa only [identitySame] using newIdentity)
  exact ⟨identitySame, valueSame, baseSame⟩

end MicroCFTA.SourceCurrentNativeAuxiliaryBaseKeyRecovery
