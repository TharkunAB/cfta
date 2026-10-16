import MicroCFTA.SourceCurrentHereditaryNativeScope

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.HereditaryNativeScopeIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionEnvironment SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryNativeScope
variable {Symbol Guard : Type}

/-- Actual entry and later heap growth retain the exact encountered binding and its stored body annotation. -/
theorem entered_binding_read (valid : Guard → Prop) (source current : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts current) (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (domain : DomainKey) (old : Bindings valid source domain) (left right : Value Symbol Guard)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftAnnotated : Annotated valid left) (rightAnnotated : Annotated valid right)
    (cache : Cache.State DomainKey) (cacheValid : Cache.Valid cache) (first second : Nat)
    (binding : Nat × Value Symbol Guard) (member : binding ∈ bindings left right) :
    let actual := SourceRecursiveIntersectionEnvironment.enter cache domain left right first second
    Bindings valid source actual.1.key ∧
      SourcePreparedSharedRows.read current binding.1 = some binding.2 ∧
      Available current binding.2 ∧ Annotated valid binding.2 ∧
      Annotated valid (SourceRecursiveIntersectionKernel.body binding.2) := by
  dsimp only
  have entered := old.enter valid source domain left right leftAvailable rightAvailable leftAnnotated rightAnnotated
    cache cacheValid first second
  have inside : binding.1 ∈ SourceRecursiveIntersectionDomain.names
      (SourceRecursiveIntersectionEnvironment.enter cache domain left right first second).1.key := by
    rw [SourceRecursiveIntersectionSchedule.entered_key cache cacheValid domain left right first second]
    exact (SourceRecursiveIntersectionDomain.extend_names domain _ _ binding.1).mpr
      (Or.inl (List.mem_map.mpr ⟨binding, member, rfl⟩))
  obtain ⟨value, found, _, available, _, annotated⟩ :=
    entered.read valid source current facts growth history _ binding.1 inside
  obtain ⟨entry, stored, depth, ordinary, same, originalAvailable⟩ :=
    bindings_available source left right leftAvailable rightAvailable binding member
  subst binding
  have expected := SourcePreparedSharedRows.read_identity current facts (.mu entry stored depth ordinary)
    (originalAvailable.grows source current growth history) entry.identity rfl
  have exactValue : value = .mu entry stored depth ordinary := Option.some.inj (found.symm.trans expected)
  subst value
  exact ⟨entered, found, available, annotated, body_annotated valid _ annotated⟩

/-- Both actual Mu operands may carry arbitrary probes while their entered stored bodies retain annotations. -/
theorem two_mu_entries (valid : Guard → Prop) (source current : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts current) (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (left right : Interned NodeKey) (leftBody rightBody leftDepth rightDepth leftOrdinary rightOrdinary : Value Symbol Guard)
    (leftAvailable : Available source (.mu left leftBody leftDepth leftOrdinary))
    (rightAvailable : Available source (.mu right rightBody rightDepth rightOrdinary))
    (leftAnnotated : Annotated valid leftBody) (rightAnnotated : Annotated valid rightBody)
    (cache : Cache.State DomainKey) (cacheValid : Cache.Valid cache) :
    let actual := SourceRecursiveIntersectionEnvironment.enter cache IntersectionEmptyDomain.emptyKey
      (.mu left leftBody leftDepth leftOrdinary) (.mu right rightBody rightDepth rightOrdinary) left.identity right.identity
    Bindings valid source actual.1.key ∧
      SourcePreparedSharedRows.read current left.identity = some (.mu left leftBody leftDepth leftOrdinary) ∧
      SourcePreparedSharedRows.read current right.identity = some (.mu right rightBody rightDepth rightOrdinary) ∧
      Annotated valid (SourceRecursiveIntersectionKernel.body (.mu left leftBody leftDepth leftOrdinary)) ∧
      Annotated valid (SourceRecursiveIntersectionKernel.body (.mu right rightBody rightDepth rightOrdinary)) := by
  dsimp only
  have first := entered_binding_read valid source current facts growth history IntersectionEmptyDomain.emptyKey
    (empty valid source) (.mu left leftBody leftDepth leftOrdinary) (.mu right rightBody rightDepth rightOrdinary)
    leftAvailable rightAvailable (.mu left leftBody leftDepth leftOrdinary leftAnnotated)
    (.mu right rightBody rightDepth rightOrdinary rightAnnotated) cache cacheValid left.identity right.identity
    (left.identity, .mu left leftBody leftDepth leftOrdinary) (by simp [bindings, binder])
  have second := entered_binding_read valid source current facts growth history IntersectionEmptyDomain.emptyKey
    (empty valid source) (.mu left leftBody leftDepth leftOrdinary) (.mu right rightBody rightDepth rightOrdinary)
    leftAvailable rightAvailable (.mu left leftBody leftDepth leftOrdinary leftAnnotated)
    (.mu right rightBody rightDepth rightOrdinary rightAnnotated) cache cacheValid left.identity right.identity
    (right.identity, .mu right rightBody rightDepth rightOrdinary) (by simp [bindings, binder])
  exact ⟨first.1, first.2.1, second.2.1, first.2.2.2.2, second.2.2.2.2⟩

#print axioms entered_binding_read
#check @entered_binding_read
#print axioms two_mu_entries
#check @two_mu_entries
end MicroCFTA.HereditaryNativeScopeIndependent
