import MicroCFTA.SourceCurrentConstrainedCapNativeIdentity

/-!
# Produced reference coverage of actual native bindings

Each bound source Mu retains its own covered free names. Actual entry adds
the encountered Mu identities before exposing their bodies. Later reads use
the same immutable source record. No future result law is a premise.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeCoverage
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceEqualityAnnotationLanguage
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionEnvironment
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapNativeIdentity (Covered)
variable {Symbol Guard : Type}

/-- Bound names retain the annotated source Mu and its current free-name coverage. -/
def Bindings (annotation : Guard → Prop) (source : State Symbol Guard) (domain : DomainKey) : Prop :=
  ∀ name ∈ SourceRecursiveIntersectionDomain.names domain,
    ∃ value, Available source value ∧ value.referenceOf = .mu name ∧
      Annotated annotation value ∧ Covered domain value

/-- The literal initial domain has no binding obligations. -/
theorem empty (annotation : Guard → Prop) (source : State Symbol Guard) :
    Bindings annotation source IntersectionEmptyDomain.emptyDomain.key := by
  intro name member
  cases member

/-- Covered binding entries supply the existing local hereditary source contract. -/
theorem Bindings.annotated {annotation : Guard → Prop} {source : State Symbol Guard} {domain : DomainKey}
    (known : Bindings annotation source domain) : SourceCurrentHereditaryNativeScope.Bindings annotation source domain := by
  intro name member
  obtain ⟨value, available, reference, annotated, _covered⟩ := known name member
  exact ⟨value, available, reference, annotated⟩

private theorem bindings_covered (domain : DomainKey) (left right : Value Symbol Guard)
    (leftCovered : Covered domain left) (rightCovered : Covered domain right)
    (binding : Nat × Value Symbol Guard) (member : binding ∈ bindings left right) : Covered domain binding.2 := by
  rcases List.mem_append.mp member with first | second
  · cases left <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at first
    subst binding
    exact leftCovered
  · cases right <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at second
    subst binding
    exact rightCovered

/-- Actual domain extension retains annotation and coverage for every old and new source Mu. -/
theorem Bindings.extend (annotation : Guard → Prop) (depth : Nat) (source : State Symbol Guard)
    (domain : DomainKey) (known : Bindings annotation source domain) (left right : Value Symbol Guard)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right)
    (leftCovered : Covered domain left) (rightCovered : Covered domain right) (key : Nat × Nat) :
    Bindings annotation source (SourceRecursiveIntersectionDomain.extend domain ((bindings left right).map Prod.fst) key) := by
  intro name member
  rcases (SourceRecursiveIntersectionDomain.extend_names domain _ key name).mp member with added | old
  · obtain ⟨binding, present, rfl⟩ := List.mem_map.mp added
    obtain ⟨entry, body, level, ordinary, same, available⟩ :=
      bindings_available source left right leftAvailable rightAvailable binding present
    have annotated := SourceCurrentConstrainedCapNativeScope.bindings_annotated annotation depth left right leftCap rightCap binding present
    have covered := bindings_covered domain left right leftCovered rightCovered binding present
    subst binding
    exact ⟨.mu entry body level ordinary, available, rfl, annotated, covered.extend _ key⟩
  · obtain ⟨value, available, reference, annotated, covered⟩ := known name old
    exact ⟨value, available, reference, annotated, covered.extend _ key⟩

/-- Exposing the actual left operand body retains every needed source name. -/
theorem left_body_covered (domain : DomainKey) (left right : Value Symbol Guard)
    (covered : Covered domain left) (key : Nat × Nat) :
    Covered (SourceRecursiveIntersectionDomain.extend domain ((bindings left right).map Prod.fst) key) (body left) := by
  cases left with
  | empty | reference | node | union => exact covered.extend _ key
  | mu entry stored level ordinary =>
      exact covered.mu_body domain entry stored level ordinary _ key (by simp [bindings, binder])

/-- Exposing the actual right operand body retains every needed source name. -/
theorem right_body_covered (domain : DomainKey) (left right : Value Symbol Guard)
    (covered : Covered domain right) (key : Nat × Nat) :
    Covered (SourceRecursiveIntersectionDomain.extend domain ((bindings left right).map Prod.fst) key) (body right) := by
  cases right with
  | empty | reference | node | union => exact covered.extend _ key
  | mu entry stored level ordinary =>
      exact covered.mu_body domain entry stored level ordinary _ key (by simp [bindings, binder])

/-- Literal domain allocation produces covered bindings and both covered exposed bodies. -/
theorem enter (annotation : Guard → Prop) (depth : Nat) (source : State Symbol Guard)
    (domain : DomainKey) (known : Bindings annotation source domain) (left right : Value Symbol Guard)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right)
    (leftCovered : Covered domain left) (rightCovered : Covered domain right)
    (cache : Cache.State DomainKey) (valid : Cache.Valid cache) (first second : Nat) :
    let actual := SourceRecursiveIntersectionEnvironment.enter cache domain left right first second
    Bindings annotation source actual.1.key ∧ Covered actual.1.key (body left) ∧ Covered actual.1.key (body right) := by
  dsimp only
  rw [SourceRecursiveIntersectionSchedule.entered_key cache valid domain left right first second]
  exact ⟨known.extend annotation depth source domain left right leftAvailable rightAvailable leftCap rightCap leftCovered rightCovered _,
    left_body_covered domain left right leftCovered _, right_body_covered domain left right rightCovered _⟩

/-- A legitimate later source read retains annotation, physical identity, and current domain coverage. -/
theorem Bindings.read (annotation : Guard → Prop) (source current : State Symbol Guard)
    (facts : Facts current) (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (domain : DomainKey) (known : Bindings annotation source domain) (name : Nat)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain) :
    ∃ value, SourcePreparedSharedRows.read current name = some value ∧ Available source value ∧
      Available current value ∧ value.referenceOf = .mu name ∧ Annotated annotation value ∧ Covered domain value := by
  obtain ⟨value, available, reference, annotated, covered⟩ := known name member
  cases value <;> simp only [Value.referenceOf, reduceCtorEq] at reference
  case mu entry stored level ordinary =>
    cases reference
    have resident := available.grows source current growth history
    exact ⟨.mu entry stored level ordinary,
      SourcePreparedSharedRows.read_identity current facts _ resident entry.identity rfl,
      available, resident, rfl, annotated, covered⟩

end MicroCFTA.SourceCurrentConstrainedCapNativeCoverage
