import MicroCFTA.SourceCurrentHereditaryConstructors
import MicroCFTA.SourceRecursiveIntersectionRequestScope
import MicroCFTA.SourceRecursiveIntersectionDomainEquivalence

/-!
# Local hereditary annotations of recursive source bindings

Each domain name retains its own available annotated Mu record in the source
heap. Later reads use that exact record. Unrelated resident guards remain
unrestricted. A reference annotation alone does not certify its stored payload.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativeScope
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionEnvironment SourceEqualityAnnotationLanguage
variable {Symbol Guard : Type}

/-- Bound names retain their exact available annotated source Mu records. -/
def Bindings (valid : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (domain : DomainKey) : Prop :=
  ∀ name ∈ SourceRecursiveIntersectionDomain.names domain,
    ∃ value, Available source value ∧ value.referenceOf = .mu name ∧ Annotated valid value

/-- The literal initial empty domain has no annotation binding obligation. -/
theorem empty (valid : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard) :
    Bindings valid source IntersectionEmptyDomain.emptyDomain.key := by
  intro name member
  cases member

/-- Actual left-before-right binding entries retain the annotations of their original operands. -/
theorem bindings_annotated (valid : Guard → Prop) (left right : Value Symbol Guard)
    (leftAnnotated : Annotated valid left) (rightAnnotated : Annotated valid right)
    (binding : Nat × Value Symbol Guard) (member : binding ∈ bindings left right) : Annotated valid binding.2 := by
  rcases List.mem_append.mp member with first | second
  · cases left <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at first
    subst binding
    exact leftAnnotated
  · cases right <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at second
    subst binding
    exact rightAnnotated

/-- Actual domain extension retains annotations at every old and newly bound identity. -/
theorem Bindings.extend (valid : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (domain : DomainKey) (old : Bindings valid source domain) (left right : Value Symbol Guard)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftAnnotated : Annotated valid left) (rightAnnotated : Annotated valid right) (key : Nat × Nat) :
    Bindings valid source (SourceRecursiveIntersectionDomain.extend domain ((bindings left right).map Prod.fst) key) := by
  intro name member
  rcases (SourceRecursiveIntersectionDomain.extend_names domain _ key name).mp member with added | retained
  · obtain ⟨binding, present, rfl⟩ := List.mem_map.mp added
    obtain ⟨entry, stored, depth, ordinary, same, available⟩ :=
      bindings_available source left right leftAvailable rightAvailable binding present
    have annotated := bindings_annotated valid left right leftAnnotated rightAnnotated binding present
    subst binding
    exact ⟨.mu entry stored depth ordinary, available, rfl, annotated⟩
  · exact old name retained

/-- The exact allocated domain key retains annotations from its actual encountered operands. -/
theorem Bindings.enter (valid : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (domain : DomainKey) (old : Bindings valid source domain) (left right : Value Symbol Guard)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftAnnotated : Annotated valid left) (rightAnnotated : Annotated valid right)
    (cache : Cache.State DomainKey) (cacheValid : Cache.Valid cache) (first second : Nat) :
    Bindings valid source (SourceRecursiveIntersectionEnvironment.enter cache domain left right first second).1.key := by
  rw [SourceRecursiveIntersectionSchedule.entered_key cache cacheValid domain left right first second]
  exact old.extend valid source domain left right leftAvailable rightAvailable leftAnnotated rightAnnotated _

/-- A later literal read returns the same annotated source Mu after actual heap and issued-map growth. -/
theorem Bindings.read (valid : Guard → Prop) (source current : InternedConstructorTemplates.State Symbol Guard)
    (facts : Facts current) (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (domain : DomainKey) (known : Bindings valid source domain) (name : Nat)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain) :
    ∃ value, SourcePreparedSharedRows.read current name = some value ∧ Available source value ∧
      Available current value ∧ value.referenceOf = .mu name ∧ Annotated valid value := by
  obtain ⟨value, available, reference, annotated⟩ := known name member
  cases value <;> simp only [Value.referenceOf, reduceCtorEq] at reference
  case mu entry stored depth ordinary =>
    cases reference
    have resident := available.grows source current growth history
    exact ⟨.mu entry stored depth ordinary,
      SourcePreparedSharedRows.read_identity current facts _ resident entry.identity rfl,
      available, resident, rfl, annotated⟩

/-- Actual source body projection retains the original annotation and ignores Mu probes. -/
theorem body_annotated (valid : Guard → Prop) (value : Value Symbol Guard)
    (annotated : Annotated valid value) : Annotated valid (SourceRecursiveIntersectionKernel.body value) := by
  cases annotated <;> first | assumption | constructor <;> assumption

/-- Each actual ordinary input row retains its guard and annotated children. -/
theorem node_edge (valid : Guard → Prop) (value : Value Symbol Guard) (annotated : Annotated valid value)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ nodeEdges value) :
    SourceCurrentHereditaryConstructors.Edge valid edge :=
  SourceCurrentHereditaryConstructors.node_edge annotated edge member

/-- Each actual zipped child request retains both operand annotations without an arity premise. -/
theorem edge_child (valid : Guard → Prop) (left right : EdgeValue Symbol Guard)
    (leftAnnotated : SourceCurrentHereditaryConstructors.Edge valid left)
    (rightAnnotated : SourceCurrentHereditaryConstructors.Edge valid right)
    (children : Value Symbol Guard × Value Symbol Guard) (member : children ∈ left.children.zip right.children) :
    Annotated valid children.1 ∧ Annotated valid children.2 := by
  have inside := List.of_mem_zip member
  exact ⟨leftAnnotated.2 children.1 inside.1, rightAnnotated.2 children.2 inside.2⟩

end MicroCFTA.SourceCurrentHereditaryNativeScope
