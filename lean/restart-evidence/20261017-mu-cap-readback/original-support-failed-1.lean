import MicroCFTA.SourceCurrentConstrainedCapNativeOccurrenceCache
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Original source support for ranked native requests

Closed initial records supply original syntax. Literal body, row, and union
projections retain that syntax in the fixed source heap. Domain extension
retains one complete witness for each bound Mu. Later reads use that witness.
These input facts do not assume a returned native result or completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapOriginalSupport
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionEnvironment
open SourceRecursiveIntersectionInputView (Original)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs EdgeInputs)
open SourceCurrentConstrainedCapNativeIdentity (Covered)
open SourceCurrentConstrainedCapPairOccurrences (Classified sourceWeight)
open SourceCurrentConstrainedCap (Cap)
variable {Symbol Guard : Type}

/-- The literal initial domain has no original binding obligation. -/
theorem empty (annotation : Guard → Prop) (source : State Symbol Guard) :
    OriginalBindings annotation source IntersectionEmptyDomain.emptyDomain.key := by
  intro name member
  cases member

private theorem binding_original (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (binding : Nat × Value Symbol Guard) (member : binding ∈ bindings left right) : Original binding.2 := by
  rcases List.mem_append.mp member with first | second
  · cases left <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at first
    subst binding
    exact leftOriginal
  · cases right <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at second
    subst binding
    exact rightOriginal

private theorem binding_covered (domain : DomainKey) (left right : Value Symbol Guard)
    (leftCovered : Covered domain left) (rightCovered : Covered domain right)
    (binding : Nat × Value Symbol Guard) (member : binding ∈ bindings left right) : Covered domain binding.2 := by
  rcases List.mem_append.mp member with first | second
  · cases left <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at first
    subst binding
    exact leftCovered
  · cases right <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at second
    subst binding
    exact rightCovered

/-- Actual extension retains the same complete original source witness for every name. -/
theorem extend (annotation : Guard → Prop) (depth : Nat) (source : State Symbol Guard)
    (domain : DomainKey) (known : OriginalBindings annotation source domain)
    (left right : Value Symbol Guard) (inputs : NodeInputs source ⟨⟨0, domain⟩, left, right⟩)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right)
    (leftCovered : Covered domain left) (rightCovered : Covered domain right) (key : Nat × Nat) :
    OriginalBindings annotation source
      (SourceRecursiveIntersectionDomain.extend domain ((bindings left right).map Prod.fst) key) := by
  intro name member
  rcases (SourceRecursiveIntersectionDomain.extend_names domain _ key name).mp member with added | old
  · obtain ⟨binding, present, rfl⟩ := List.mem_map.mp added
    obtain ⟨entry, body, level, ordinary, same, available⟩ :=
      bindings_available source left right inputs.2.2.1 inputs.2.2.2 binding present
    have annotated := SourceCurrentConstrainedCapNativeScope.bindings_annotated
      annotation depth left right leftCap rightCap binding present
    have covered := binding_covered domain left right leftCovered rightCovered binding present
    have original := binding_original left right inputs.1 inputs.2.1 binding present
    subst binding
    exact ⟨.mu entry body level ordinary, available, rfl, annotated, covered.extend _ key, original⟩
  · obtain ⟨value, available, reference, annotated, covered, original⟩ := known name old
    exact ⟨value, available, reference, annotated, covered.extend _ key, original⟩

/-- Literal source domain allocation retains complete original binding witnesses. -/
theorem enter (annotation : Guard → Prop) (depth : Nat) (source : State Symbol Guard)
    (domain : DomainKey) (known : OriginalBindings annotation source domain)
    (left right : Value Symbol Guard) (inputs : NodeInputs source ⟨⟨0, domain⟩, left, right⟩)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right)
    (leftCovered : Covered domain left) (rightCovered : Covered domain right)
    (cache : Cache.State DomainKey) (valid : Cache.Valid cache) (first second : Nat) :
    OriginalBindings annotation source
      (SourceRecursiveIntersectionEnvironment.enter cache domain left right first second).1.key := by
  rw [SourceRecursiveIntersectionSchedule.entered_key cache valid domain left right first second]
  exact extend annotation depth source domain known left right inputs leftCap rightCap leftCovered rightCovered _

/-- A later literal read returns the same original available source Mu and its coverage. -/
theorem read (annotation : Guard → Prop) (source current : State Symbol Guard)
    (facts : Facts current) (growth : Grows source current)
    (history : Extends source.nodes.issued current.nodes.issued) (domain : DomainKey)
    (known : OriginalBindings annotation source domain) (name : Nat)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain) :
    ∃ value, SourcePreparedSharedRows.read current name = some value ∧ Available source value ∧
      Available current value ∧ value.referenceOf = .mu name ∧
      SourceEqualityAnnotationLanguage.Annotated annotation value ∧ Covered domain value ∧ Original value := by
  obtain ⟨value, available, reference, annotated, covered, original⟩ := known name member
  cases value <;> simp only [Value.referenceOf, reduceCtorEq] at reference
  case mu entry body level ordinary =>
    cases reference
    have resident := available.grows source current growth history
    exact ⟨.mu entry body level ordinary,
      SourcePreparedSharedRows.read_identity current facts _ resident entry.identity rfl,
      available, resident, rfl, annotated, covered, original⟩

/-- Closed initial operands derive original input support from their actual coherent source. -/
theorem closed_inputs (source : State Symbol Guard) (facts : Facts source)
    (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) : NodeInputs source ⟨domain, left, right⟩ :=
  ⟨SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed,
    SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed,
    leftAvailable, rightAvailable⟩

/-- Exposing a literal source body retains original payload syntax and availability. -/
theorem body_input (source : State Symbol Guard) (value : Value Symbol Guard)
    (original : Original value) (available : Available source value) :
    Original (body value) ∧ Available source (body value) := by
  cases original <;> first | exact ⟨by assumption, available.children _ (by simp [children])⟩ | exact ⟨by constructor <;> assumption, available⟩

/-- Each literal ordinary row child remains an original available source operand. -/
theorem node_child (source : State Symbol Guard) (value : Value Symbol Guard)
    (original : Original value) (available : Available source value)
    (edge : EdgeValue Symbol Guard) (selected : edge ∈ nodeEdges value)
    (child : Value Symbol Guard) (member : child ∈ edge.children) : Original child ∧ Available source child := by
  cases original <;> simp only [nodeEdges] at selected <;> try contradiction
  case node entry edges level free children =>
    exact ⟨children edge selected child member,
      available.children child (List.mem_flatMap.mpr ⟨edge, selected, member⟩)⟩

/-- Literal joined rows retain the exact original child support required by row requests. -/
theorem rows_input (source : State Symbol Guard) (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (inputs : NodeInputs source ⟨domain, left, right⟩)
    (first second : EdgeValue Symbol Guard) (leftMember : first ∈ nodeEdges left)
    (rightMember : second ∈ nodeEdges right) : EdgeInputs source ⟨domain, first, second⟩ :=
  ⟨node_child source left inputs.1 inputs.2.2.1 first leftMember,
    node_child source right inputs.2.1 inputs.2.2.2 second rightMember⟩

/-- Every literal member of an original available union is an original source operand. -/
theorem union_member (source : State Symbol Guard) (entry : Interned NodeKey)
    (members : List (Value Symbol Guard)) (level free)
    (original : Original (.union entry members level free))
    (available : Available source (.union entry members level free))
    (child : Value Symbol Guard) (member : child ∈ members) : Original child ∧ Available source child := by
  cases original with
  | union _ _ _ _ children => exact ⟨children child member, available.children child member⟩

/-- Original source operands have zero-weight free names at every request bound. -/
theorem classified (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (value : Value Symbol Guard) (original : Original value) (available : Available source value) (bound : Nat) :
    Classified (sourceWeight annotation source) bound value := by
  have zero : ∀ name ∈ value.free, sourceWeight annotation source name = 0 := by
    intro name member
    obtain ⟨identity, rfl⟩ := original.free_interned source facts value available name member
    rfl
  refine ⟨fun name member => by rw [zero name member]; exact Nat.zero_le _, ?_⟩
  intro name member
  have free := InternedDeepFreeNormalization.deep_free value source facts.coherent available name member
  rw [zero name free]
  omega

end MicroCFTA.SourceCurrentConstrainedCapOriginalSupport
