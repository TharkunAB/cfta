import MicroCFTA.SourceCurrentConstrainedCap
import MicroCFTA.SourceCurrentHereditaryNativeScope

/-!
# Local source bindings for finite constrained caps

Only Mu operands add source bindings. A capped Mu is hereditary at every
cap depth. This fact supplies actual entered names and their later reads.
Ordinary constrained records outside these bindings remain permitted.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeScope
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionEnvironment SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentHereditaryNativeScope (Bindings)
variable {Symbol Guard : Type}

/-- A capped Mu operand is hereditary regardless of the finite cap depth. -/
theorem mu_annotated {annotation : Guard → Prop} {depth : Nat} {entry body level ordinary}
    (bounded : Cap annotation depth (Value.mu (Symbol := Symbol) entry body level ordinary)) :
    Annotated annotation (.mu entry body level ordinary) := by
  cases bounded with
  | plain _ annotated => exact annotated

/-- The literal domain bindings contain only hereditary source Mu operands. -/
theorem bindings_annotated (annotation : Guard → Prop) (depth : Nat) (left right : Value Symbol Guard)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right)
    (binding : Nat × Value Symbol Guard) (member : binding ∈ bindings left right) : Annotated annotation binding.2 := by
  rcases List.mem_append.mp member with first | second
  · cases left <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at first
    subst binding
    exact mu_annotated leftCap
  · cases right <;> simp only [binder, List.mem_nil_iff, List.mem_singleton] at second
    subst binding
    exact mu_annotated rightCap

/-- Actual extension retains old local bindings and the encountered capped Mu operands. -/
theorem extend (annotation : Guard → Prop) (depth : Nat) (source : State Symbol Guard)
    (domain : DomainKey) (known : Bindings annotation source domain) (left right : Value Symbol Guard)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right) (key : Nat × Nat) :
    Bindings annotation source (SourceRecursiveIntersectionDomain.extend domain ((bindings left right).map Prod.fst) key) := by
  intro name member
  rcases (SourceRecursiveIntersectionDomain.extend_names domain _ key name).mp member with added | retained
  · obtain ⟨binding, present, rfl⟩ := List.mem_map.mp added
    obtain ⟨entry, stored, level, ordinary, same, available⟩ :=
      bindings_available source left right leftAvailable rightAvailable binding present
    have annotated := bindings_annotated annotation depth left right leftCap rightCap binding present
    subst binding
    exact ⟨.mu entry stored level ordinary, available, rfl, annotated⟩
  · exact known name retained

/-- Literal allocated entry retains the exact domain-key binding contract. -/
theorem enter (annotation : Guard → Prop) (depth : Nat) (source : State Symbol Guard)
    (domain : DomainKey) (known : Bindings annotation source domain) (left right : Value Symbol Guard)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftCap : Cap annotation depth left) (rightCap : Cap annotation depth right)
    (cache : Cache.State DomainKey) (valid : Cache.Valid cache) (first second : Nat) :
    Bindings annotation source (SourceRecursiveIntersectionEnvironment.enter cache domain left right first second).1.key := by
  rw [SourceRecursiveIntersectionSchedule.entered_key cache valid domain left right first second]
  exact extend annotation depth source domain known left right leftAvailable rightAvailable leftCap rightCap _

/-- A legitimate later read returns the exact hereditary source Mu, not an arbitrary heap record. -/
theorem read (annotation : Guard → Prop) (source current : State Symbol Guard)
    (facts : Facts current) (growth : Grows source current) (history : Extends source.nodes.issued current.nodes.issued)
    (domain : DomainKey) (known : Bindings annotation source domain) (name : Nat)
    (member : name ∈ SourceRecursiveIntersectionDomain.names domain) :
    ∃ value, SourcePreparedSharedRows.read current name = some value ∧ Available source value ∧
      Available current value ∧ value.referenceOf = .mu name ∧ Annotated annotation value :=
  known.read annotation source current facts growth history domain name member

/-- Stored-body projection retains the same cap; a Mu body uses its hereditary annotation. -/
theorem body_cap (annotation : Guard → Prop) (depth : Nat) (value : Value Symbol Guard)
    (bounded : Cap annotation depth value) : Cap annotation depth (SourceRecursiveIntersectionKernel.body value) := by
  cases value with
  | mu entry stored level ordinary =>
      exact .plain depth (SourceCurrentHereditaryNativeScope.body_annotated annotation _ (mu_annotated bounded))
  | empty | node | ref | union => exact bounded

/-- Every actual ordinary input row has its parent's cap depth. -/
theorem node_edge (annotation : Guard → Prop) (depth : Nat) (value : Value Symbol Guard)
    (bounded : Cap annotation depth value) (edge : EdgeValue Symbol Guard) (member : edge ∈ nodeEdges value) : Edge annotation depth edge :=
  SourceCurrentConstrainedCap.node_edge bounded edge member

/-- Actual zipped child operands have the smaller depth used by accepted edge code. -/
theorem edge_child (annotation : Guard → Prop) (depth : Nat) (left right : EdgeValue Symbol Guard)
    (leftCap : Edge annotation depth left) (rightCap : Edge annotation depth right)
    (children : Value Symbol Guard × Value Symbol Guard) (member : children ∈ left.children.zip right.children) :
    Cap annotation (depth - 1) children.1 ∧ Cap annotation (depth - 1) children.2 := by
  have inside := List.of_mem_zip member
  cases depth with
  | zero => exact ⟨.plain 0 (leftCap.2 _ inside.1), .plain 0 (rightCap.2 _ inside.2)⟩
  | succ depth => exact ⟨leftCap _ inside.1, rightCap _ inside.2⟩

end MicroCFTA.SourceCurrentConstrainedCapNativeScope
