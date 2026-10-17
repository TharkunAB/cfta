import MicroCFTA.SourceCurrentConstrainedCapNativeScope
import MicroCFTA.SourceRecursiveIntersectionInputLanguage

/-!
# Numeric identities of scoped native operands

Complete records share one canonical identity supply. An interned reference
resolves to an annotated source Mu. It cannot alias a nonhereditary ordinary
record with that numeric identity. Coverage comes from actual free names.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeIdentity
open Cache InternedConstructorTemplates InternedRecordCoherence InternedFreshProbeKeys
open InternedProbeProvenance InternedNestedFacts InternedBinderProtocol
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionControl
open SourceEqualityAnnotationLanguage SourceCurrentHereditaryNativeScope
open SourceRecursiveIntersectionInputView
variable {Symbol Guard : Type}

/-- Every actual free interned reference has a name in the current source domain. -/
def Covered (domain : DomainKey) (value : Value Symbol Guard) : Prop :=
  ∀ name, Reference.interned name ∈ value.free → name ∈ SourceRecursiveIntersectionDomain.names domain

/-- A closed initial operand has no free-name obligation. -/
theorem Covered.closed (domain : DomainKey) (value : Value Symbol Guard) (closed : value.free = []) :
    Covered domain value := by
  intro name present
  rw [closed] at present
  cases present

/-- Actual domain extension retains coverage of every existing operand. -/
theorem Covered.extend {domain : DomainKey} {value : Value Symbol Guard} (covered : Covered domain value)
    (bound : List Nat) (key : Nat × Nat) : Covered (SourceRecursiveIntersectionDomain.extend domain bound key) value := by
  intro name present
  exact (SourceRecursiveIntersectionDomain.extend_names domain bound key name).mpr (.inr (covered name present))

/-- A coherent ordinary child's free names are covered by the parent's domain. -/
theorem Covered.node_child (source : State Symbol Guard) (facts : Facts source)
    (domain : DomainKey) (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (level free)
    (available : Available source (.node entry edges level free))
    (covered : Covered domain (.node entry edges level free))
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges)
    (child : Value Symbol Guard) (inside : child ∈ edge.children) : Covered domain child := by
  intro name present
  exact covered name ((freeNames_member _ name).mp
    (node_free_child source facts entry edges level free available edge member child inside name
      ((freeNames_member child name).mpr present)))

/-- A coherent union member retains the original domain coverage. -/
theorem Covered.union_member (source : State Symbol Guard) (facts : Facts source)
    (domain : DomainKey) (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (level free)
    (available : Available source (.union entry members level free))
    (covered : Covered domain (.union entry members level free))
    (child : Value Symbol Guard) (member : child ∈ members) : Covered domain child := by
  intro name present
  exact covered name ((freeNames_member _ name).mp
    (union_free_child source facts entry members level free available child member name
      ((freeNames_member child name).mpr present)))

/-- Opening a Mu adds its own identity and retains every other covered name. -/
theorem Covered.mu_body (domain : DomainKey) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (covered : Covered domain (.mu entry body depth ordinary))
    (bound : List Nat) (key : Nat × Nat) (added : entry.identity ∈ bound) :
    Covered (SourceRecursiveIntersectionDomain.extend domain bound key) body := by
  intro name present
  by_cases same : name = entry.identity
  · exact (SourceRecursiveIntersectionDomain.extend_names domain bound key name).mpr (.inl (same ▸ added))
  · apply (SourceRecursiveIntersectionDomain.extend_names domain bound key name).mpr
    right
    apply covered name
    rw [Value.free]
    simp only [List.mem_filter, bne_iff_ne]
    exact ⟨present, by simpa only [Reference.interned.injEq] using same⟩

private theorem identity_shape (value : Value Symbol Guard) (number : Nat)
    (found : identity value = some number) :
    (∃ entry, entryOf value = some entry ∧ entry.identity = number) ∨ value = .reference (.interned number) := by
  cases value with
  | empty => cases found
  | reference name =>
      cases name <;> simp only [identity, reduceCtorEq, Option.some.injEq] at found
      subst number
      exact .inr rfl
  | node entry edges level free | union entry members level free | mu entry body depth ordinary =>
      exact .inl ⟨entry, rfl, Option.some.inj found⟩

private theorem bound_record_annotated (annotation : Guard → Prop) (source : State Symbol Guard)
    (facts : Facts source) (domain : DomainKey) (bindings : Bindings annotation source domain)
    (value : Value Symbol Guard) (available : Available source value) (entry : Interned NodeKey)
    (field : entryOf value = some entry) (number : Nat) (same : entry.identity = number)
    (bound : number ∈ SourceRecursiveIntersectionDomain.names domain) : Annotated annotation value := by
  obtain ⟨stored, resident, reference, annotated⟩ := bindings number bound
  cases stored <;> simp only [Value.referenceOf, reduceCtorEq] at reference
  case mu actual body depth ordinary =>
    have numberEq : actual.identity = number := NodeRef.mu.inj reference
    have equal := resident_identity_unique source facts.coherent value (.mu actual body depth ordinary)
      available.resident resident.resident entry actual field rfl (same.trans numberEq.symm)
    exact equal ▸ annotated

/-- Equal numeric identities give the same record or two hereditary source operands. -/
theorem same_identity (annotation : Guard → Prop) (source : State Symbol Guard) (facts : Facts source)
    (domain : DomainKey) (bindings : Bindings annotation source domain)
    (left right : Value Symbol Guard) (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftCovered : Covered domain left) (rightCovered : Covered domain right) (number : Nat)
    (leftId : identity left = some number) (rightId : identity right = some number) :
    left = right ∨ (Annotated annotation left ∧ Annotated annotation right) := by
  rcases identity_shape left number leftId with ⟨first, leftField, leftNumber⟩ | rfl
  · rcases identity_shape right number rightId with ⟨second, rightField, rightNumber⟩ | rfl
    · exact .inl (resident_identity_unique source facts.coherent left right leftAvailable.resident rightAvailable.resident
        first second leftField rightField (leftNumber.trans rightNumber.symm))
    · exact .inr ⟨bound_record_annotated annotation source facts domain bindings left leftAvailable first leftField
        number leftNumber (rightCovered number (by simp [Value.free])), .reference _⟩
  · rcases identity_shape right number rightId with ⟨second, rightField, rightNumber⟩ | rfl
    · exact .inr ⟨.reference _, bound_record_annotated annotation source facts domain bindings right rightAvailable second rightField
        number rightNumber (leftCovered number (by simp [Value.free]))⟩
    · exact .inl rfl

end MicroCFTA.SourceCurrentConstrainedCapNativeIdentity
