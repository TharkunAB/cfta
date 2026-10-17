import MicroCFTA.SourceCurrentConstrainedCapNativeCode

/-!
# Finite-cap certificates for actual row and union compilation

Joined rows and union members retain the same input cap depth. Each
continuation uses the actual returned machine and its local request law.
These certificates do not cover mixed Mu optional binding or completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapNativeCompile
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage SourceCurrentConstrainedCapNativeCode
open SourceCurrentConstrainedCap (Cap Edge)
open SourceCurrentHereditaryNativeScope (Bindings)
variable {Symbol Guard : Type}
variable (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
  (representation : InternedConstructorTemplates.State Symbol Guard → Prop)
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Literal hash-joined rows retain their own guards and child caps. -/
theorem rows_certified [DecidableEq Symbol] (depth : Nat) (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (represented : representation state.heap)
    (bindings : Bindings annotation source domain.key)
    (leftAnnotated : ∀ edge ∈ left, Edge annotation depth edge)
    (rightAnnotated : ∀ edge ∈ right, Edge annotation depth edge) :
    Certified annotation source representation (compileRows domain left right) state
      (fun after value => Available after.heap value ∧ Cap annotation depth value) := by
  let input := fun (_ : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Edge annotation depth pair.1 ∧ Edge annotation depth pair.2
  let output := fun (after : Machine Symbol Guard) (edge : EdgeValue Symbol Guard) =>
    EdgeResident after.heap edge ∧ Edge annotation depth edge
  have walked := certified_walk annotation source representation
    (fun pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard => requestEdge domain pair.1 pair.2)
    (pairs left right) input output (by intro _ _ _ _ known; exact known)
    (by intro before after growth edge known; exact ⟨edge_stable before after growth edge known.1, known.2⟩)
    (by intro pair _ current _ _ known; exact request_edge annotation source representation depth ⟨domain, pair.1, pair.2⟩ current bindings known.1 known.2)
    state valid represented (by
      intro pair member
      have inside := (pairs_member left right pair).mp member
      exact ⟨leftAnnotated pair.1 inside.1, rightAnnotated pair.2 inside.2.1⟩)
  unfold compileRows
  apply certified_bind annotation source representation _ _ state valid represented _ _ walked
  intro values after afterValid _ _ returned
  exact node_work annotation source representation depth values after afterValid
    (fun edge member => (returned edge member).1) (fun edge member => (returned edge member).2)

/-- Each left union callback retains its literal member and original right operand. -/
theorem left_union_certified (depth : Nat) (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (right : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (represented : representation state.heap)
    (bindings : Bindings annotation source domain.key)
    (membersAnnotated : ∀ value ∈ members, Cap annotation depth value) (rightAnnotated : Cap annotation depth right) :
    Certified annotation source representation
      ((walk (fun member => requestNode domain member right) members).bind fun values => .work (makeUnion values) .pure)
      state (fun after value => Available after.heap value ∧ Cap annotation depth value) := by
  have walked := certified_walk annotation source representation
    (fun member => requestNode domain member right) members (fun _ value => Cap annotation depth value)
    (fun after value => Available after.heap value ∧ Cap annotation depth value)
    (by intro _ _ _ _ known; exact known)
    (by intro before after growth value known; exact ⟨growth.available value known.1, known.2⟩)
    (by intro value _ current _ _ known; exact request_node annotation source representation depth ⟨domain, value, right⟩ current bindings known rightAnnotated)
    state valid represented membersAnnotated
  apply certified_bind annotation source representation _ _ state valid represented _ _ walked
  intro values after afterValid _ _ returned
  exact union_work annotation source representation depth values after afterValid
    (fun value member => (returned value member).1) (fun value member => (returned value member).2)

/-- Each right union callback retains the original left operand and literal member. -/
theorem right_union_certified (depth : Nat) (domain : Interned DomainKey) (left : Value Symbol Guard)
    (members : List (Value Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (represented : representation state.heap)
    (bindings : Bindings annotation source domain.key) (leftAnnotated : Cap annotation depth left)
    (membersAnnotated : ∀ value ∈ members, Cap annotation depth value) :
    Certified annotation source representation
      ((walk (fun member => requestNode domain left member) members).bind fun values => .work (makeUnion values) .pure)
      state (fun after value => Available after.heap value ∧ Cap annotation depth value) := by
  have walked := certified_walk annotation source representation
    (fun member => requestNode domain left member) members (fun _ value => Cap annotation depth value)
    (fun after value => Available after.heap value ∧ Cap annotation depth value)
    (by intro _ _ _ _ known; exact known)
    (by intro before after growth value known; exact ⟨growth.available value known.1, known.2⟩)
    (by intro value _ current _ _ known; exact request_node annotation source representation depth ⟨domain, left, value⟩ current bindings leftAnnotated known)
    state valid represented membersAnnotated
  apply certified_bind annotation source representation _ _ state valid represented _ _ walked
  intro values after afterValid _ _ returned
  exact union_work annotation source representation depth values after afterValid
    (fun value member => (returned value member).1) (fun value member => (returned value member).2)

end MicroCFTA.SourceCurrentConstrainedCapNativeCompile
