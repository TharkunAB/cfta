import MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionInputView SourceCurrentAllocatedNativeContextCache
open SourceCurrentAllocatedNativeContextualCode SourceCurrentAllocatedNativeContextualReferenceCertificates
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates.resolve
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates.left_code
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates.right_code
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates.left_reference
#print axioms MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates.right_reference
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates.resolve
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates.left_code
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates.right_code
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates.left_reference
#check @MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates.right_reference

namespace ReferenceCertificateChecks
noncomputable section
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq Symbol := Classical.typeDecidableEq _
local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.typeDecidableEq _

-- 1. Empty original binding scope is derived, not supplied as a future lookup.
example (source : InternedConstructorTemplates.State Symbol Guard) :
    OriginalBindings source IntersectionEmptyDomain.emptyDomain.key := by
  intro name member
  cases member

-- 2. A missing original name remains the literal failure code.
example (name : Nat) (other : Value Symbol Guard) (side : Bool) :
    compileReference IntersectionEmptyDomain.emptyDomain name other side = .fail (.missingBinder name) := rfl

-- 3. Failure certification asserts no result, even for an impossible result condition.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (state : Machine Symbol Guard) (name : Nat) :
    Certified view model ranked holds (Code.fail (.missingBinder name) : Code Symbol Guard (Value Symbol Guard)) state
      (fun _ _ => False) := True.intro

-- 4. Left certification needs no completed child, future result, or trace in the original heap.
example (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view state.heap holds))
    (ranked : IntersectSchedule.RankedInput (view state.heap holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings state.heap domain.key)
    (name : Nat) (other : Value Symbol Guard) :
    Certified (view state.heap holds) model ranked holds (compileReference domain name other true) state
      (fun _ result => NodeLaw (view state.heap holds) model ranked holds ⟨domain, .reference (.interned name), other⟩ result) :=
  left_code state.heap holds model ranked domain bindings name other state valid
    (InternedConstructorTemplates.grows_refl _) (Cache.extends_refl _)

-- 5. Right certification preserves the literal right-child request at the same source heap.
example (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view state.heap holds))
    (ranked : IntersectSchedule.RankedInput (view state.heap holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings state.heap domain.key)
    (name : Nat) (other : Value Symbol Guard) :
    Certified (view state.heap holds) model ranked holds (compileReference domain name other false) state
      (fun _ result => NodeLaw (view state.heap holds) model ranked holds ⟨domain, other, .reference (.interned name)⟩ result) :=
  right_code state.heap holds model ranked domain bindings name other state valid
    (InternedConstructorTemplates.grows_refl _) (Cache.extends_refl _)

-- 6. Reached readback derives the exact original Mu identity after actual source growth.
example (source current : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts current) (growth : Grows source current)
    (history : Extends source.nodes.issued current.nodes.issued)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain)
    (name : Nat) (member : name ∈ SourceRecursiveIntersectionDomain.names domain) :
    ∃ entry body depth ordinary, entry.identity = name ∧ Original (.mu entry body depth ordinary) ∧
      SourcePreparedSharedRows.read current name = some (.mu entry body depth ordinary) := by
  obtain ⟨entry, body, depth, ordinary, same, original, _, readback⟩ :=
    resolve source current facts growth history domain bindings name member
  exact ⟨entry, body, depth, ordinary, same, original, readback⟩
end
end ReferenceCertificateChecks
