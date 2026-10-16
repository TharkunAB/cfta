import MicroCFTA.SourceCurrentAllocatedNativeContextualCode
import MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning

/-!
# Local certificates for actual original reference branches

Original source bindings derive the current literal Mu readback after heap
growth. Only the exact resolved child request supplies a local node law.
The certificate preserves the original input model and operand order.
A missing binding certifies the literal failure branch. This does not
assert successful execution or general recursive completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativeContextCache SourceCurrentAllocatedNativeContextualCode
open SourceCurrentAllocatedNativeReferenceMeaning
open InternedBinderProtocol
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Current readback determines the exact original source binder and its identity. -/
theorem resolve (source current : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts current) (growth : Grows source current)
    (history : Extends source.nodes.issued current.nodes.issued)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain)
    (name : Nat) (member : name ∈ SourceRecursiveIntersectionDomain.names domain) :
    ∃ entry body depth ordinary, entry.identity = name ∧ Original (.mu entry body depth ordinary) ∧
      Available source (.mu entry body depth ordinary) ∧
      SourcePreparedSharedRows.read current name = some (.mu entry body depth ordinary) := by
  obtain ⟨value, found, original, available, encoded⟩ := bindings.read source current facts growth history domain name member
  cases original <;>
    simp only [inputOf, Value.referenceOf, IntersectionFlatMemoKey.input, Option.getD_some, reduceCtorEq, IntersectSchedule.Input.mu.injEq] at encoded <;>
    try contradiction
  case mu entry body depth ordinary original =>
    exact ⟨entry, body, depth, ordinary, encoded, .mu entry body depth ordinary original, available, found⟩

/-- A left source reference certifies only its literal read and exact bound child request. -/
theorem left_code [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain.key)
    (name : Nat) (other : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (growth : Grows source state.heap)
    (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified (view source holds) model ranked holds (compileReference domain name other true) state
      (fun _ result => NodeLaw (view source holds) model ranked holds ⟨domain, .reference (.interned name), other⟩ result) := by
  by_cases member : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨entry, body, depth, ordinary, same, original, _, found⟩ :=
      resolve source state.heap valid.1 growth history domain.key bindings name member
    simp only [compileReference, ite_eq_left member, Certified, found]
    intro result after _ _ _ _ law
    exact left_law (view source holds) model ranked holds domain name other entry body depth ordinary result same original law
  · simp only [compileReference, ite_eq_right member, Certified]

/-- A right source reference retains its original operand order in the child certificate. -/
theorem right_code [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain.key)
    (name : Nat) (other : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (growth : Grows source state.heap)
    (history : Extends source.nodes.issued state.heap.nodes.issued) :
    Certified (view source holds) model ranked holds (compileReference domain name other false) state
      (fun _ result => NodeLaw (view source holds) model ranked holds ⟨domain, other, .reference (.interned name)⟩ result) := by
  by_cases member : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨entry, body, depth, ordinary, same, original, _, found⟩ :=
      resolve source state.heap valid.1 growth history domain.key bindings name member
    simp only [compileReference, ite_eq_left member, Certified, found]
    intro result after _ _ _ _ law
    exact right_law (view source holds) model ranked holds domain name other entry body depth ordinary result same original law
  · simp only [compileReference, ite_eq_right member, Certified]

/-- Actual selected left reference compilation has its derived local contextual certificate. -/
theorem left_reference [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain.key)
    (name : Nat) (other : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (growth : Grows source state.heap)
    (history : Extends source.nodes.issued state.heap.nodes.issued)
    (selected : SourceRecursiveIntersectionControl.decision domain.key (.reference (.interned name)) other = .leftReference) :
    Certified (view source holds) model ranked holds (compileNode ⟨domain, .reference (.interned name), other⟩) state
      (fun _ result => NodeLaw (view source holds) model ranked holds ⟨domain, .reference (.interned name), other⟩ result) := by
  simpa only [compileNode, selected] using left_code source holds model ranked domain bindings name other state valid growth history

/-- Actual selected right reference compilation has its derived local contextual certificate. -/
theorem right_reference [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Term Symbol → Bool)
    (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (bindings : OriginalBindings source domain.key)
    (name : Nat) (other : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (growth : Grows source state.heap)
    (history : Extends source.nodes.issued state.heap.nodes.issued)
    (selected : SourceRecursiveIntersectionControl.decision domain.key other (.reference (.interned name)) = .rightReference) :
    Certified (view source holds) model ranked holds (compileNode ⟨domain, other, .reference (.interned name)⟩) state
      (fun _ result => NodeLaw (view source holds) model ranked holds ⟨domain, other, .reference (.interned name)⟩ result) := by
  simpa only [compileNode, selected] using right_code source holds model ranked domain bindings name other state valid growth history

end MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates
