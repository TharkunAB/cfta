import MicroCFTA.SourceCurrentAllocatedNativeContextualMuCertificates
open MicroCFTA MicroCFTA.Cache
open InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionInputView
open SourceRecursiveIntersectionThunks SourceCurrentAllocatedNativeContextualMuCertificates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

#print axioms identity_nonempty
#print axioms payload_recursive
#print axioms selected_fresh
#print axioms optional_law
#print axioms mu_certified
#check @identity_nonempty
#check @payload_recursive
#check @selected_fresh
#check @optional_law
#check @mu_certified

example (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (right : Value Symbol Guard) :
    (∃ name, inputOf (.mu entry body depth ordinary) = .mu name) ∨ ∃ name, inputOf right = .mu name :=
  payload_recursive (.mu entry body depth ordinary) right (by
    cases right <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl))

example (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (original : Original body) : inputOf (.mu entry body depth ordinary) ≠ .empty :=
  identity_nonempty _ (.mu entry body depth ordinary original) entry.identity rfl
