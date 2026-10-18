import MicroCFTA.SourceCurrentStoredRootDeletionConstruction
import MicroCFTA.SourceCurrentNativeCallbackErasure
import MicroCFTA.InternedFilterSelfReference

/-!
# Original root deletion after actual self filtering and bare erasure

The actual filter removes self from root unions. Bare erasure removes
standalone self. Together they add self to the original deletion tests.
They do not remove names later exposed by a Mu or a replacement.
-/
namespace MicroCFTA.SourceCurrentStoredRootDeletionErasure
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open InternedProfileSemantics (combine)
open InternedStoredMuOrigins (Normal)
open InternedUnionNormalForm (Atomic)
open SourceCurrentStoredRootDeletion (deleted deletedMany)
open SourceCurrentNativeCallbackErasure (eraseSelf)

private theorem atomic (cuts : Reference → Bool) (own : Reference) (value : Value Symbol Guard)
    (assignment : Reference → Profile) (flat : Atomic value) :
    deleted (fun name => cuts name || (name == own)) value assignment =
      if value.referenceOf == .ref own then some [] else deleted cuts value assignment := by
  cases value with
  | empty => simp only [deleted,Value.referenceOf,beq_iff_eq,reduceCtorEq,ite_false]
  | reference name =>
      by_cases same : name = own
      · subst name
        simp only [deleted,beq_self_eq_true,Bool.or_true,ite_true,Value.referenceOf]
      · have different : (name == own) = false := Bool.eq_false_iff.mpr (fun found => same (eq_of_beq found))
        simp only [deleted,different,Bool.or_false,Value.referenceOf,beq_iff_eq,
          InternedBinderProtocol.NodeRef.ref.injEq,same,ite_false]
  | node | mu => simp only [deleted,Value.referenceOf,beq_iff_eq,reduceCtorEq,ite_false]
  | union => cases flat

private theorem members (cuts : Reference → Bool) (own : Reference)
    (values : List (Value Symbol Guard)) (assignment : Reference → Profile)
    (flat : ∀ value ∈ values, Atomic value) :
    deletedMany cuts (values.filter (fun member => member.referenceOf != .ref own)) assignment =
      deletedMany (fun name => cuts name || (name == own)) values assignment := by
  induction values with
  | nil => rw [List.filter_nil,deletedMany,deletedMany]
  | cons first rest ih =>
      rw [deletedMany,atomic cuts own first assignment (flat first List.mem_cons_self)]
      have tail := ih (fun value member => flat value (List.mem_cons_of_mem _ member))
      simp only [bne] at tail
      by_cases selected : first.referenceOf == .ref own
      · simp only [selected,ite_true,List.filter_cons,bne,Bool.not_true,Bool.false_eq_true,ite_false]
        rw [tail]
        cases deletedMany (fun name => cuts name || (name == own)) rest assignment <;> rfl
      · have kept : (first.referenceOf == .ref own) = false := Bool.eq_false_iff.mpr selected
        simp only [kept,Bool.false_eq_true,ite_false,List.filter_cons,bne,Bool.not_false,ite_true,deletedMany]
        rw [tail]

/-- Actual self filtering and bare erasure add only the original own reference to deletion. -/
theorem erased_filter [DecidableEq (EdgeKey Symbol Guard)]
    (cuts : Reference → Bool) (own : Reference) (raw : Value Symbol Guard)
    (assignment : Reference → Profile) (state : State Symbol Guard)
    (normal : Normal state) (available : Available state raw) :
    Equivalent (deleted cuts (eraseSelf own (run (withoutSelfReference own raw) state).1) assignment)
      (deleted (fun name => cuts name || (name == own)) raw assignment) := by
  cases raw with
  | empty =>
      simp only [withoutSelfReference,run,eraseSelf,Value.referenceOf,reduceCtorEq,ite_false,deleted]
      exact ⟨Iff.rfl,fun _ => Iff.rfl⟩
  | reference name =>
      by_cases same : name = own
      · subst name
        simp only [withoutSelfReference,run,eraseSelf,Value.referenceOf,ite_true,deleted,
          beq_self_eq_true,Bool.or_true]
        exact ⟨Iff.rfl,fun _ => Iff.rfl⟩
      · have different : (name == own) = false := Bool.eq_false_iff.mpr (fun found => same (eq_of_beq found))
        simp only [withoutSelfReference,run,eraseSelf,Value.referenceOf,InternedBinderProtocol.NodeRef.ref.injEq,
          same,ite_false,deleted,different,Bool.or_false]
        exact ⟨Iff.rfl,fun _ => Iff.rfl⟩
  | node | mu =>
      simp only [withoutSelfReference,run,eraseSelf,Value.referenceOf,reduceCtorEq,ite_false,deleted]
      exact ⟨Iff.rfl,fun _ => Iff.rfl⟩
  | union entry values depth free =>
      have notBare : (run (withoutSelfReference own (.union entry values depth free)) state).1.referenceOf ≠ .ref own := by
        intro same
        have returned := (referenceOf_self_iff own _).mp same
        have original := (InternedFilterSelfReference.filter_self_iff own (.union entry values depth free)
          state normal.facts.coherent normal.flat available).mp returned
        cases original
      rw [eraseSelf,ite_eq_right notBare,deleted]
      have flat := InternedUnionNormalForm.resident_flat state normal.flat _ available.resident
      by_cases selected : values.any (fun member => member.referenceOf == .ref own) = true
      · simp only [withoutSelfReference,selected,ite_true]
        rw [←members cuts own values assignment flat]
        apply SourceCurrentStoredRootDeletionConstruction.makeUnion cuts _ assignment state normal
        intro value member
        exact available.children value (List.mem_filter.mp member).1
      · have missing : (values.any (fun member => member.referenceOf == .ref own)) = false := Bool.eq_false_iff.mpr selected
        have unchanged : values.filter (fun member => member.referenceOf != .ref own) = values := by
          apply List.filter_eq_self.mpr
          intro value member
          have absent : (value.referenceOf == .ref own) = false :=
            Bool.eq_false_iff.mpr (fun found => selected (List.any_eq_true.mpr ⟨value,member,found⟩))
          simp only [bne,absent,Bool.not_false]
        simp only [withoutSelfReference,missing,Bool.false_eq_true,ite_false,run,deleted]
        rw [←members cuts own values assignment flat,unchanged]
        exact ⟨Iff.rfl,fun _ => Iff.rfl⟩

end MicroCFTA.SourceCurrentStoredRootDeletionErasure
