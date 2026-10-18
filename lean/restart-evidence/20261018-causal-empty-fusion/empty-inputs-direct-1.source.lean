import MicroCFTA.SourceCurrentStoredProfileEmptyProjection
import MicroCFTA.SourceCurrentScopedProfileInputs
import MicroCFTA.SourceCurrentReaderReplacementSlots

/-!
# Empty-projected assignments on live source inputs

Paired reference slots retain their resolved physical Empty tests. Ready
replacement records reflect those tests in their profiles. Nonreference
captures retain equal maps on their free names. Live source support selects
only the required lexical entries. No reader-wide input availability is
required for default references or unused captures.
-/
namespace MicroCFTA.SourceCurrentEmptyProjectionInputs
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryLiveInputs (input inputProfile)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile profile)
open InternedProfileSemantics (isEmpty)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentReaderReplacementSlots (Slot Paired)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentStoredProfileEmptyProjection (canonical)

private theorem member_slot {Atom : Type} (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Environment Symbol Guard)
    (paired : Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second
      (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (selected : Sum (Value Symbol Guard) Atom) (member : selected ∈ inputs) :
    Slot (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second
      (input firstNames selected) (input secondNames selected) := by
  induction inputs with
  | nil => cases member
  | cons head tail ih =>
      cases paired with
      | cons first rest =>
          rcases List.mem_cons.mp member with rfl | member
          · exact first
          · exact ih rest member

private theorem resolved_empty (reader : State Symbol Guard) (ready : Ready reader)
    (environment : Environment Symbol Guard) (replacements : Replacements reader environment) (name : Reference) :
    isEmpty (profile ((environment name).getD (.reference name))) =
      (((environment name).getD (.reference name)).referenceOf == .empty) := by
  cases found : environment name with
  | none => simp only [Option.getD_none,profile,isEmpty,Value.referenceOf,List.isEmpty_cons,reduceBEq]
  | some value =>
      exact InternedRootProfileNode.isEmpty_profile value reader ready.semantic.1.normal.proper
        (replacements name value found)

private theorem reference_slot (reader : State Symbol Guard) (ready : Ready reader)
    (first second : Environment Symbol Guard) (firstReplacements : Replacements reader first)
    (secondReplacements : Replacements reader second) (firstName secondName : Reference)
    (paired : Slot (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second
      (.reference firstName) (.reference secondName)) :
    canonical (fun name => profile ((first name).getD (.reference name))) firstName =
      canonical (fun name => profile ((second name).getD (.reference name))) secondName := by
  unfold canonical
  rw [resolved_empty reader ready first firstReplacements firstName,
    resolved_empty reader ready second secondReplacements secondName]
  change (if ((first firstName).getD (.reference firstName)).referenceOf == .empty then some [] else none) =
    (if ((second secondName).getD (.reference secondName)).referenceOf == .empty then some [] else none)
  rw [paired]

private theorem fixed_slot (reader : State Symbol Guard) (ready : Ready reader)
    (first second : Environment Symbol Guard) (firstReplacements : Replacements reader first)
    (secondReplacements : Replacements reader second) (value : Value Symbol Guard)
    (paired : Slot (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second value value) :
    ∀ name ∈ value.free,
      canonical (fun name => profile ((first name).getD (.reference name))) name =
        canonical (fun name => profile ((second name).getD (.reference name))) name := by
  cases value with
  | reference own =>
      intro name member
      have same : name = own := by simpa only [Value.free,List.mem_singleton] using member
      subst name
      exact reference_slot reader ready first second firstReplacements secondReplacements own own paired
  | empty | node | union | mu =>
      intro name member
      have same := paired.2 name member
      simp only [same]

private theorem varying_origin {Atom : Type} (expression : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (atom : Atom)
    (member : .inr atom ∈ support expression inputs) : .inr atom ∈ inputs := by
  obtain ⟨names,present,included⟩ := InternedFreeNameSemantics.evaluate_origins expression
    (inputs.map inputProfile) (inputs.map inputNames) (.inr atom) member
  obtain ⟨selected,present,rfl⟩ := List.mem_map.mp present
  cases selected with
  | inl value => simp [inputNames] at included
  | inr other =>
      have same : atom = other := by simpa only [inputNames,List.mem_singleton,Sum.inr.injEq] using included
      simpa only [same] using present

/-- Paired physical Empty tests derive the live compatibility of canonical resolved assignments. -/
theorem compatible {Atom : Type} (reader : State Symbol Guard) (ready : Ready reader)
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Environment Symbol Guard)
    (paired : Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second
      (inputs.map (input firstNames)) (inputs.map (input secondNames)))
    (firstReplacements : Replacements reader first) (secondReplacements : Replacements reader second) :
    SourceCurrentScopedProfileInputs.Compatible expression inputs firstNames secondNames
      (canonical (fun name => profile ((first name).getD (.reference name))))
      (canonical (fun name => profile ((second name).getD (.reference name)))) := by
  constructor
  · intro name live
    obtain ⟨value,present,included⟩ := SourceCurrentNativeNormalizationInputs.fixed_origin expression inputs name live
    exact fixed_slot reader ready first second firstReplacements secondReplacements value
      (member_slot inputs firstNames secondNames first second paired (.inl value) present) name included
  · intro atom live
    exact reference_slot reader ready first second firstReplacements secondReplacements (firstNames atom) (secondNames atom)
      (member_slot inputs firstNames secondNames first second paired (.inr atom) (varying_origin expression inputs atom live))

end MicroCFTA.SourceCurrentEmptyProjectionInputs
