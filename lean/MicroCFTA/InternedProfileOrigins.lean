import MicroCFTA.InternedProfileCallbackForm

/-!
# Captured reference provenance in the pure profile interpreter

A pure output reference comes from an original lexical input. Smart local
references do not escape their binder. The symbolic callback form therefore
contains only names from its fixed captured profiles.
-/
namespace MicroCFTA.InternedProfileOrigins
open InternedNestedConstruction InternedProfileSemantics InternedProfileCallbackForm
open InternedRootProfile (Profile)
open InternedBinderProtocol (Reference)

/-- A union output reference came from one of its original operands. -/
theorem combine_origin (first second : Abstract Atom) (atom : Atom)
    (present : atom ∈ (combine first second).getD []) :
    atom ∈ first.getD [] ∨ atom ∈ second.getD [] := by
  cases first <;> cases second <;> simp_all [combine]

/-- An ordered union output reference came from an original profile. -/
theorem combineMany_origin (values : List (Abstract Atom)) (atom : Atom)
    (present : atom ∈ (combineMany values).getD []) :
    ∃ value ∈ values, atom ∈ value.getD [] := by
  induction values with
  | nil => simp [combineMany] at present
  | cons first rest ih =>
      rcases combine_origin first (combineMany rest) atom present with head | tail
      · exact ⟨first, by simp, head⟩
      · obtain ⟨value, member, selected⟩ := ih tail
        exact ⟨value, by simp [member], selected⟩

/-- Removing a smart local retains exactly the external symbolic names. -/
theorem lower_member (value : Abstract (Sum Unit Atom)) (atom : Atom) :
    atom ∈ (lower value).getD [] ↔ Sum.inr atom ∈ value.getD [] := by
  cases value with
  | none => simp [lower]
  | some names =>
      simp only [lower, Option.getD_some]
      induction names with
      | nil => simp
      | cons first rest ih => cases first <;> simp [ih]

/-- A mapped profile reference comes from an original literal name. -/
theorem mapNames_member (function : Atom → Other) (value : Abstract Atom) (atom : Other) :
    atom ∈ (mapNames function value).getD [] ↔ ∃ original ∈ value.getD [], function original = atom := by
  cases value <;> simp [mapNames]

mutual
/-- Every pure result reference originates in the source expression's lexical inputs. -/
theorem evaluate_origin {Atom : Type} (expression : Syntax Symbol Guard) (environment : List (Abstract Atom))
    (atom : Atom) (present : atom ∈ (evaluate expression environment).getD []) :
    ∃ value ∈ environment, atom ∈ value.getD [] := by
  cases expression with
  | empty => simp [evaluate] at present
  | var index =>
      rw [evaluate] at present
      cases found : environment[index]? with
      | none => simp [found] at present
      | some value => exact ⟨value, List.mem_of_getElem? found, by simpa only [found, Option.getD_some] using present⟩
  | node edges =>
      rw [evaluate] at present
      cases selected : evaluateEdges edges environment <;> simp [selected] at present
  | union members =>
      rw [evaluate] at present
      obtain ⟨value, member, selected⟩ := combineMany_origin (evaluateMany members environment) atom present
      exact evaluateMany_origin members environment value member atom selected
  | binder smart body =>
      cases smart with
      | false => simp [evaluate] at present
      | true =>
          rw [evaluate, lower_member] at present
          obtain ⟨value, member, selected⟩ := evaluate_origin body
            (some [Sum.inl ()] :: environment.map (mapNames Sum.inr)) (Sum.inr atom) present
          rcases List.mem_cons.mp member with rfl | member
          · simp at selected
          · obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
            obtain ⟨name, source, same⟩ := (mapNames_member Sum.inr original (Sum.inr atom)).mp selected
            have equal : name = atom := Sum.inr.inj same
            exact ⟨original, included, equal ▸ source⟩
termination_by sizeOf expression

/-- Each pure ordered child result retains lexical reference provenance. -/
theorem evaluateMany_origin {Atom : Type} (expressions : List (Syntax Symbol Guard)) (environment : List (Abstract Atom))
    (value : Abstract Atom) (member : value ∈ evaluateMany expressions environment) (atom : Atom)
    (present : atom ∈ value.getD []) : ∃ original ∈ environment, atom ∈ original.getD [] := by
  cases expressions with
  | nil => simp [evaluateMany] at member
  | cons first rest =>
      rw [evaluateMany] at member
      rcases List.mem_cons.mp member with rfl | member
      · exact evaluate_origin first environment atom present
      · exact evaluateMany_origin rest environment value member atom present
termination_by sizeOf expressions
end

/-- Captured symbolic names are exactly the right-tagged result members. -/
theorem captures_member (names : List (Sum Unit Reference)) (name : Reference) :
    name ∈ captures names ↔ Sum.inr name ∈ names := by
  constructor
  · intro member
    obtain ⟨original, included, same⟩ := List.mem_filterMap.mp member
    cases original with
    | inl token => cases same
    | inr value => cases same; exact included
  · intro member
    exact List.mem_filterMap.mpr ⟨.inr name, member, rfl⟩

/-- Fixed names in the syntax-derived callback form come only from its captured profiles. -/
theorem captures_origin (body : Syntax Symbol Guard) (environment : List Profile)
    (names : List (Sum Unit Reference)) (computed : symbolic body environment = some names)
    (name : Reference) (present : name ∈ captures names) :
    ∃ value ∈ environment, name ∈ value.getD [] := by
  have member : Sum.inr name ∈ names := (captures_member names name).mp present
  have observed : Sum.inr name ∈ (symbolic body environment).getD [] := by simp [computed, member]
  obtain ⟨value, included, selected⟩ := evaluate_origin body
    (some [Sum.inl ()] :: environment.map (mapNames Sum.inr)) (Sum.inr name) observed
  rcases List.mem_cons.mp included with rfl | included
  · simp at selected
  · obtain ⟨original, source, rfl⟩ := List.mem_map.mp included
    obtain ⟨other, member, equal⟩ := (mapNames_member Sum.inr original (Sum.inr name)).mp selected
    exact ⟨original, source, (Sum.inr.inj equal) ▸ member⟩

/-- A fresh actual binder name cannot occur among the fixed names of its symbolic callback form. -/
theorem captures_fresh (body : Syntax Symbol Guard) (environment : List Profile)
    (names : List (Sum Unit Reference)) (computed : symbolic body environment = some names)
    (name : Reference) (fresh : ∀ value ∈ environment, name ∉ value.getD []) : name ∉ captures names := by
  intro member
  obtain ⟨value, included, present⟩ := captures_origin body environment names computed name member
  exact fresh value included present

end MicroCFTA.InternedProfileOrigins
