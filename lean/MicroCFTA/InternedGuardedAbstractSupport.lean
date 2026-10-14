import MicroCFTA.InternedGuardedSyntax
import MicroCFTA.InternedFreeNameSemantics

/-!
# Semantic support of root profiles and free names

A pure root profile bounds its language by the listed reference languages.
Free names bound the changes to an ambient environment that can affect a
language. These two properties remain valid when a binder removes its local.
-/
namespace MicroCFTA.InternedGuardedAbstractSupport
open Language InternedProfileSemantics
open BinderLanguage (Lang Included least)

/-- Interpret the listed root alternatives in an ambient environment. -/
def roots (environment : Atom → Lang Symbol) (names : List Atom) : Lang Symbol :=
  fun term => ∃ name ∈ names, environment name term

/-- A present root profile bounds the language by its literal alternatives. -/
def Upper (environment : Atom → Lang Symbol) : Abstract Atom → Lang Symbol → Prop
  | none, _ => True
  | some names, language => Included language (roots environment names)

/-- Two ambient environments agree on every listed free name. -/
def Agree (before after : Atom → Lang Symbol) (names : List Atom) : Prop :=
  ∀ name ∈ names, before name = after name

/-- Root bounds and free-name support relate two interpretations of one plan. -/
structure Related (profile : Abstract Atom) (names : List Atom)
    (before after : Atom → Lang Symbol) (left right : Lang Symbol) : Prop where
  upper_left : Upper before profile left
  upper_right : Upper after profile right
  support : Agree before after names → left = right

/-- Empty syntax has no roots and reads no ambient name. -/
theorem related_empty (before after : Atom → Lang Symbol) :
    Related (some []) [] before after (fun _ => False) (fun _ => False) :=
  ⟨fun _ impossible => False.elim impossible, fun _ impossible => False.elim impossible, fun _ => rfl⟩

/-- Combining two alternatives retains their root bounds. -/
theorem upper_combine (environment : Atom → Lang Symbol) (first second : Abstract Atom)
    (left right : Lang Symbol) (leftBound : Upper environment first left) (rightBound : Upper environment second right) :
    Upper environment (combine first second) (fun term => left term ∨ right term) := by
  cases first with
  | none => trivial
  | some names =>
      cases second with
      | none => trivial
      | some others =>
          rintro term (accepted | accepted)
          · obtain ⟨name, member, accepted⟩ := leftBound term accepted
            exact ⟨name, List.mem_append_left _ member, accepted⟩
          · obtain ⟨name, member, accepted⟩ := rightBound term accepted
            exact ⟨name, List.mem_append_right _ member, accepted⟩

/-- Union retains both semantic root bounds and free-name support. -/
theorem related_combine (before after : Atom → Lang Symbol)
    (first second : Abstract Atom) (firstNames secondNames : List Atom)
    (leftFirst rightFirst leftSecond rightSecond : Lang Symbol)
    (firstRelated : Related first firstNames before after leftFirst rightFirst)
    (secondRelated : Related second secondNames before after leftSecond rightSecond) :
    Related (combine first second) (firstNames ++ secondNames) before after
      (fun term => leftFirst term ∨ leftSecond term) (fun term => rightFirst term ∨ rightSecond term) := by
  refine ⟨upper_combine _ _ _ _ _ firstRelated.upper_left secondRelated.upper_left,
    upper_combine _ _ _ _ _ firstRelated.upper_right secondRelated.upper_right, ?_⟩
  intro agree
  rw [firstRelated.support (fun name member => agree name (List.mem_append_left _ member)),
    secondRelated.support (fun name member => agree name (List.mem_append_right _ member))]

/-- A binder assigns a language to its local and retains every external name. -/
def extend (environment : Atom → Lang Symbol) (language : Lang Symbol) : Sum Unit Atom → Lang Symbol
  | .inl _ => language
  | .inr name => environment name

/-- Lifting an input profile preserves its root bound under any local language. -/
theorem upper_lift (environment : Atom → Lang Symbol) (candidate language : Lang Symbol)
    (profile : Abstract Atom) (bound : Upper environment profile language) :
    Upper (extend environment candidate) (mapNames Sum.inr profile) language := by
  cases profile with
  | none => trivial
  | some names =>
      intro term accepted
      obtain ⟨name, member, accepted⟩ := bound term accepted
      exact ⟨.inr name, List.mem_map.mpr ⟨name, member, rfl⟩, accepted⟩

/-- A lifted captured input remains supported by its external free names. -/
theorem related_lift (before after : Atom → Lang Symbol) (leftCandidate rightCandidate : Lang Symbol)
    (profile : Abstract Atom) (names : List Atom) (left right : Lang Symbol)
    (related : Related profile names before after left right) :
    Related (mapNames Sum.inr profile) (names.map Sum.inr)
      (extend before leftCandidate) (extend after rightCandidate) left right := by
  refine ⟨upper_lift _ _ _ _ related.upper_left, upper_lift _ _ _ _ related.upper_right, ?_⟩
  intro agree
  exact related.support (fun name member => agree (.inr name) (List.mem_map.mpr ⟨name, member, rfl⟩))

/-- The new lexical input reads exactly the new local language. -/
theorem related_local (before after : Atom → Lang Symbol) (left right : Lang Symbol) :
    Related (some [Sum.inl ()]) [.inl ()] (extend before left) (extend after right) left right := by
  refine ⟨fun term accepted => ⟨.inl (), by simp, accepted⟩,
    fun term accepted => ⟨.inl (), by simp, accepted⟩, ?_⟩
  intro agree
  exact agree (.inl ()) (by simp)

/-- Removing the local from a pure profile gives a closed candidate for its body. -/
theorem lower_closed (environment : Atom → Lang Symbol) (names : List (Sum Unit Atom))
    (transform : Lang Symbol → Lang Symbol)
    (bound : ∀ candidate, Upper (extend environment candidate) (some names) (transform candidate)) :
    Upper environment (lower (some names)) (least transform) := by
  apply BinderLanguage.least_le transform (roots environment (InternedFreeNameSemantics.lower names))
  intro term accepted
  obtain ⟨name, member, accepted⟩ := bound _ term accepted
  cases name with
  | inl token => exact accepted
  | inr name => exact ⟨name, (InternedFreeNameSemantics.lower_member names name).mpr member, accepted⟩

/-- Both binder forms retain support; a smart binder also lowers its pure root bound. -/
theorem related_binder (before after : Atom → Lang Symbol) (smart : Bool)
    (profile : Abstract (Sum Unit Atom)) (names : List (Sum Unit Atom))
    (left right : Lang Symbol → Lang Symbol)
    (body : ∀ leftCandidate rightCandidate,
      Related profile names (extend before leftCandidate) (extend after rightCandidate)
        (left leftCandidate) (right rightCandidate)) :
    Related (if smart then lower profile else none) (InternedFreeNameSemantics.lower names)
      before after (least left) (least right) := by
  refine ⟨?_, ?_, ?_⟩
  · cases smart with
    | false => trivial
    | true =>
        cases profile with
        | none => trivial
        | some names => exact lower_closed before names left (fun candidate => (body candidate candidate).upper_left)
  · cases smart with
    | false => trivial
    | true =>
        cases profile with
        | none => trivial
        | some names => exact lower_closed after names right (fun candidate => (body candidate candidate).upper_right)
  · intro agree
    apply BinderLanguage.least_congr
    intro candidate term
    apply iff_of_eq
    apply congrFun ((body candidate candidate).support ?_) term
    intro name member
    cases name with
    | inl token => rfl
    | inr name => exact agree name ((InternedFreeNameSemantics.lower_member names name).mpr member)

end MicroCFTA.InternedGuardedAbstractSupport
