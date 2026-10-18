import MicroCFTA.SourceCurrentScopedProfileInputs

/-!
# Root deletion tests on live source support

Only live fixed names and varying labels constrain the cut predicates.
Binder extension adds its local reference to both deletion predicates.
The local alias tests preserve captured decisions for both binder forms.
Unused captures and dead source rows require no freshness condition.
-/
namespace MicroCFTA.SourceCurrentScopedDeletionInputs
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreshOrdinaryLiveInputs (inputProfile liftInput)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open InternedBinderProtocol (Reference)

variable {Atom : Type}

/-- Live fixed names and paired varying names have equal deletion tests. -/
def Compatible (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Reference → Bool) : Prop :=
  (∀ name, .inl name ∈ support expression inputs → first name = second name) ∧
    ∀ atom, .inr atom ∈ support expression inputs → first (firstNames atom) = second (secondNames atom)

/-- A selected variable constrains only its fixed free names or its varying label. -/
theorem variable_input (index : Nat) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Reference → Bool)
    (compatible : Compatible (.var index) inputs firstNames secondNames first second)
    (selected : Sum (Value Symbol Guard) Atom) (found : inputs[index]? = some selected) :
    match selected with
    | .inl value => ∀ name ∈ value.free, first name = second name
    | .inr atom => first (firstNames atom) = second (secondNames atom) := by
  cases selected with
  | inl value =>
      intro name member
      apply compatible.1 name
      simpa only [support,InternedFreeNameSemantics.evaluate,List.getElem?_map,found,
        Option.map_some,Option.getD_some,inputNames] using List.mem_map.mpr ⟨name,member,rfl⟩
  | inr atom =>
      apply compatible.2 atom
      simp only [support,InternedFreeNameSemantics.evaluate,List.getElem?_map,found,
        Option.map_some,Option.getD_some,inputNames,List.mem_singleton]

/-- Each original union member inherits the parent's live deletion tests. -/
theorem union_member (members : List (Syntax Symbol Guard)) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Reference → Bool)
    (compatible : Compatible (.union members) inputs firstNames secondNames first second)
    (member : Syntax Symbol Guard) (present : member ∈ members) :
    Compatible member inputs firstNames secondNames first second := by
  have included (label : Sum Reference Atom) (live : label ∈ support member inputs) :
      label ∈ support (.union members) inputs := by
    unfold support at live ⊢
    rw [InternedFreeNameSemantics.evaluate]
    exact (InternedFreeNameSemantics.evaluateMany_member members (inputs.map inputProfile)
      (inputs.map inputNames) label).mpr ⟨member,present,live⟩
  exact ⟨fun name live => compatible.1 name (included _ live),
    fun atom live => compatible.2 atom (included _ live)⟩

/-- A child of an original live node row inherits the parent's deletion tests. -/
theorem node_child (rows : List (EdgeSyntax Symbol Guard)) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Reference → Bool)
    (compatible : Compatible (.node rows) inputs firstNames secondNames first second)
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (row : EdgeSyntax.mk symbol guard children ∈ rows)
    (live : (InternedProfileSemantics.evaluateMany children (inputs.map inputProfile)).all
      (fun child => !InternedProfileSemantics.isEmpty child) = true)
    (child : Syntax Symbol Guard) (present : child ∈ children) :
    Compatible child inputs firstNames secondNames first second := by
  have included (label : Sum Reference Atom) (member : label ∈ support child inputs) :
      label ∈ support (.node rows) inputs := by
    unfold support at member ⊢
    rw [InternedFreeNameSemantics.evaluate]
    exact (InternedFreeNameSemantics.evaluateEdges_member rows (inputs.map inputProfile)
      (inputs.map inputNames) label).mpr ⟨symbol,guard,children,row,live,child,present,member⟩
  exact ⟨fun name member => compatible.1 name (included _ member),
    fun atom member => compatible.2 atom (included _ member)⟩

/-- Equal live local aliases preserve combined cuts for either binder form. -/
theorem extend (smart : Bool) (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (first second : Reference → Bool)
    (compatible : Compatible (.binder smart body) inputs firstNames secondNames first second)
    (firstArgument secondArgument : Reference)
    (aliases : ∀ label ∈ support (.binder smart body) inputs,
      Sum.elim id firstNames label = firstArgument ↔ Sum.elim id secondNames label = secondArgument) :
    Compatible body (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ => firstArgument) firstNames) (Sum.elim (fun _ => secondArgument) secondNames)
      (fun name => first name || (name == firstArgument))
      (fun name => second name || (name == secondArgument)) := by
  constructor
  · intro name member
    have captured : .inl name ∈ support (.binder smart body) inputs := by
      simpa only [support,InternedFreeNameSemantics.evaluate] using
        (SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inl name)).mp member
    have alias := aliases (.inl name) captured
    change name = firstArgument ↔ name = secondArgument at alias
    change (first name || (name == firstArgument)) = (second name || (name == secondArgument))
    rw [compatible.1 name captured]
    exact congrArg (fun test => second name || test)
      (Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using alias))
  · intro atom member
    cases atom with
    | inl token => simp only [Sum.elim_inl,beq_self_eq_true,Bool.or_true]
    | inr atom =>
        have captured : .inr atom ∈ support (.binder smart body) inputs := by
          simpa only [support,InternedFreeNameSemantics.evaluate] using
            (SourceCurrentNativeNormalizedComparison.capture_support body inputs (.inr atom)).mp member
        have alias := aliases (.inr atom) captured
        change firstNames atom = firstArgument ↔ secondNames atom = secondArgument at alias
        change (first (firstNames atom) || (firstNames atom == firstArgument)) =
          (second (secondNames atom) || (secondNames atom == secondArgument))
        rw [compatible.2 atom captured]
        exact congrArg (fun test => second (secondNames atom) || test)
          (Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq] using alias))

/-- Equal live local aliases make the two singleton local cuts compatible. -/
theorem local_cuts (smart : Bool) (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstArgument secondArgument : Reference)
    (aliases : ∀ label ∈ support (.binder smart body) inputs,
      Sum.elim id firstNames label = firstArgument ↔ Sum.elim id secondNames label = secondArgument) :
    Compatible body (.inr (.inl ()) :: inputs.map liftInput)
      (Sum.elim (fun _ => firstArgument) firstNames) (Sum.elim (fun _ => secondArgument) secondNames)
      (fun name => name == firstArgument) (fun name => name == secondArgument) := by
  simpa only [Bool.false_or] using extend smart body inputs firstNames secondNames
    (fun _ => false) (fun _ => false) ⟨fun _ _ => rfl,fun _ _ => rfl⟩ firstArgument secondArgument aliases

end MicroCFTA.SourceCurrentScopedDeletionInputs
