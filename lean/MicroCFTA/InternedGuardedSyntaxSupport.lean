import MicroCFTA.InternedGuardedAbstractSupport

/-!
# Semantic support of complete lexical source syntax

The existing profile analysis bounds root languages. The existing free-name
analysis bounds ambient dependencies. Empty-child filtering can remove
dependencies because an empty profile cannot accept any finite term.
-/
namespace MicroCFTA.InternedGuardedSyntaxSupport
open Language InternedNestedConstruction
open BinderLanguage (Lang Included)
open InternedGuardedAbstractSupport

/-- The profile interpreter retains one result for each source operand. -/
theorem profiles_many (expressions : List (Syntax Symbol Guard)) (profiles : List (InternedProfileSemantics.Abstract Atom)) :
    InternedProfileSemantics.evaluateMany expressions profiles = expressions.map (fun expression => InternedProfileSemantics.evaluate expression profiles) := by
  induction expressions with
  | nil => rw [InternedProfileSemantics.evaluateMany]; rfl
  | cons first rest ih => rw [InternedProfileSemantics.evaluateMany, List.map_cons, ih]

/-- The free-name interpreter retains one result for each source operand. -/
theorem names_many (expressions : List (Syntax Symbol Guard)) (profiles : List (InternedProfileSemantics.Abstract Atom)) (names : List (List Atom)) :
    InternedFreeNameSemantics.evaluateMany expressions profiles names = expressions.map (fun expression => InternedFreeNameSemantics.evaluate expression profiles names) := by
  induction expressions with
  | nil => rw [InternedFreeNameSemantics.evaluateMany]; rfl
  | cons first rest ih => rw [InternedFreeNameSemantics.evaluateMany, List.map_cons, ih]

/-- Equal child languages give the same complete ordered source forest. -/
theorem forest_congr (holds : Guard → Term Symbol → Bool) (before after : List (Lang Symbol))
    (children : List (Syntax Symbol Guard))
    (same : ∀ child ∈ children, InternedGuardedSyntax.evaluate holds before child = InternedGuardedSyntax.evaluate holds after child)
    (terms : List (Term Symbol)) : InternedGuardedSyntax.forest holds before children terms ↔ InternedGuardedSyntax.forest holds after children terms := by
  induction children generalizing terms with
  | nil => cases terms <;> simp only [InternedGuardedSyntax.forest]
  | cons child rest ih =>
      cases terms with
      | nil => simp only [InternedGuardedSyntax.forest]
      | cons term terms =>
          simp only [InternedGuardedSyntax.forest]
          exact and_congr (iff_of_eq (congrFun (same child List.mem_cons_self) term))
            (ih (fun child member => same child (List.mem_cons_of_mem _ member)) terms)

/-- An accepted forest supplies an accepted term for each source child. -/
theorem forest_child (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol))
    (children : List (Syntax Symbol Guard)) (terms : List (Term Symbol))
    (accepted : InternedGuardedSyntax.forest holds environment children terms) (child : Syntax Symbol Guard) (member : child ∈ children) :
    ∃ term, InternedGuardedSyntax.evaluate holds environment child term := by
  induction children generalizing terms with
  | nil => cases member
  | cons first rest ih =>
      cases terms with
      | nil => simp only [InternedGuardedSyntax.forest] at accepted
      | cons term terms =>
          rw [InternedGuardedSyntax.forest] at accepted
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨term, accepted.1⟩
          · exact ih terms accepted.2 member

/-- An accepted forest has no child with a pure empty profile. -/
theorem forest_live (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol))
    (ambient : Atom → Lang Symbol) (profiles : List (InternedProfileSemantics.Abstract Atom))
    (children : List (Syntax Symbol Guard))
    (bounds : ∀ child ∈ children, Upper ambient (InternedProfileSemantics.evaluate child profiles) (InternedGuardedSyntax.evaluate holds environment child))
    (terms : List (Term Symbol)) (accepted : InternedGuardedSyntax.forest holds environment children terms) :
    (InternedProfileSemantics.evaluateMany children profiles).all (fun child => !InternedProfileSemantics.isEmpty child) = true := by
  rw [profiles_many, List.all_map, List.all_eq_true]
  intro child member
  obtain ⟨term, accepted⟩ := forest_child holds environment children terms accepted child member
  have bound := bounds child member
  cases profile : InternedProfileSemantics.evaluate child profiles with
  | none => simp only [Function.comp_apply, profile, InternedProfileSemantics.isEmpty, Bool.not_false]
  | some names =>
      cases names with
      | nil =>
          rw [profile] at bound
          obtain ⟨name, impossible, _⟩ := bound term accepted
          cases impossible
      | cons name rest => simp only [Function.comp_apply, profile, InternedProfileSemantics.isEmpty, Bool.not_false]

/-- An accepted edge supplies the live-edge witness used by the profile analysis. -/
theorem edge_live (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol))
    (ambient : Atom → Lang Symbol) (profiles : List (InternedProfileSemantics.Abstract Atom))
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (bounds : ∀ child ∈ children, Upper ambient (InternedProfileSemantics.evaluate child profiles) (InternedGuardedSyntax.evaluate holds environment child))
    (term : Term Symbol) (accepted : InternedGuardedSyntax.edgeMeaning holds environment (.mk symbol guard children) term) :
    (InternedProfileSemantics.evaluateMany children profiles).all (fun child => !InternedProfileSemantics.isEmpty child) = true := by
  rw [InternedGuardedSyntax.edgeMeaning] at accepted
  obtain ⟨terms, _, runs, _⟩ := accepted
  exact forest_live holds environment ambient profiles children bounds terms runs

/-- A live source edge makes the complete node profile opaque. -/
theorem node_live (edges : List (EdgeSyntax Symbol Guard)) (profiles : List (InternedProfileSemantics.Abstract Atom))
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (member : EdgeSyntax.mk symbol guard children ∈ edges)
    (live : (InternedProfileSemantics.evaluateMany children profiles).all (fun child => !InternedProfileSemantics.isEmpty child) = true) :
    InternedProfileSemantics.evaluateEdges edges profiles = true := by
  induction edges with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [InternedProfileSemantics.evaluateEdges, live, Bool.true_or]
      · have tailLive := ih member
        cases first with
        | mk s g c => simp only [InternedProfileSemantics.evaluateEdges, tailLive, Bool.or_true]

/-- Finite unions retain every operand's root-language bound. -/
theorem alternatives_upper (environment : Atom → Lang Symbol) (values : List Value)
    (profile : Value → InternedProfileSemantics.Abstract Atom) (language : Value → Lang Symbol)
    (bounds : ∀ value ∈ values, Upper environment (profile value) (language value)) :
    Upper environment (InternedProfileSemantics.combineMany (values.map profile))
      (fun term => ∃ value : {value // value ∈ values}, language value.val term) := by
  induction values with
  | nil =>
      intro term accepted
      obtain ⟨value, _⟩ := accepted
      cases value.property
  | cons first rest ih =>
      have combined := upper_combine environment (profile first) (InternedProfileSemantics.combineMany (rest.map profile))
        (language first) (fun term => ∃ value : {value // value ∈ rest}, language value.val term)
        (bounds first List.mem_cons_self) (ih (fun value member => bounds value (List.mem_cons_of_mem _ member)))
      have same : (fun term => ∃ value : {value // value ∈ first :: rest}, language value.val term) =
          (fun term => language first term ∨ ∃ value : {value // value ∈ rest}, language value.val term) := by
        funext term
        apply propext
        constructor
        · rintro ⟨⟨value, member⟩, accepted⟩
          rcases List.mem_cons.mp member with rfl | member
          · exact Or.inl accepted
          · exact Or.inr ⟨⟨value, member⟩, accepted⟩
        · rintro (accepted | ⟨⟨value, member⟩, accepted⟩)
          · exact ⟨⟨first, List.mem_cons_self⟩, accepted⟩
          · exact ⟨⟨value, List.mem_cons_of_mem _ member⟩, accepted⟩
      simpa only [List.map_cons, InternedProfileSemantics.combineMany, same] using combined


/-- Source edge children are structurally smaller than their complete edge. -/
theorem child_size (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (child : Syntax Symbol Guard) (member : child ∈ children) :
    sizeOf child < sizeOf (EdgeSyntax.mk symbol guard children) := by
  have smaller := List.sizeOf_lt_of_mem member
  simp_wf
  omega

/-- A node with a pure profile cannot accept a term. -/
theorem node_upper (holds : Guard → Term Symbol → Bool) (environment : List (Lang Symbol))
    (ambient : Atom → Lang Symbol) (profiles : List (InternedProfileSemantics.Abstract Atom))
    (edges : List (EdgeSyntax Symbol Guard))
    (bounds : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ edges →
      ∀ child ∈ children, Upper ambient (InternedProfileSemantics.evaluate child profiles) (InternedGuardedSyntax.evaluate holds environment child)) :
    Upper ambient (InternedProfileSemantics.evaluate (.node edges) profiles) (InternedGuardedSyntax.evaluate holds environment (.node edges)) := by
  rw [InternedProfileSemantics.evaluate]
  cases live : InternedProfileSemantics.evaluateEdges edges profiles with
  | true => trivial
  | false =>
      rw [InternedGuardedSyntax.evaluate]
      rintro term ⟨⟨edge, member⟩, accepted⟩
      cases edge with
      | mk symbol guard children =>
          have edgeLive := edge_live holds environment ambient profiles symbol guard children
            (bounds symbol guard children member) term accepted
          have allLive := node_live edges profiles symbol guard children member edgeLive
          simp only [allLive, Bool.true_eq_false] at live

/-- Equal child languages retain each full source guard and symbol. -/
theorem edge_congr (holds : Guard → Term Symbol → Bool) (before after : List (Lang Symbol))
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (same : ∀ child ∈ children, InternedGuardedSyntax.evaluate holds before child = InternedGuardedSyntax.evaluate holds after child) :
    InternedGuardedSyntax.edgeMeaning holds before (.mk symbol guard children) = InternedGuardedSyntax.edgeMeaning holds after (.mk symbol guard children) := by
  funext term
  simp only [InternedGuardedSyntax.edgeMeaning]
  apply propext
  exact exists_congr (fun terms => and_congr Iff.rfl (and_congr (forest_congr holds before after children same terms) Iff.rfl))

/-- Every lexical input has the root bound and support required by the analyses. -/
def Inputs (profiles : List (InternedProfileSemantics.Abstract Atom)) (names : List (List Atom))
    (before after : Atom → Lang Symbol) (left right : List (Lang Symbol)) : Prop :=
  ∀ index : Nat, Related (profiles[index]?.getD (some [])) (names[index]?.getD []) before after
    (left[index]?.getD (fun _ => False)) (right[index]?.getD (fun _ => False))

/-- Mapping a lexical input list also maps its default value. -/
theorem map_getD (values : List Value) (function : Value → Other) (default : Value) (index : Nat) :
    (values.map function)[index]?.getD (function default) = function (values[index]?.getD default) := by
  cases found : values[index]? <;> simp only [List.getElem?_map, found, Option.map_none,
    Option.map_some, Option.getD_none, Option.getD_some]

/-- Extending lexical scope retains the relation for both the new local and all captures. -/
theorem inputs_binder (profiles : List (InternedProfileSemantics.Abstract Atom)) (names : List (List Atom))
    (before after : Atom → Lang Symbol) (left right : List (Lang Symbol))
    (inputs : Inputs profiles names before after left right) (leftCandidate rightCandidate : Lang Symbol) :
    Inputs (some [Sum.inl ()] :: profiles.map (InternedProfileSemantics.mapNames Sum.inr))
      ([Sum.inl ()] :: names.map (List.map Sum.inr))
      (extend before leftCandidate) (extend after rightCandidate) (leftCandidate :: left) (rightCandidate :: right) := by
  intro index
  cases index with
  | zero => exact related_local before after leftCandidate rightCandidate
  | succ index =>
      have lifted := related_lift before after leftCandidate rightCandidate _ _ _ _ (inputs index)
      have profileLookup : (profiles.map (InternedProfileSemantics.mapNames (Sum.inr : Atom → Sum Unit Atom)))[index]?.getD (some []) =
          InternedProfileSemantics.mapNames (Sum.inr : Atom → Sum Unit Atom) (profiles[index]?.getD (some [])) :=
        map_getD profiles (InternedProfileSemantics.mapNames (Sum.inr : Atom → Sum Unit Atom)) (some []) index
      have namesLookup : (names.map (List.map (Sum.inr : Atom → Sum Unit Atom)))[index]?.getD [] =
          (names[index]?.getD []).map (Sum.inr : Atom → Sum Unit Atom) := map_getD names (List.map (Sum.inr : Atom → Sum Unit Atom)) [] index
      simpa only [List.getElem?_cons_succ, profileLookup, namesLookup] using lifted

/-- Complete lexical syntax satisfies the existing root-profile and free-name analyses. -/
theorem evaluate_related {Atom : Type} (holds : Guard → Term Symbol → Bool) (expression : Syntax Symbol Guard)
    (profiles : List (InternedProfileSemantics.Abstract Atom)) (names : List (List Atom))
    (before after : Atom → Lang Symbol) (left right : List (Lang Symbol))
    (inputs : Inputs profiles names before after left right) :
    Related (InternedProfileSemantics.evaluate expression profiles) (InternedFreeNameSemantics.evaluate expression profiles names) before after
      (InternedGuardedSyntax.evaluate holds left expression) (InternedGuardedSyntax.evaluate holds right expression) := by
  cases expression with
  | empty =>
      simpa only [InternedProfileSemantics.evaluate, InternedFreeNameSemantics.evaluate, InternedGuardedSyntax.evaluate] using related_empty before after
  | var index => simpa only [InternedProfileSemantics.evaluate, InternedFreeNameSemantics.evaluate, InternedGuardedSyntax.evaluate] using inputs index
  | union members =>
      have each (member : Syntax Symbol Guard) (present : member ∈ members) := by
        have smaller := List.sizeOf_lt_of_mem present
        exact evaluate_related holds member profiles names before after left right inputs
      refine ⟨?_, ?_, ?_⟩
      · simpa only [InternedProfileSemantics.evaluate, profiles_many, InternedGuardedSyntax.evaluate] using
          alternatives_upper before members (fun member => InternedProfileSemantics.evaluate member profiles) (InternedGuardedSyntax.evaluate holds left)
            (fun member present => (each member present).upper_left)
      · simpa only [InternedProfileSemantics.evaluate, profiles_many, InternedGuardedSyntax.evaluate] using
          alternatives_upper after members (fun member => InternedProfileSemantics.evaluate member profiles) (InternedGuardedSyntax.evaluate holds right)
            (fun member present => (each member present).upper_right)
      · intro agree
        rw [InternedFreeNameSemantics.evaluate] at agree
        rw [InternedGuardedSyntax.evaluate, InternedGuardedSyntax.evaluate]
        funext term
        apply propext
        apply exists_congr
        intro member
        apply iff_of_eq
        apply congrFun ((each member.val member.property).support ?_) term
        intro name present
        exact agree name ((InternedFreeNameSemantics.evaluateMany_member members profiles names name).mpr ⟨member.val, member.property, present⟩)
  | node edges =>
      have each (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
          (edgeMember : EdgeSyntax.mk symbol guard children ∈ edges)
          (child : Syntax Symbol Guard) (childMember : child ∈ children) := by
        have edgeSmall := List.sizeOf_lt_of_mem edgeMember
        have childSmall := child_size symbol guard children child childMember
        exact evaluate_related holds child profiles names before after left right inputs
      refine ⟨node_upper holds left before profiles edges (fun symbol guard children member child childMember =>
          (each symbol guard children member child childMember).upper_left),
        node_upper holds right after profiles edges (fun symbol guard children member child childMember =>
          (each symbol guard children member child childMember).upper_right), ?_⟩
      intro agree
      rw [InternedFreeNameSemantics.evaluate] at agree
      rw [InternedGuardedSyntax.evaluate, InternedGuardedSyntax.evaluate]
      funext term
      apply propext
      apply exists_congr
      intro edge
      rcases edge with ⟨edge, member⟩
      cases edge with
      | mk symbol guard children =>
          by_cases live : (InternedProfileSemantics.evaluateMany children profiles).all (fun child => !InternedProfileSemantics.isEmpty child) = true
          · apply iff_of_eq
            apply congrFun (edge_congr holds left right symbol guard children ?_) term
            intro child childMember
            apply (each symbol guard children member child childMember).support
            intro name present
            exact agree name ((InternedFreeNameSemantics.evaluateEdges_member edges profiles names name).mpr
              ⟨symbol, guard, children, member, live, child, childMember, present⟩)
          · constructor
            · intro accepted
              exact False.elim (live (edge_live holds left before profiles symbol guard children
                (fun child childMember => (each symbol guard children member child childMember).upper_left) term accepted))
            · intro accepted
              exact False.elim (live (edge_live holds right after profiles symbol guard children
                (fun child childMember => (each symbol guard children member child childMember).upper_right) term accepted))
  | binder smart body =>
      have bodyRelated (leftCandidate rightCandidate : Lang Symbol) :=
        evaluate_related holds body (some [Sum.inl ()] :: profiles.map (InternedProfileSemantics.mapNames Sum.inr))
          ([Sum.inl ()] :: names.map (List.map Sum.inr))
          (extend before leftCandidate) (extend after rightCandidate)
          (leftCandidate :: left) (rightCandidate :: right)
          (inputs_binder profiles names before after left right inputs leftCandidate rightCandidate)
      have result := related_binder before after smart _ _
        (fun language => InternedGuardedSyntax.evaluate holds (language :: left) body)
        (fun language => InternedGuardedSyntax.evaluate holds (language :: right) body) bodyRelated
      cases smart <;> simpa only [InternedProfileSemantics.evaluate, InternedFreeNameSemantics.evaluate, InternedGuardedSyntax.evaluate, Bool.false_eq_true,
        Bool.true_eq, ↓reduceIte] using result
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end MicroCFTA.InternedGuardedSyntaxSupport
