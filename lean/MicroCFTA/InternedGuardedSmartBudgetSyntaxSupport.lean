import MicroCFTA.InternedGuardedSmartBudgetSupport
import MicroCFTA.InternedGuardedSyntaxSupport

/-!
# Complete lexical support for smart unfolding budgets

The existing depth shapes bound roots and ambient dependencies. An accepted
forest has no empty child shape. Deleted edges therefore contribute no
accepted term. Both smart binder branches retain the same support relation.
-/
namespace MicroCFTA.InternedGuardedSmartBudgetSupport
open Language InternedNestedConstruction
open InternedDepthSemantics (Shape)
open BinderBudgetLanguage (Lang)

/-- The shape interpreter retains one shape for each ordered source operand. -/
theorem shapes_many (expressions : List (Syntax Symbol Guard)) (shapes : List (Shape Atom)) :
    InternedDepthSemantics.evaluateMany expressions shapes = expressions.map (fun expression => InternedDepthSemantics.evaluate expression shapes) := by
  induction expressions with
  | nil => rw [InternedDepthSemantics.evaluateMany, List.map_nil]
  | cons first rest ih => rw [InternedDepthSemantics.evaluateMany, List.map_cons, ih]

/-- Combined shape free names come from exactly one original operand. -/
theorem combined_free (shapes : List (Shape Atom)) (name : Atom) :
    name ∈ (InternedDepthSemantics.combineMany shapes).free ↔ ∃ shape ∈ shapes, name ∈ shape.free := by
  induction shapes with
  | nil => simp [InternedDepthSemantics.combineMany, Shape.free]
  | cons first rest ih =>
      rw [InternedDepthSemantics.combineMany, InternedDepthFreeProjection.combine_member, ih]
      simp only [List.mem_cons, exists_eq_or_imp]

/-- A union's interpreted free names come from exactly one source operand. -/
theorem many_free (expressions : List (Syntax Symbol Guard)) (shapes : List (Shape Atom)) (name : Atom) :
    name ∈ (InternedDepthSemantics.combineMany (InternedDepthSemantics.evaluateMany expressions shapes)).free ↔
      ∃ expression ∈ expressions, name ∈ (InternedDepthSemantics.evaluate expression shapes).free := by
  rw [combined_free, shapes_many]
  constructor
  · rintro ⟨shape, member, named⟩
    obtain ⟨expression, present, rfl⟩ := List.mem_map.mp member
    exact ⟨expression, present, named⟩
  · rintro ⟨expression, present, named⟩
    exact ⟨_, List.mem_map.mpr ⟨expression, present, rfl⟩, named⟩

/-- A live edge places every interpreted child free name in its parent node shape. -/
theorem edge_free_parent (edges : List (EdgeSyntax Symbol Guard)) (shapes : List (Shape Atom))
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (member : EdgeSyntax.mk symbol guard children ∈ edges)
    (live : (InternedDepthSemantics.evaluateMany children shapes).any Shape.isEmpty = false)
    (child : Syntax Symbol Guard) (childIn : child ∈ children) (name : Atom)
    (named : name ∈ (InternedDepthSemantics.evaluate child shapes).free) :
    name ∈ (InternedDepthSemantics.evaluateEdges edges shapes).free := by
  induction edges with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · rw [InternedDepthSemantics.evaluateEdges, InternedDepthFreeProjection.combine_member]
        apply Or.inl
        simp only [InternedDepthSemantics.edge, live, Bool.false_eq_true, ↓reduceIte, Shape.free, List.nil_append]
        exact (many_free children shapes name).mpr ⟨child, childIn, named⟩
      · have tailNamed := ih member
        cases first with
        | mk s g c =>
            rw [InternedDepthSemantics.evaluateEdges, InternedDepthFreeProjection.combine_member]
            exact Or.inr tailNamed

/-- Equal child budget languages retain exactly the same ordered lexical forest. -/
theorem forest_congr (holds : Guard → Term Symbol → Bool) (shapes : List (Shape Atom))
    (before after : List (Lang Symbol)) (children : List (Syntax Symbol Guard))
    (same : ∀ child ∈ children, InternedGuardedSmartBudget.evaluate holds shapes before child = InternedGuardedSmartBudget.evaluate holds shapes after child)
    (budget : Nat) (terms : List (Term Symbol)) :
    InternedGuardedSmartBudget.forest holds shapes before budget children terms ↔
      InternedGuardedSmartBudget.forest holds shapes after budget children terms := by
  induction children generalizing terms with
  | nil => cases terms <;> simp only [InternedGuardedSmartBudget.forest]
  | cons child rest ih =>
      cases terms with
      | nil => simp only [InternedGuardedSmartBudget.forest]
      | cons term terms =>
          simp only [InternedGuardedSmartBudget.forest]
          exact and_congr (iff_of_eq (congrFun (congrFun (same child List.mem_cons_self) budget) term))
            (ih (fun child member => same child (List.mem_cons_of_mem _ member)) terms)

/-- An accepted lexical forest supplies a term for each original child at the common bound. -/
theorem forest_child (holds : Guard → Term Symbol → Bool) (shapes : List (Shape Atom)) (environment : List (Lang Symbol))
    (children : List (Syntax Symbol Guard)) (budget : Nat) (terms : List (Term Symbol))
    (accepted : InternedGuardedSmartBudget.forest holds shapes environment budget children terms)
    (child : Syntax Symbol Guard) (member : child ∈ children) :
    ∃ term, InternedGuardedSmartBudget.evaluate holds shapes environment child budget term := by
  induction children generalizing terms with
  | nil => cases member
  | cons first rest ih =>
      cases terms with
      | nil => simp only [InternedGuardedSmartBudget.forest] at accepted
      | cons term terms =>
          rw [InternedGuardedSmartBudget.forest] at accepted
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨term, accepted.1⟩
          · exact ih terms accepted.2 member

/-- An accepted root-bounded language cannot have an empty shape. -/
theorem accepted_nonempty (environment : Atom → Lang Symbol) (shape : Shape Atom) (language : Lang Symbol)
    (bound : Upper environment shape language) (budget : Nat) (term : Term Symbol) (accepted : language budget term) :
    shape.isEmpty = false := by
  apply Bool.eq_false_iff.mpr
  intro empty
  have fields : shape.hasOpaque = false ∧ shape.roots = [] := by simpa [Shape.isEmpty] using empty
  obtain ⟨name, member, _⟩ := bound fields.1 budget term accepted
  rw [fields.2] at member
  cases member

/-- An accepted forest uses only children retained by the existing shape analysis. -/
theorem forest_live (holds : Guard → Term Symbol → Bool) (shapes : List (Shape Atom)) (environment : List (Lang Symbol))
    (ambient : Atom → Lang Symbol) (children : List (Syntax Symbol Guard))
    (bounds : ∀ child ∈ children, Upper ambient (InternedDepthSemantics.evaluate child shapes)
      (InternedGuardedSmartBudget.evaluate holds shapes environment child))
    (budget : Nat) (terms : List (Term Symbol))
    (accepted : InternedGuardedSmartBudget.forest holds shapes environment budget children terms) :
    (InternedDepthSemantics.evaluateMany children shapes).any Shape.isEmpty = false := by
  apply Bool.eq_false_iff.mpr
  intro dead
  obtain ⟨shape, member, empty⟩ := List.any_eq_true.mp dead
  rw [shapes_many] at member
  obtain ⟨child, childIn, rfl⟩ := List.mem_map.mp member
  obtain ⟨term, accepted⟩ := forest_child holds shapes environment children budget terms accepted child childIn
  rw [accepted_nonempty ambient _ _ (bounds child childIn) budget term accepted] at empty
  cases empty

/-- An accepted complete lexical edge has a live interpreted child list. -/
theorem edge_live (holds : Guard → Term Symbol → Bool) (shapes : List (Shape Atom)) (environment : List (Lang Symbol))
    (ambient : Atom → Lang Symbol) (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (bounds : ∀ child ∈ children, Upper ambient (InternedDepthSemantics.evaluate child shapes)
      (InternedGuardedSmartBudget.evaluate holds shapes environment child)) (budget : Nat) (term : Term Symbol)
    (accepted : InternedGuardedSmartBudget.edgeMeaning holds shapes environment (.mk symbol guard children) budget term) :
    (InternedDepthSemantics.evaluateMany children shapes).any Shape.isEmpty = false := by
  rw [InternedGuardedSmartBudget.edgeMeaning] at accepted
  obtain ⟨terms, _, runs, _⟩ := accepted
  exact forest_live holds shapes environment ambient children bounds budget terms runs

/-- One live source edge makes the complete node shape opaque. -/
theorem node_live (edges : List (EdgeSyntax Symbol Guard)) (shapes : List (Shape Atom))
    (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
    (member : EdgeSyntax.mk symbol guard children ∈ edges)
    (live : (InternedDepthSemantics.evaluateMany children shapes).any Shape.isEmpty = false) :
    (InternedDepthSemantics.evaluateEdges edges shapes).hasOpaque = true := by
  induction edges with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [InternedDepthSemantics.evaluateEdges, InternedDepthSemantics.combine,
          InternedDepthSemantics.edge, live, Bool.false_eq_true, ↓reduceIte, Bool.true_or]
      · have tailLive := ih member
        cases first with
        | mk s g c =>
            simp only [InternedDepthSemantics.evaluateEdges, InternedDepthSemantics.combine, tailLive, Bool.or_true]

/-- A lexical node with no opaque alternative accepts no finite term. -/
theorem node_upper (holds : Guard → Term Symbol → Bool) (shapes : List (Shape Atom)) (environment : List (Lang Symbol))
    (ambient : Atom → Lang Symbol) (edges : List (EdgeSyntax Symbol Guard))
    (bounds : ∀ symbol guard children, EdgeSyntax.mk symbol guard children ∈ edges → ∀ child ∈ children,
      Upper ambient (InternedDepthSemantics.evaluate child shapes) (InternedGuardedSmartBudget.evaluate holds shapes environment child)) :
    Upper ambient (InternedDepthSemantics.evaluate (.node edges) shapes)
      (InternedGuardedSmartBudget.evaluate holds shapes environment (.node edges)) := by
  intro nonopaque budget term accepted
  rw [InternedGuardedSmartBudget.evaluate] at accepted
  obtain ⟨⟨edge, member⟩, accepted⟩ := accepted
  cases edge with
  | mk symbol guard children =>
      have live := edge_live holds shapes environment ambient symbol guard children (bounds symbol guard children member) budget term accepted
      have opaqueNode := node_live edges shapes symbol guard children member live
      simp only [InternedDepthSemantics.evaluate, opaqueNode, Bool.true_eq_false] at nonopaque

/-- Finite source alternatives retain each operand's interpreted root bound. -/
theorem alternatives_upper (ambient : Atom → Lang Symbol) (values : List Value)
    (shape : Value → Shape Atom) (language : Value → Lang Symbol)
    (bounds : ∀ value ∈ values, Upper ambient (shape value) (language value)) :
    Upper ambient (InternedDepthSemantics.combineMany (values.map shape))
      (fun budget term => ∃ value : {value // value ∈ values}, language value.val budget term) := by
  induction values with
  | nil =>
      intro _ budget term accepted
      obtain ⟨value, _⟩ := accepted
      cases value.property
  | cons first rest ih =>
      have combined := upper_combine ambient (shape first) (InternedDepthSemantics.combineMany (rest.map shape))
        (language first) (fun budget term => ∃ value : {value // value ∈ rest}, language value.val budget term)
        (bounds first List.mem_cons_self) (ih (fun value member => bounds value (List.mem_cons_of_mem _ member)))
      intro nonopaque budget term accepted
      apply combined nonopaque budget term
      obtain ⟨⟨value, member⟩, accepted⟩ := accepted
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl accepted
      · exact Or.inr ⟨⟨value, member⟩, accepted⟩

/-- Every lexical input has its stated root bound and complete ambient budget support. -/
def Inputs (shapes : List (Shape Atom)) (before after : Atom → Lang Symbol) (left right : List (Lang Symbol)) : Prop :=
  ∀ index : Nat, Related (shapes[index]?.getD {}) before after
    (left[index]?.getD (fun _ _ => False)) (right[index]?.getD (fun _ _ => False))

/-- Symbolic binder scope retains both the new local and each mapped captured input. -/
theorem inputs_binder (shapes : List (Shape Atom)) (before after : Atom → Lang Symbol) (left right : List (Lang Symbol))
    (inputs : Inputs shapes before after left right) (leftCandidate rightCandidate : Lang Symbol) :
    Inputs (⟨[Sum.inl ()], [], false, 0⟩ :: shapes.map (Shape.map Sum.inr))
      (extend before leftCandidate) (extend after rightCandidate) (leftCandidate :: left) (rightCandidate :: right) := by
  intro index
  cases index with
  | zero => exact related_local before after leftCandidate rightCandidate
  | succ index =>
      have lifted := related_lift before after leftCandidate rightCandidate _ _ _ (inputs index)
      have lookup := InternedGuardedSyntaxSupport.map_getD shapes (Shape.map (Sum.inr : Atom → Sum Unit Atom)) {} index
      have lookupEmpty : (shapes.map (Shape.map (Sum.inr : Atom → Sum Unit Atom)))[index]?.getD {} =
          (shapes[index]?.getD {}).map Sum.inr := by
        simpa only [Shape.map, List.map_nil] using lookup
      simpa only [List.getElem?_cons_succ, lookupEmpty] using lifted

/-- Complete lexical syntax satisfies the existing shapes' root and free-name budget bounds. -/
theorem evaluate_related {Atom : Type} (holds : Guard → Term Symbol → Bool) (expression : Syntax Symbol Guard)
    (shapes : List (Shape Atom)) (before after : Atom → Lang Symbol) (left right : List (Lang Symbol))
    (inputs : Inputs shapes before after left right) :
    Related (InternedDepthSemantics.evaluate expression shapes) before after
      (InternedGuardedSmartBudget.evaluate holds shapes left expression) (InternedGuardedSmartBudget.evaluate holds shapes right expression) := by
  cases expression with
  | empty => simpa only [InternedDepthSemantics.evaluate, InternedGuardedSmartBudget.evaluate] using related_empty before after
  | var index => simpa only [InternedDepthSemantics.evaluate, InternedGuardedSmartBudget.evaluate] using inputs index
  | union members =>
      have each (member : Syntax Symbol Guard) (present : member ∈ members) := by
        have smaller := List.sizeOf_lt_of_mem present
        exact evaluate_related holds member shapes before after left right inputs
      refine ⟨?_, ?_, ?_⟩
      · simpa only [InternedDepthSemantics.evaluate, shapes_many, InternedGuardedSmartBudget.evaluate] using
          alternatives_upper before members (fun member => InternedDepthSemantics.evaluate member shapes)
            (InternedGuardedSmartBudget.evaluate holds shapes left) (fun member present => (each member present).upper_left)
      · simpa only [InternedDepthSemantics.evaluate, shapes_many, InternedGuardedSmartBudget.evaluate] using
          alternatives_upper after members (fun member => InternedDepthSemantics.evaluate member shapes)
            (InternedGuardedSmartBudget.evaluate holds shapes right) (fun member present => (each member present).upper_right)
      · intro agree
        rw [InternedGuardedSmartBudget.evaluate, InternedGuardedSmartBudget.evaluate]
        funext budget term
        apply propext
        apply exists_congr
        intro member
        apply iff_of_eq
        apply congrFun
        apply congrFun ((each member.val member.property).support ?_)
        intro name named
        apply agree name
        rw [InternedDepthSemantics.evaluate]
        exact (many_free members shapes name).mpr ⟨member.val, member.property, named⟩
  | node edges =>
      have each (symbol : Symbol) (guard : Guard) (children : List (Syntax Symbol Guard))
          (edgeMember : EdgeSyntax.mk symbol guard children ∈ edges) (child : Syntax Symbol Guard) (childMember : child ∈ children) := by
        have edgeSmall := List.sizeOf_lt_of_mem edgeMember
        have childSmall := InternedGuardedSyntaxSupport.child_size symbol guard children child childMember
        exact evaluate_related holds child shapes before after left right inputs
      refine ⟨node_upper holds shapes left before edges (fun symbol guard children member child childMember =>
          (each symbol guard children member child childMember).upper_left),
        node_upper holds shapes right after edges (fun symbol guard children member child childMember =>
          (each symbol guard children member child childMember).upper_right), ?_⟩
      intro agree
      rw [InternedGuardedSmartBudget.evaluate, InternedGuardedSmartBudget.evaluate]
      funext budget term
      apply propext
      apply exists_congr
      intro edge
      rcases edge with ⟨edge, member⟩
      cases edge with
      | mk symbol guard children =>
          by_cases live : (InternedDepthSemantics.evaluateMany children shapes).any Shape.isEmpty = false
          · rw [InternedGuardedSmartBudget.edgeMeaning, InternedGuardedSmartBudget.edgeMeaning]
            apply exists_congr
            intro terms
            apply and_congr_right
            intro same
            apply and_congr_left
            intro guardHolds
            apply forest_congr holds shapes left right children ?_ budget terms
            intro child childMember
            apply (each symbol guard children member child childMember).support
            intro name named
            apply agree name
            rw [InternedDepthSemantics.evaluate]
            exact edge_free_parent edges shapes symbol guard children member live child childMember name named
          · constructor
            · intro accepted
              exact False.elim (live (edge_live holds shapes left before symbol guard children
                (fun child childMember => (each symbol guard children member child childMember).upper_left) budget term accepted))
            · intro accepted
              exact False.elim (live (edge_live holds shapes right after symbol guard children
                (fun child childMember => (each symbol guard children member child childMember).upper_right) budget term accepted))
  | binder smart body =>
      have bodyRelated (leftCandidate rightCandidate : Lang Symbol) :=
        evaluate_related holds body (⟨[Sum.inl ()], [], false, 0⟩ :: shapes.map (Shape.map Sum.inr))
          (extend before leftCandidate) (extend after rightCandidate) (leftCandidate :: left) (rightCandidate :: right)
          (inputs_binder shapes before after left right inputs leftCandidate rightCandidate)
      simpa only [InternedDepthSemantics.evaluate, InternedGuardedSmartBudget.evaluate] using
        related_binder before after smart _ _ _ bodyRelated
termination_by sizeOf expression
decreasing_by all_goals simp_wf; all_goals subst_vars; all_goals simp_wf; all_goals omega

end MicroCFTA.InternedGuardedSmartBudgetSupport
