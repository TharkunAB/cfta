import MicroCFTA.SourceSynthesisProgramBuildRolesGeneric
import MicroCFTA.InternedGuardedExecution

/-!
# Finite members of the original Type universe

The source binder accepts finite constructor and arrow terms built from its
declared alternatives. A generalized source variable uses this same binder.
The final law transfers membership to the same actual closed construction.
These laws do not supply joint application or filter equality constraints.
-/
namespace MicroCFTA.SourceSynthesisTypeUniverseMembership
open Language InternedConstructorTemplates
open InternedGuardedLanguage (Env)
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax (allTypes allTypesBody arrowType arrowMarker)
open SourceSynthesisGeneralizeSyntax (Guard top generalize)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges mapChildren_eq_map)

variable {Symbol : Type}

private theorem body_member (literal : String → Symbol)
    (holds : Guard → Term Symbol → Bool) (catalog : List (String × Nat))
    (expression : Syntax String Guard) (term : Term Symbol)
    (member : expression ∈ arrowType top (.var 0) (.var 0) ::
      (["var1", "var2", "var3", "var4"].map (fun name => .node [.mk name top []]) ++
        catalog.map (fun (name, arity) => .node [.mk name top (List.replicate arity (.var 0))])))
    (accepted : evaluate holds
      [evaluate holds [] (mapSyntax literal (allTypes top catalog))]
      (mapSyntax literal expression) term) :
    evaluate holds [] (mapSyntax literal (allTypes top catalog)) term := by
  let choices : List (Syntax String Guard) := arrowType top (.var 0) (.var 0) ::
      (["var1", "var2", "var3", "var4"].map (fun name => .node [.mk name top []]) ++
        catalog.map (fun (name, arity) => .node [.mk name top (List.replicate arity (.var 0))]))
  change evaluate holds [] (.binder true (.union (mapChildren literal choices))) term
  apply (InternedGuardedSyntax.binder_unfold holds [] true _ term).mpr
  rw [evaluate]
  refine ⟨⟨mapSyntax literal expression, ?_⟩, accepted⟩
  rw [mapChildren_eq_map]
  exact List.mem_map.mpr ⟨expression, member, rfl⟩

private theorem node_member (literal : String → Symbol)
    (holds : Guard → Term Symbol → Bool) (environment : List (BinderLanguage.Lang Symbol))
    (name : String) (children : List (Syntax String Guard)) (terms : List (Term Symbol))
    (accepted : forest holds environment (mapChildren literal children) terms)
    (guardHeld : holds top (.node (literal name) terms) = true) :
    evaluate holds environment (mapSyntax literal (.node [.mk name top children]))
      (.node (literal name) terms) := by
  simp only [mapSyntax, mapEdges]
  rw [evaluate]
  refine ⟨⟨.mk (literal name) top (mapChildren literal children), List.mem_cons_self⟩, ?_⟩
  rw [edgeMeaning]
  exact ⟨terms, rfl, accepted, guardHeld⟩

private theorem variables_forest (holds : Guard → Term Symbol → Bool)
    (language : BinderLanguage.Lang Symbol) (terms : List (Term Symbol))
    (accepted : ∀ term ∈ terms, language term) :
    forest holds [language] (List.replicate terms.length (.var 0)) terms := by
  induction terms with
  | nil => simp only [List.length_nil, List.replicate_zero, forest]
  | cons term terms ih =>
      rw [List.length_cons, List.replicate_succ, forest, evaluate]
      change language term ∧ forest holds [language] (List.replicate terms.length (.var 0)) terms
      exact ⟨accepted term List.mem_cons_self,
        ih (fun child member => accepted child (List.mem_cons_of_mem _ member))⟩

/-- Each of the four rigid variable alternatives is a finite universe member. -/
theorem variable_member (literal : String → Symbol) (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true) (catalog : List (String × Nat))
    (name : String) (present : name ∈ ["var1", "var2", "var3", "var4"]) :
    evaluate holds [] (mapSyntax literal (allTypes top catalog)) (.node (literal name) []) := by
  apply body_member literal holds catalog (.node [.mk name top []]) (.node (literal name) [])
  · exact List.mem_cons_of_mem _ (List.mem_append.mpr
      (Or.inl (List.mem_map.mpr ⟨name, present, rfl⟩)))
  · exact node_member literal holds _ name [] []
      (by simp only [mapChildren, forest]) (topHeld _)

/-- A declared constructor preserves finite membership of its ordered children. -/
theorem constructor_member (literal : String → Symbol) (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true) (catalog : List (String × Nat))
    (name : String) (children : List (Term Symbol))
    (present : (name, children.length) ∈ catalog)
    (accepted : ∀ child ∈ children,
      evaluate holds [] (mapSyntax literal (allTypes top catalog)) child) :
    evaluate holds [] (mapSyntax literal (allTypes top catalog))
      (.node (literal name) children) := by
  apply body_member literal holds catalog
    (.node [.mk name top (List.replicate children.length (.var 0))]) (.node (literal name) children)
  · exact List.mem_cons_of_mem _ (List.mem_append.mpr
      (Or.inr (List.mem_map.mpr ⟨(name, children.length), present, rfl⟩)))
  · apply node_member literal holds _ name (List.replicate children.length (.var 0)) children
    · simpa only [mapChildren_eq_map, List.map_replicate, mapSyntax] using
        variables_forest holds (evaluate holds [] (mapSyntax literal (allTypes top catalog))) children accepted
    · exact topHeld _

/-- The arrow alternative retains its marker, argument, and result in source order. -/
theorem arrow_member (literal : String → Symbol) (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true) (catalog : List (String × Nat))
    (argument result : Term Symbol)
    (argumentMember : evaluate holds [] (mapSyntax literal (allTypes top catalog)) argument)
    (resultMember : evaluate holds [] (mapSyntax literal (allTypes top catalog)) result) :
    evaluate holds [] (mapSyntax literal (allTypes top catalog))
      (.node (literal "->") [.node (literal "(->)") [], argument, result]) := by
  apply body_member literal holds catalog (arrowType top (.var 0) (.var 0))
    (.node (literal "->") [.node (literal "(->)") [], argument, result])
  · exact List.mem_cons_self
  · apply node_member literal holds _ "->" [arrowMarker top, .var 0, .var 0]
      [.node (literal "(->)") [], argument, result]
    · simp only [mapChildren, mapSyntax, forest]
      refine ⟨?_, ?_, ?_, True.intro⟩
      · exact node_member literal holds _ "(->)" [] []
          (by simp only [mapChildren, forest]) (topHeld _)
      · rw [evaluate]
        exact argumentMember
      · rw [evaluate]
        exact resultMember
    · exact topHeld _

/-- Generalization of any source variable keeps the supplied universe binder. -/
theorem generalize_variable_member (literal : String → Symbol)
    (holds : Guard → Term Symbol → Bool) (catalog : List (String × Nat))
    (name : String) (term : Term Symbol)
    (member : evaluate holds [] (mapSyntax literal (allTypes top catalog)) term) :
    evaluate holds [] (mapSyntax literal
      (generalize (allTypes top catalog) (.tVar name))) term := by
  simpa only [generalize, SourceSynthesisGeneralizeSyntax.replace, allTypes,
    SourceSynthesisGeneralizeSyntax.finish] using member

/-- The same closed build accepts every finite member supplied by the source laws. -/
theorem build_generalize_variable_member [DecidableEq (EdgeKey Symbol Guard)]
    (literal : String → Symbol) (holds : Guard → Term Symbol → Bool)
    (catalog : List (String × Nat)) (name : String) (term : Term Symbol)
    (member : evaluate holds [] (mapSyntax literal (allTypes top catalog)) term)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (done : InternedFreshOrdinaryConstruction.build (mapSyntax literal
      (generalize (allTypes top catalog) (.tVar name))) []
        InternedConstructorTemplates.empty = .done value heap)
    (ambient : Env Symbol) : InternedGuardedLanguage.meaning holds ambient value term := by
  rw [InternedGuardedExecution.closed_language _ value heap done holds ambient]
  exact generalize_variable_member literal holds catalog name term member

end MicroCFTA.SourceSynthesisTypeUniverseMembership
