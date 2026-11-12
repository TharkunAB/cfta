import MicroCFTA.SourceSynthesisFiniteTypeWitnesses

/-!
# Exact finite membership of the source type universe

The structural TypeIn judgment is the least language of allTypes.
Catalog entries may repeat or overlap variable and arrow symbols.
The proof uses the existing guarded syntax semantics.
It does not assert raw type eligibility or native construction behavior.
-/
namespace MicroCFTA.SourceSynthesisTypeUniverseExact
open Language
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax (Expr allTypes allTypesBody arrowType arrowMarker)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
open SourceSynthesisProgramBuildRolesGeneric
  (mapSyntax mapChildren mapEdges mapChildren_eq_map)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

private theorem node_children (holds : Guard → Term Symbol → Bool)
    (environment : List (BinderLanguage.Lang Symbol)) (name : String)
    (children : List (Expr Guard)) (term : Term Symbol)
    (accepted : evaluate holds environment
      (mapSyntax literal (.node [.mk name top children])) term) :
    ∃ terms, term = .node (literal name) terms ∧
      forest holds environment (mapChildren literal children) terms := by
  simp only [mapSyntax, mapEdges] at accepted
  rw [evaluate] at accepted
  obtain ⟨⟨edge, member⟩, checked⟩ := accepted
  have same := List.mem_singleton.mp member
  subst edge
  rw [edgeMeaning] at checked
  obtain ⟨terms, shape, childrenAccepted, _guardHeld⟩ := checked
  exact ⟨terms, shape, childrenAccepted⟩

private theorem leaf_term (holds : Guard → Term Symbol → Bool)
    (language : BinderLanguage.Lang Symbol) (name : String) (term : Term Symbol)
    (accepted : evaluate holds [language]
      (mapSyntax literal (.node [.mk name top []])) term) :
    term = .node (literal name) [] := by
  obtain ⟨terms, shape, checked⟩ := node_children holds [language] name [] term accepted
  cases terms with
  | nil => exact shape
  | cons first rest => simp only [mapChildren, forest] at checked

private theorem replicate_children (holds : Guard → Term Symbol → Bool)
    (catalog : List (String × Nat)) (count : Nat) (terms : List (Term Symbol))
    (accepted : forest holds [TypeIn catalog] (List.replicate count (.var 0)) terms) :
    terms.length = count ∧ ∀ term ∈ terms, TypeIn catalog term := by
  induction count generalizing terms with
  | zero =>
      cases terms with
      | nil => exact ⟨rfl, by intro term member; cases member⟩
      | cons first rest => simp only [List.replicate_zero, forest] at accepted
  | succ count ih =>
      cases terms with
      | nil => simp only [List.replicate_succ, forest] at accepted
      | cons term terms =>
          rw [List.replicate_succ, forest] at accepted
          have own := accepted.1
          rw [evaluate] at own
          obtain ⟨length, children⟩ := ih terms accepted.2
          refine ⟨by simp only [List.length_cons, length], ?_⟩
          intro child member
          rcases List.mem_cons.mp member with rfl | later
          · exact own
          · exact children child later

private theorem arrow_closed (holds : Guard → Term Symbol → Bool)
    (catalog : List (String × Nat)) (term : Term Symbol)
    (accepted : evaluate holds [TypeIn catalog]
      (mapSyntax literal (arrowType top (.var 0) (.var 0))) term) :
    TypeIn catalog term := by
  obtain ⟨terms, shape, checked⟩ := node_children holds [TypeIn catalog] "->"
    [arrowMarker top, .var 0, .var 0] term (by simpa only [arrowType] using accepted)
  rcases terms with _ | ⟨marker, _ | ⟨argument, _ | ⟨result, _ | ⟨_, _⟩⟩⟩⟩ <;>
    simp only [mapChildren, forest, and_false] at checked
  have markerShape := leaf_term holds (TypeIn catalog) "(->)" marker
    (by simpa only [arrowMarker] using checked.1)
  have first := checked.2.1
  have second := checked.2.2.1
  rw [mapSyntax, evaluate] at first second
  rw [shape, markerShape]
  exact TypeIn.arrow argument result first second

private theorem body_closed (holds : Guard → Term Symbol → Bool)
    (catalog : List (String × Nat)) :
    BinderLanguage.Included
      (evaluate holds [TypeIn catalog] (mapSyntax literal (allTypesBody top catalog)))
      (TypeIn catalog) := by
  intro term accepted
  simp only [allTypesBody, mapSyntax] at accepted
  rw [evaluate] at accepted
  obtain ⟨⟨expression, selected⟩, checked⟩ := accepted
  rw [mapChildren_eq_map] at selected
  obtain ⟨choice, member, rfl⟩ := List.mem_map.mp selected
  change choice ∈ arrowType top (.var 0) (.var 0) ::
    (["var1", "var2", "var3", "var4"].map (fun name => .node [.mk name top []]) ++
      catalog.map (fun (name, arity) => .node [.mk name top (List.replicate arity (.var 0))]))
    at member
  rcases List.mem_cons.mp member with rfl | later
  · exact arrow_closed holds catalog term checked
  · rcases List.mem_append.mp later with rigidRow | catalogRow
    · obtain ⟨name, present, rfl⟩ := List.mem_map.mp rigidRow
      rw [leaf_term holds (TypeIn catalog) name term checked]
      exact TypeIn.leaf name present
    · obtain ⟨⟨name, arity⟩, present, rfl⟩ := List.mem_map.mp catalogRow
      obtain ⟨terms, shape, children⟩ := node_children holds [TypeIn catalog] name
        (List.replicate arity (.var 0)) term checked
      have replicated : forest holds [TypeIn catalog] (List.replicate arity (.var 0)) terms := by
        simpa only [mapChildren_eq_map, List.map_replicate, mapSyntax] using children
      obtain ⟨length, admitted⟩ := replicate_children holds catalog arity terms replicated
      rw [shape]
      exact TypeIn.node name terms (by simpa only [length] using present) admitted

/-- The source universe accepts exactly its structural TypeIn witnesses. -/
theorem allTypes_member_iff_TypeIn (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true)
    (catalog : List (String × Nat)) (term : Term Symbol) :
    evaluate holds [] (mapSyntax literal (allTypes top catalog)) term ↔
      TypeIn catalog term := by
  constructor
  · intro accepted
    rw [allTypes, mapSyntax, evaluate] at accepted
    exact BinderLanguage.least_le
      (fun language => evaluate holds [language] (mapSyntax literal (allTypesBody top catalog)))
      (TypeIn catalog) (body_closed holds catalog) term accepted
  · intro admitted
    exact TypeIn.member holds topHeld admitted

end MicroCFTA.SourceSynthesisTypeUniverseExact
