import MicroCFTA.InternedGuardedRequest
import MicroCFTA.InternedShallowValues

/-!
# Ordered language transport for actual source constructor lists

Equal ordered child languages give equal guarded forests. Actual edge
allocation retains its complete requested key and canonical child values.
These laws retain source guards and source order through cache hits.
-/
namespace MicroCFTA.InternedGuardedExecutionLists
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (Env meaning)
open BinderLanguage (Lang)

/-- Equal ordered language lists have equal alternative languages. -/
theorem alternatives_equal (values : List Item) (expressions : List Expression)
    (left : Item → Lang Symbol) (right : Expression → Lang Symbol)
    (mapped : values.map left = expressions.map right) (term : Term Symbol) :
    (∃ value ∈ values, left value term) ↔ ∃ expression ∈ expressions, right expression term := by
  constructor
  · rintro ⟨value, member, accepted⟩
    have present : left value ∈ expressions.map right := mapped ▸ List.mem_map.mpr ⟨value, member, rfl⟩
    obtain ⟨expression, member, same⟩ := List.mem_map.mp present
    exact ⟨expression, member, same.symm ▸ accepted⟩
  · rintro ⟨expression, member, accepted⟩
    have present : right expression ∈ values.map left := mapped.symm ▸ List.mem_map.mpr ⟨expression, member, rfl⟩
    obtain ⟨value, member, same⟩ := List.mem_map.mp present
    exact ⟨value, member, same.symm ▸ accepted⟩

/-- Equal ordered language lists retain the exact source child forest. -/
theorem forest_equal (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) (environment : List (Lang Symbol))
    (values : List (Value Symbol Guard)) (expressions : List (Syntax Symbol Guard))
    (mapped : values.map (meaning holds ambient) = expressions.map (InternedGuardedSyntax.evaluate holds environment))
    (terms : List (Term Symbol)) :
    InternedGuardedLanguage.forest holds ambient values terms ↔ InternedGuardedSyntax.forest holds environment expressions terms := by
  induction values generalizing expressions terms with
  | nil =>
      cases expressions with
      | nil => cases terms <;> simp only [InternedGuardedLanguage.forest, InternedGuardedSyntax.forest]
      | cons expression rest => simp only [List.map_nil, List.map_cons] at mapped; cases mapped
  | cons value rest ih =>
      cases expressions with
      | nil => simp only [List.map_nil, List.map_cons, List.cons_ne_nil] at mapped
      | cons expression expressions =>
          simp only [List.map_cons, List.cons.injEq] at mapped
          cases terms with
          | nil => simp only [InternedGuardedLanguage.forest, InternedGuardedSyntax.forest]
          | cons term terms =>
              rw [InternedGuardedLanguage.forest, InternedGuardedSyntax.forest]
              exact and_congr (iff_of_eq (congrFun mapped.1 term)) (ih expressions mapped.2 terms)

/-- The actual canonical edge has its requested full key and original child values. -/
theorem makeEdge_fields [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (cached : Cached state) (available : Values state values) :
    (run (makeEdge symbol guard values) state).1.entry.key = ⟨symbol, values.map Value.referenceOf, guard⟩ ∧
      (run (makeEdge symbol guard values) state).1.children = values := by
  have correct := edgeStep_correct ⟨symbol, values.map Value.referenceOf, guard⟩
    (fun entry => .mk entry values) state coherent.valid
  have after := edgeStep_coherent ⟨symbol, values.map Value.referenceOf, guard⟩
    (fun entry => .mk entry values) state coherent (fun _ key => ⟨rfl, key, rfl⟩)
  exact ⟨(after.edges _ _ correct.2.2).2.1,
    InternedShallowValues.makeEdge_children symbol guard values state coherent cached available⟩

/-- Actual edge allocation retains full independent guarded meaning of its ordered source children. -/
theorem makeEdge_language [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (ambient : Env Symbol) (environment : List (Lang Symbol)) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (expressions : List (Syntax Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state) (available : Values state values)
    (mapped : values.map (meaning holds ambient) = expressions.map (InternedGuardedSyntax.evaluate holds environment)) :
    InternedGuardedLanguage.edgeMeaning holds ambient (run (makeEdge symbol guard values) state).1 =
      InternedGuardedSyntax.edgeMeaning holds environment (.mk symbol guard expressions) := by
  obtain ⟨key, children⟩ := makeEdge_fields symbol guard values state coherent cached available
  generalize actual : (run (makeEdge symbol guard values) state).1 = edge at key children ⊢
  cases edge with
  | mk entry actualChildren =>
      simp only [EdgeValue.entry, EdgeValue.children] at key children
      subst actualChildren
      rw [InternedGuardedLanguage.edgeMeaning, InternedGuardedSyntax.edgeMeaning]
      simp only [key]
      funext term
      apply propext
      exact exists_congr (fun terms => and_congr Iff.rfl (and_congr
        (forest_equal holds ambient environment values expressions mapped terms) Iff.rfl))

/-- Subtype witnesses and list-membership witnesses denote the same alternative language. -/
theorem exists_member (values : List Item) (predicate : Item → Prop) :
    (∃ value : {value // value ∈ values}, predicate value.val) ↔ ∃ value ∈ values, predicate value := by
  constructor
  · rintro ⟨⟨value, member⟩, accepted⟩; exact ⟨value, member, accepted⟩
  · rintro ⟨value, member, accepted⟩; exact ⟨⟨value, member⟩, accepted⟩

/-- Prepending one edge splits its accepting alternatives into head and tail. -/
theorem exists_cons (first : Item) (rest : List Item) (predicate : Item → Prop) :
    (∃ value ∈ first :: rest, predicate value) ↔ predicate first ∨ ∃ value ∈ rest, predicate value := by
  constructor
  · rintro ⟨value, member, accepted⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl accepted
    · exact Or.inr ⟨value, member, accepted⟩
  · rintro (accepted | ⟨value, member, accepted⟩)
    · exact ⟨first, List.mem_cons_self, accepted⟩
    · exact ⟨value, List.mem_cons_of_mem _ member, accepted⟩

end MicroCFTA.InternedGuardedExecutionLists
