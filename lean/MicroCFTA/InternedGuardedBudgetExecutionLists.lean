import MicroCFTA.InternedGuardedBudgetRequest
import MicroCFTA.InternedGuardedExecutionLists

/-!
# Ordered budget transport for actual constructor lists

Equal ordered budget-language lists retain alternatives and child forests.
Actual edge allocation retains the full key and canonical child payloads.
-/
namespace MicroCFTA.InternedGuardedBudgetExecutionLists
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedNestedProvenance (Values)
open InternedGuardedBudget (Env meaning)
open InternedDepthSemantics (Shape)
open BinderBudgetLanguage (Lang)

/-- Equal budget-language lists have equal alternatives at every fixed bound. -/
theorem alternatives_equal (values : List Item) (expressions : List Expression)
    (left : Item → Lang Symbol) (right : Expression → Lang Symbol)
    (mapped : values.map left = expressions.map right) (budget : Nat) (term : Term Symbol) :
    (∃ value ∈ values, left value budget term) ↔ ∃ expression ∈ expressions, right expression budget term := by
  apply InternedGuardedExecutionLists.alternatives_equal values expressions
    (fun value => left value budget) (fun expression => right expression budget) ?_ term
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map (fun language => language budget)) mapped

/-- Equal ordered budget-language lists retain the exact common-bound child forest. -/
theorem forest_equal (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (shapes : List (Shape Atom)) (environment : List (Lang Symbol))
    (values : List (Value Symbol Guard)) (expressions : List (Syntax Symbol Guard))
    (mapped : values.map (meaning holds ambient) = expressions.map (InternedGuardedSmartBudget.evaluate holds shapes environment))
    (budget : Nat) (terms : List (Term Symbol)) :
    InternedGuardedBudget.forest holds ambient budget values terms ↔
      InternedGuardedSmartBudget.forest holds shapes environment budget expressions terms := by
  induction values generalizing expressions terms with
  | nil =>
      cases expressions with
      | nil => cases terms <;> simp only [InternedGuardedBudget.forest, InternedGuardedSmartBudget.forest]
      | cons expression rest => simp only [List.map_nil, List.map_cons] at mapped; cases mapped
  | cons value rest ih =>
      cases expressions with
      | nil => simp only [List.map_nil, List.map_cons, List.cons_ne_nil] at mapped
      | cons expression expressions =>
          simp only [List.map_cons, List.cons.injEq] at mapped
          cases terms with
          | nil => simp only [InternedGuardedBudget.forest, InternedGuardedSmartBudget.forest]
          | cons term terms =>
              rw [InternedGuardedBudget.forest, InternedGuardedSmartBudget.forest]
              exact and_congr (iff_of_eq (congrFun (congrFun mapped.1 budget) term)) (ih expressions mapped.2 terms)

/-- Actual edge allocation retains each complete guarded child budget language. -/
theorem makeEdge_language [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (ambient : Env Symbol) (shapes : List (Shape Atom)) (environment : List (Lang Symbol)) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (expressions : List (Syntax Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state) (available : Values state values)
    (mapped : values.map (meaning holds ambient) = expressions.map (InternedGuardedSmartBudget.evaluate holds shapes environment)) :
    InternedGuardedBudget.edgeMeaning holds ambient (run (makeEdge symbol guard values) state).1 =
      InternedGuardedSmartBudget.edgeMeaning holds shapes environment (.mk symbol guard expressions) := by
  obtain ⟨key, children⟩ := InternedGuardedExecutionLists.makeEdge_fields symbol guard values state coherent cached available
  generalize actual : (run (makeEdge symbol guard values) state).1 = edge at key children ⊢
  cases edge with
  | mk entry actualChildren =>
      simp only [EdgeValue.entry, EdgeValue.children] at key children
      subst actualChildren
      rw [InternedGuardedBudget.edgeMeaning, InternedGuardedSmartBudget.edgeMeaning]
      simp only [key]
      funext budget term
      apply propext
      exact exists_congr (fun terms => and_congr Iff.rfl (and_congr
        (forest_equal holds ambient shapes environment values expressions mapped budget terms) Iff.rfl))

end MicroCFTA.InternedGuardedBudgetExecutionLists
