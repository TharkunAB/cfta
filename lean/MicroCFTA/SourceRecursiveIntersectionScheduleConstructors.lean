import MicroCFTA.SourceRecursiveIntersectionScheduleEnvironment
import MicroCFTA.MergedPhysicalGroupEdges

/-!
# Actual constructor steps and semantic schedule syntax

Ordered child correspondence passes through actual edge construction,
node normalization, and union normalization. Complete guards remain in
the branch payloads. These local laws do not assume product language.
-/
namespace MicroCFTA.SourceRecursiveIntersectionScheduleConstructors
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionScheduleEnvironment (environment)

/-- An actual value has the same language as schedule syntax in every pair environment. -/
def Corresponds (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard)
    (shape : Shape (BinderLanguage.Payload Symbol)) : Prop :=
  ∀ ambient, InternedGuardedLanguage.meaning holds (environment ambient) value = BinderLanguage.meaning ambient shape

/-- An actual complete row has the same language as its schedule branch. -/
def EdgeCorresponds (holds : Guard → Term Symbol → Bool) (edge : EdgeValue Symbol Guard)
    (shape : Shape (BinderLanguage.Payload Symbol)) : Prop :=
  ∀ ambient, InternedGuardedLanguage.edgeMeaning holds (environment ambient) edge = BinderLanguage.meaning ambient shape

/-- Ordered corresponding children have exactly the schedule forest language. -/
theorem forest (holds : Guard → Term Symbol → Bool) (values : List (Value Symbol Guard))
    (shapes : List (Shape (BinderLanguage.Payload Symbol))) (related : All₂ (Corresponds holds) values shapes)
    (ambient : BinderLanguage.Env Symbol) (terms : List (Term Symbol)) :
    InternedGuardedLanguage.forest holds (environment ambient) values terms ↔ BinderLanguage.forest ambient shapes terms := by
  induction related generalizing terms with
  | nil => cases terms <;> simp only [InternedGuardedLanguage.forest, BinderLanguage.forest]
  | @cons value shape values shapes head tail ih =>
      cases terms with
      | nil => simp only [InternedGuardedLanguage.forest, BinderLanguage.forest]
      | cons term terms =>
          simp only [InternedGuardedLanguage.forest, BinderLanguage.forest, head ambient, ih terms]

/-- A literal complete row retains its symbol, guard, and ordered corresponding children. -/
theorem edge (holds : Guard → Term Symbol → Bool) (entry : Interned (EdgeKey Symbol Guard))
    (values : List (Value Symbol Guard)) (shapes : List (Shape (BinderLanguage.Payload Symbol)))
    (related : All₂ (Corresponds holds) values shapes) :
    EdgeCorresponds holds (.mk entry values)
      (.branch ⟨entry.key.symbol, fun term => holds entry.key.constraint term = true⟩ shapes) := by
  intro ambient
  funext term
  apply propext
  simp only [InternedGuardedLanguage.edgeMeaning, BinderLanguage.meaning]
  exact exists_congr (fun terms => and_congr Iff.rfl (and_congr (forest holds values shapes related ambient terms) Iff.rfl))

/-- Actual edge interning retains the corresponding full guarded schedule branch. -/
theorem makeEdge [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (shapes : List (Shape (BinderLanguage.Payload Symbol))) (related : All₂ (Corresponds holds) values shapes)
    (state : State Symbol Guard) (facts : Facts state) (available : ∀ value ∈ values, Available state value) :
    EdgeCorresponds holds (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1
      (.branch ⟨symbol, fun term => holds guard term = true⟩ shapes) := by
  have fields := MergedPhysicalGroupEdges.makeEdge_fields state facts symbol guard values available
  cases actual : (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 with
  | mk entry children =>
      simp only [actual, EdgeValue.entry, EdgeValue.children] at fields
      obtain ⟨sameSymbol, sameGuard, sameChildren⟩ := fields
      subst children
      simpa only [sameSymbol, sameGuard] using edge holds entry values shapes related

/-- Pointwise ordered correspondence gives exactly the same union of languages. -/
theorem alternatives (first : α → BinderLanguage.Lang Symbol) (second : β → BinderLanguage.Lang Symbol)
    (values : List α) (shapes : List β) (related : All₂ (fun value shape => first value = second shape) values shapes)
    (term : Term Symbol) :
    (∃ value ∈ values, first value term) ↔ ∃ shape ∈ shapes, second shape term := by
  induction related with
  | nil => simp only [List.not_mem_nil, false_and, exists_false]
  | @cons value shape values shapes head tail ih =>
      simp only [List.mem_cons, exists_eq_or_imp, head, ih]

/-- Actual node normalization has exactly the alternatives of the corresponding source rows. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (edges : List (EdgeValue Symbol Guard)) (shapes : List (Shape (BinderLanguage.Payload Symbol)))
    (related : All₂ (EdgeCorresponds holds) edges shapes) (state : State Symbol Guard) (facts : Facts state)
    (resident : InternedNestedProvenance.Edges state edges) :
    Corresponds holds (run (InternedConstructorTemplates.makeNode edges) state).1 (.alternatives shapes) := by
  intro ambient
  funext term
  apply propext
  rw [InternedGuardedLanguage.makeNode_exact state facts holds (environment ambient) edges resident]
  simp only [BinderLanguage.meaning, Subtype.exists, exists_prop]
  have meanings := related.imp (fun edge shape same => same ambient)
  have actual := alternatives (InternedGuardedLanguage.edgeMeaning holds (environment ambient))
    (BinderLanguage.meaning ambient) edges shapes meanings term
  simpa only [InternedGuardedLanguage.edgeMeaning_all] using actual

/-- Actual union normalization has exactly the alternatives of the corresponding returned members. -/
theorem makeUnion [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (values : List (Value Symbol Guard)) (shapes : List (Shape (BinderLanguage.Payload Symbol)))
    (related : All₂ (Corresponds holds) values shapes) (state : State Symbol Guard) (facts : Facts state)
    (available : InternedNestedProvenance.Values state values) :
    Corresponds holds (run (InternedConstructorTemplates.makeUnion values) state).1 (.alternatives shapes) := by
  intro ambient
  funext term
  apply propext
  rw [InternedGuardedLanguage.makeUnion_exact state facts holds (environment ambient) values available]
  simp only [BinderLanguage.meaning, Subtype.exists, exists_prop]
  exact alternatives _ _ values shapes (related.imp (fun value shape same => same ambient)) term

/-- An actual repeated-pair leaf has precisely its schedule reference language. -/
theorem repeated (holds : Guard → Term Symbol → Bool) (pair : Nat × Nat) :
    Corresponds holds (SourceRecursiveIntersectionControl.repeatedValue pair)
      (.ref (IntersectSchedule.pairName pair)) := by
  intro ambient
  rw [SourceRecursiveIntersectionControl.repeatedValue, InternedGuardedLanguage.meaning, BinderLanguage.meaning]
  rfl

end MicroCFTA.SourceRecursiveIntersectionScheduleConstructors
