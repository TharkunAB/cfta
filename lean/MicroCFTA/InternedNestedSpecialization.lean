import MicroCFTA.InternedNestedDependencies

/-!
# Specialize nested dependencies from their actual earlier source trace

Each nested binder that ignores the enclosing local variable has already
completed during the earlier body execution. Later executions replace that
binder by its exact stored result. Ordinary constructors retain their source
order and their actual cache effects.
-/
namespace MicroCFTA.InternedNestedSpecialization
open InternedConstructorTemplates InternedNestedConstruction InternedNestedDependencies

mutual
/-- Every immediate nested binder ignores the enclosing local variable. -/
def Independent : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesIndependent edges
  | .union members => ManyIndependent members
  | expression@(.binder _ _) => 0 ∉ inputs expression
termination_by expression => sizeOf expression

/-- All ordinary children satisfy the same local dependency condition. -/
def ManyIndependent : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Independent first ∧ ManyIndependent rest
termination_by expressions => sizeOf expressions

/-- Edge declarations retain their original child dependency conditions. -/
def EdgesIndependent : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => ManyIndependent children ∧ EdgesIndependent rest
termination_by expressions => sizeOf expressions
end

/-- A completed sequence exposes the actual completed earlier action. -/
theorem bind_done (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (value : Result) (final : State Symbol Guard)
    (completed : outcome.bind next = .done value final) :
    ∃ earlier middle, outcome = .done earlier middle ∧ next earlier middle = .done value final := by
  cases outcome with
  | pending key state => cases completed
  | done earlier middle => exact ⟨earlier, middle, rfl, completed⟩

/-- Ordinary work and nested execution use the same sequencing order. -/
theorem work_bind [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard First)
    (next : First → Work Symbol Guard Result) (state : State Symbol Guard) :
    work (computation.bind next) state =
      (work computation state).bind (fun value after => work (next value) after) := by
  simp only [work, run_bind, Outcome.bind]

mutual
/-- A successful body trace derives one ordinary template for every later local input. -/
theorem build_specializes [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (independent : Independent expression) (initial : Value Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (completed : build expression (initial :: environment) before = .done value final) :
    ∃ template : Template Symbol Guard, ∀ argument after,
      InternedConstructorTemplates.Valid after → Grows final after →
      build expression (argument :: environment) after = work (compile template argument) after := by
  cases expression with
  | empty => exact ⟨.captured .empty, fun _ _ _ _ => by simp [build, compile, work, run]⟩
  | var index =>
      cases index with
      | zero => exact ⟨.argument, fun _ _ _ _ => by simp [build, compile, work, run]⟩
      | succ index =>
          exact ⟨.captured (environment[index]?.getD .empty), fun _ _ _ _ => by
            simp [build, compile, work, run]⟩
  | node edges =>
      simp only [build] at completed
      simp only [Independent] at independent
      obtain ⟨values, middle, earlier, later⟩ := bind_done _ _ value final completed
      have middleFacts := buildEdges_correct edges (initial :: environment) before valid
      rw [earlier] at middleFacts
      have finishFacts := work_correct (makeNode values) middle middleFacts.1
      rw [later] at finishFacts
      obtain ⟨templates, specializes⟩ := buildEdges_specializes edges independent initial environment before
        values middle valid earlier
      refine ⟨.node templates, ?_⟩
      intro argument after afterValid growth
      simp only [build, compile, work_bind,
        specializes argument after afterValid (grows_trans finishFacts.2 growth)]
  | union members =>
      simp only [build] at completed
      simp only [Independent] at independent
      obtain ⟨values, middle, earlier, later⟩ := bind_done _ _ value final completed
      have middleFacts := buildMany_correct members (initial :: environment) before valid
      rw [earlier] at middleFacts
      have finishFacts := work_correct (makeUnion values) middle middleFacts.1
      rw [later] at finishFacts
      obtain ⟨templates, specializes⟩ := buildMany_specializes members independent initial environment before
        values middle valid earlier
      refine ⟨.union templates, ?_⟩
      intro argument after afterValid growth
      simp only [build, compile, work_bind,
        specializes argument after afterValid (grows_trans finishFacts.2 growth)]
  | binder smart body =>
      simp only [Independent] at independent
      refine ⟨.captured value, ?_⟩
      intro argument after _ growth
      have same : Agree (inputs (.binder smart body)) (initial :: environment) (argument :: environment) := by
        intro index member
        cases index with
        | zero => exact False.elim (independent member)
        | succ index => rfl
      simpa only [compile, work, run] using independent_replay (.binder smart body)
        (initial :: environment) (argument :: environment) before after value final valid completed growth same
termination_by sizeOf expression

/-- Child specialization retains the source order and every ordinary cache operation. -/
theorem buildMany_specializes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (independent : ManyIndependent expressions) (initial : Value Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (values : List (Value Symbol Guard)) (final : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (completed : buildMany expressions (initial :: environment) before = .done values final) :
    ∃ templates : List (Template Symbol Guard), ∀ argument after,
      InternedConstructorTemplates.Valid after → Grows final after →
      buildMany expressions (argument :: environment) after = work (compileMany templates argument) after := by
  cases expressions with
  | nil => exact ⟨[], fun _ _ _ _ => by simp [buildMany, compileMany, work, run]⟩
  | cons first rest =>
      simp only [buildMany] at completed
      simp only [ManyIndependent] at independent
      obtain ⟨value, middle, earlier, later⟩ := bind_done _ _ values final completed
      obtain ⟨tail, last, tailDone, assembled⟩ := bind_done _ _ values final later
      simp only [Outcome.done.injEq] at assembled
      rcases assembled with ⟨rfl, rfl⟩
      have middleFacts := build_correct first (initial :: environment) before valid
      rw [earlier] at middleFacts
      have finalFacts := buildMany_correct rest (initial :: environment) middle middleFacts.1
      rw [tailDone] at finalFacts
      obtain ⟨headTemplate, headSpecializes⟩ := build_specializes first independent.1 initial environment before
        value middle valid earlier
      obtain ⟨tailTemplates, tailSpecializes⟩ := buildMany_specializes rest independent.2 initial environment middle
        tail last middleFacts.1 tailDone
      refine ⟨headTemplate :: tailTemplates, ?_⟩
      intro argument after afterValid growth
      have headLater := headSpecializes argument after afterValid (grows_trans finalFacts.2 growth)
      have headFacts := run_correct (compile headTemplate argument) after afterValid
      have tailLater := tailSpecializes argument (run (compile headTemplate argument) after).2
        headFacts.1 (grows_trans growth headFacts.2)
      simp only [buildMany, compileMany, headLater, work, Outcome.bind]
      rw [tailLater]
      simp only [work, run_bind, run]
termination_by sizeOf expressions

/-- Edge specialization captures only completed nested binders and preserves edge allocation order. -/
theorem buildEdges_specializes [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (independent : EdgesIndependent expressions) (initial : Value Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (values : List (EdgeValue Symbol Guard)) (final : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before)
    (completed : buildEdges expressions (initial :: environment) before = .done values final) :
    ∃ templates : List (EdgeTemplate Symbol Guard), ∀ argument after,
      InternedConstructorTemplates.Valid after → Grows final after →
      buildEdges expressions (argument :: environment) after = work (compileEdges templates argument) after := by
  cases expressions with
  | nil => exact ⟨[], fun _ _ _ _ => by simp [buildEdges, compileEdges, work, run]⟩
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [buildEdges] at completed
          simp only [EdgesIndependent] at independent
          obtain ⟨childrenValues, middle, earlier, later⟩ := bind_done _ _ values final completed
          obtain ⟨edge, afterEdge, edgeDone, afterEdgeDone⟩ := bind_done _ _ values final later
          obtain ⟨tail, last, tailDone, assembled⟩ := bind_done _ _ values final afterEdgeDone
          simp only [Outcome.done.injEq] at assembled
          rcases assembled with ⟨rfl, rfl⟩
          have middleFacts := buildMany_correct children (initial :: environment) before valid
          rw [earlier] at middleFacts
          have edgeFacts := work_correct (makeEdge symbol constraint childrenValues) middle middleFacts.1
          rw [edgeDone] at edgeFacts
          have finalFacts := buildEdges_correct rest (initial :: environment) afterEdge edgeFacts.1
          rw [tailDone] at finalFacts
          obtain ⟨childrenTemplates, childrenSpecialize⟩ := buildMany_specializes children independent.1 initial
            environment before childrenValues middle valid earlier
          obtain ⟨tailTemplates, tailSpecialize⟩ := buildEdges_specializes rest independent.2 initial environment
            afterEdge tail last edgeFacts.1 tailDone
          refine ⟨.mk symbol constraint childrenTemplates :: tailTemplates, ?_⟩
          intro argument after afterValid growth
          have childrenLater := childrenSpecialize argument after afterValid
            (grows_trans edgeFacts.2 (grows_trans finalFacts.2 growth))
          let childrenResult := run (compileMany childrenTemplates argument) after
          have childrenFacts := run_correct (compileMany childrenTemplates argument) after afterValid
          let edgeResult := run (makeEdge symbol constraint childrenResult.1) childrenResult.2
          have actualEdgeFacts := run_correct (makeEdge symbol constraint childrenResult.1) childrenResult.2 childrenFacts.1
          have tailLater := tailSpecialize argument edgeResult.2 actualEdgeFacts.1
            (grows_trans growth (grows_trans childrenFacts.2 actualEdgeFacts.2))
          simp only [buildEdges, compileEdges, childrenLater, work, Outcome.bind]
          rw [tailLater]
          simp only [work, run_bind, run, edgeResult, childrenResult]
termination_by sizeOf expressions
end

end MicroCFTA.InternedNestedSpecialization
