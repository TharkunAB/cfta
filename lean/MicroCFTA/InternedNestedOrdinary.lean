import MicroCFTA.InternedStagedBinders
import MicroCFTA.InternedNestedSpecialization
import MicroCFTA.InternedNestedCoverage
import MicroCFTA.InternedErasedEdgeReplay

/-!
# Ordinary templates are actual nested source expressions

An ordinary skeleton uses the nearest local variable and a finite list of
enclosing capture slots. Its nested execution equals its existing finite
template computation, including all cache effects.
-/
namespace MicroCFTA.InternedNestedOrdinary
open InternedConstructorTemplates InternedNestedConstruction InternedNestedSpecialization
open InternedStagedBinders (Skeleton EdgeSkeleton instantiate instantiateMany instantiateEdges)
open InternedRecordCoherence InternedNestedCoverage

mutual
/-- Insert an ordinary skeleton into the full lexical source syntax. -/
def source : Skeleton Symbol Guard → Syntax Symbol Guard
  | .argument => .var 0
  | .capture index => .var (index + 1)
  | .node edges => .node (sourceEdges edges)
  | .union members => .union (sourceMany members)
termination_by expression => sizeOf expression

/-- Insert each ordered child into the same lexical source environment. -/
def sourceMany : List (Skeleton Symbol Guard) → List (Syntax Symbol Guard)
  | [] => []
  | first :: rest => source first :: sourceMany rest
termination_by expressions => sizeOf expressions

/-- Source edge declarations retain their symbol, guard, and ordered children. -/
def sourceEdges : List (EdgeSkeleton Symbol Guard) → List (EdgeSyntax Symbol Guard)
  | [] => []
  | .mk symbol constraint children :: rest => .mk symbol constraint (sourceMany children) :: sourceEdges rest
termination_by expressions => sizeOf expressions
end

mutual
/-- Actual nested execution of ordinary syntax equals its finite constructor template. -/
theorem source_build [DecidableEq (EdgeKey Symbol Guard)] (expression : Skeleton Symbol Guard)
    (argument : Value Symbol Guard) (captures : List (Value Symbol Guard)) (state : State Symbol Guard) :
    build (source expression) (argument :: captures) state = work (compile (instantiate expression captures) argument) state := by
  cases expression with
  | argument => simp [source, build, instantiate, compile, work, run]
  | capture index => simp [source, build, instantiate, compile, work, run]
  | node edges => simp only [source, build, instantiate, compile, work_bind, sourceEdges_build edges argument captures state]
  | union members => simp only [source, build, instantiate, compile, work_bind, sourceMany_build members argument captures state]
termination_by sizeOf expression

/-- Ordinary child execution retains the exact complete ordered constructor computation. -/
theorem sourceMany_build [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Skeleton Symbol Guard))
    (argument : Value Symbol Guard) (captures : List (Value Symbol Guard)) (state : State Symbol Guard) :
    buildMany (sourceMany expressions) (argument :: captures) state =
      work (compileMany (instantiateMany expressions captures) argument) state := by
  cases expressions with
  | nil => simp [sourceMany, buildMany, instantiateMany, compileMany, work, run]
  | cons first rest =>
      simp only [sourceMany, buildMany, instantiateMany, compileMany, work_bind, source_build first argument captures state]
      congr 1
      funext value after
      simp only [sourceMany_build rest argument captures after]
      congr 1
termination_by sizeOf expressions

/-- Ordinary edge execution uses the same separate edge-cache requests in the same order. -/
theorem sourceEdges_build [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSkeleton Symbol Guard))
    (argument : Value Symbol Guard) (captures : List (Value Symbol Guard)) (state : State Symbol Guard) :
    buildEdges (sourceEdges expressions) (argument :: captures) state =
      work (compileEdges (instantiateEdges expressions captures) argument) state := by
  cases expressions with
  | nil => simp [sourceEdges, buildEdges, instantiateEdges, compileEdges, work, run]
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [sourceEdges, buildEdges, instantiateEdges, compileEdges, work_bind, sourceMany_build children argument captures state]
          congr 1
          funext values after
          congr 1
          funext edge next
          simp only [sourceEdges_build rest argument captures next]
          congr 1
termination_by sizeOf expressions
end

/-- Complete caches make the source request equal the existing finite-template Mu operation. -/
theorem request_template [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (template : Template Symbol Guard) (depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (covered : Covered [] state) :
    request smart depth ordinary (fun name current => work (compileBody template name) current) state =
      .done (finish smart (finishMu template depth ordinary state).1) (finishMu template depth ordinary state).2 := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      rcases covered.nodes _ entry installed with impossible | ⟨record, stored⟩
      · cases impossible
      · simp only [request, installed, stored, finishMu]
  | none =>
      have missing : state.nodeRecords (muKey depth ordinary) = none := by
        cases stored : state.nodeRecords (muKey depth ordinary) with
        | none => rfl
        | some value =>
            obtain ⟨entry, present, _⟩ := coherent.nodes _ value stored
            rw [installed] at present
            cases present
      simp only [request, installed, finishMu, missing, work, Outcome.bind]

/-- The full source binder over ordinary syntax executes the exact two probes, body reservation, and cleanup. -/
theorem source_binder [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Skeleton Symbol Guard)
    (captures : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (covered : Covered [] state) :
    build (.binder smart (source body)) captures state =
      .done (finish smart (internMu (instantiate body captures) state).1)
        (internMu (instantiate body captures) state).2 := by
  let template := instantiate body captures
  have firstCoherent := InternedErasedEdgeReplay.run_coherent (compileBody template .depth) state
    (safe_bind _ _ (compile_safe _ _) (withoutSelfReference_safe _)) coherent
  have firstCovered := run_covered (compileBody template .depth) state coherent.valid covered
  have secondCoherent := InternedErasedEdgeReplay.run_coherent
    (compileBody template (.uninterned (run (compileBody template .depth) state).1.depth))
    (run (compileBody template .depth) state).2 (safe_bind _ _ (compile_safe _ _) (withoutSelfReference_safe _)) firstCoherent
  have secondCovered := run_covered
    (compileBody template (.uninterned (run (compileBody template .depth) state).1.depth))
    (run (compileBody template .depth) state).2 firstCoherent.valid firstCovered
  simp only [build, source_build, ← work_bind]
  simp only [work, Outcome.bind]
  exact request_template smart template _ _ _ secondCoherent secondCovered

end MicroCFTA.InternedNestedOrdinary
