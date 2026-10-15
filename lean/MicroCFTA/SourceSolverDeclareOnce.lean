import MicroCFTA.SourceSolverAppliedPreparation

/-!
# Scope declarations once per modeled solver process

The source creates a process and declares its fixed scope before any query.
A query pushes one frame, declares only its local names, asserts the same
counterexample, checks, and pops. Replacement starts another process epoch.
This component models that command sequence before the established name
encoding. External SMT commands, process creation, IO, and exception-safe
bracket execution remain adapters. No theorem certifies the runtime.
-/
namespace MicroCFTA.SourceSolverDeclareOnce
open FullSyntax (Name)
open FormulaLowering (TargetSort)
open SolverAdapter SourceSizedLiquidProgram

/-- Current query-local declarations retain reserved-name checks and inferred applied sorts. -/
def localDeclarations (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query) : Option (List Declaration) := do
  let ambient := declarations given
  let fresh ← SourceSizedLiquidAmbientRepair.reservedFreshList ambient assumptions query.bindings
  pure (fresh ++ SourceAppliedDeclarations.undeclared ambient fresh
    (mentioned assumptions query.antecedent query.consequent)
    (SourceAppliedDeclarations.queryApplications assumptions query.antecedent query.consequent))

/-- Successful local preparation reconstructs the complete existing logical request. -/
theorem local_prepared (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query)
    (locals : List Declaration) (prepared : localDeclarations given assumptions query = some locals) :
    SourceSolverAppliedPreparation.prepare given assumptions query =
      some ⟨declarations given ++ locals, assertion assumptions query.antecedent query.consequent⟩ := by
  unfold localDeclarations at prepared
  unfold SourceSolverAppliedPreparation.prepare
  cases fresh : SourceSizedLiquidAmbientRepair.reservedFreshList (declarations given) assumptions query.bindings with
  | none => simp [fresh] at prepared
  | some entries =>
      simp only [fresh, bind, Option.bind, pure, Option.some.injEq] at prepared ⊢
      rw [← prepared]
      simp only [List.append_assoc]

/-- A rejected fresh-name preflight submits no request in either arrangement. -/
theorem rejected_exact (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query) :
    localDeclarations given assumptions query = none ↔ SourceSolverAppliedPreparation.prepare given assumptions query = none := by
  unfold localDeclarations SourceSolverAppliedPreparation.prepare
  cases SourceSizedLiquidAmbientRepair.reservedFreshList (declarations given) assumptions query.bindings <;> simp

/-- These are the source commands relevant to declaration lifetime. -/
inductive Command where
  | declare (bindings : List Declaration)
  | push
  | assert (formula : FormulaLowering.Formula)
  | check
  | pop

/-- One query bracket contains its declarations and its single counterexample assertion. -/
structure Frame where
  declared : List Declaration
  asserted : Option FormulaLowering.Formula

/-- A process epoch has permanent declarations and at most one serialized query frame. -/
structure Context where
  epoch : Nat
  scope : List Declaration
  frame : Option Frame
  scopeWrites : Nat
  sent : List Command

/-- Active declarations include the query frame only while that frame exists. -/
def active (context : Context) : List Declaration :=
  context.scope ++ match context.frame with | none => [] | some frame => frame.declared

/-- A modeled declaration request rejects duplicate active names, regardless of their sorts. -/
abbrev distinct (bindings : List Declaration) : Prop := (bindings.map Prod.fst).Nodup

/-- The abstract SMT command adapter checks declaration names and query-frame sequencing. -/
def step (command : Command) (context : Context) : Option Context :=
  match command with
  | .declare bindings =>
      if distinct (active context ++ bindings) then
        match context.frame with
        | none => some {context with scope := context.scope ++ bindings, scopeWrites := context.scopeWrites + 1, sent := context.sent ++ [command]}
        | some frame => some {context with frame := some {frame with declared := frame.declared ++ bindings}, sent := context.sent ++ [command]}
      else none
  | .push => match context.frame with
      | none => some {context with frame := some ⟨[], none⟩, sent := context.sent ++ [command]}
      | some _ => none
  | .assert formula => match context.frame with
      | some ⟨bindings, none⟩ => some {context with frame := some ⟨bindings, some formula⟩, sent := context.sent ++ [command]}
      | _ => none
  | .check => match context.frame with
      | some ⟨_, some _⟩ => some {context with sent := context.sent ++ [command]}
      | _ => none
  | .pop => match context.frame with
      | some _ => some {context with frame := none, sent := context.sent ++ [command]}
      | none => none

/-- Command execution follows the literal sequence and stops at an invalid adapter operation. -/
def commands : List Command → Context → Option Context
  | [], context => some context
  | command :: rest, context => do
      let next ← step command context
      commands rest next

/-- A quiescent process has no query-local declarations or assertions. -/
def idle (epoch : Nat) (scope : List Declaration) (writes : Nat) (sent : List Command) : Context :=
  ⟨epoch, scope, none, writes, sent⟩

/-- newContext creates an empty process and sends exactly the fixed scope declarations. -/
def newContext (epoch : Nat) (scope : List Declaration) : Option Context :=
  commands [.declare scope] (idle epoch [] 0 [])

/-- Successful initialization derives the permanent scope and its single declaration batch. -/
theorem newContext_effects (epoch : Nat) (scope : List Declaration) (valid : distinct scope) :
    newContext epoch scope = some (idle epoch scope 1 [.declare scope]) := by
  simp [newContext, commands, step, active, idle, valid]

/-- The source sends only local declarations between its push and pop. -/
def queryCommands (locals : List Declaration) (asserted : FormulaLowering.Formula) : List Command :=
  [.push, .declare locals, .assert asserted, .check, .pop]

/-- The observed logical request uses both the permanent and the current query declarations. -/
def observe (context : Context) : Option Prepared := do
  let frame ← context.frame
  let asserted ← frame.asserted
  pure ⟨active context, asserted⟩

/-- A completed bracket observes the actual assertion before it checks and removes its query frame. -/
def queryBracket (context : Context) (locals : List Declaration) (asserted : FormulaLowering.Formula) : Option (Prepared × Context) := do
  let beforeCheck ← commands [.push, .declare locals, .assert asserted] context
  let request ← observe beforeCheck
  let after ← commands [.check, .pop] beforeCheck
  pure (request, after)

/-- The literal bracket derives its complete request and clears all query-local state. -/
theorem bracket_effects (epoch : Nat) (scope locals : List Declaration) (writes : Nat) (sent : List Command)
    (asserted : FormulaLowering.Formula) (valid : distinct (scope ++ locals)) :
    queryBracket (idle epoch scope writes sent) locals asserted =
      some (⟨scope ++ locals, asserted⟩, idle epoch scope writes (sent ++ queryCommands locals asserted)) := by
  simp [queryBracket, commands, step, active, idle, valid, observe, queryCommands, List.append_assoc]

/-- A completed query retains scope declarations and removes every distinct local name. -/
theorem no_local_leak (epoch : Nat) (scope locals : List Declaration) (writes : Nat) (sent : List Command)
    (asserted : FormulaLowering.Formula) (valid : distinct (scope ++ locals)) :
    ∃ request after, queryBracket (idle epoch scope writes sent) locals asserted = some (request, after) ∧
      after.scope = scope ∧ after.frame = none ∧ after.scopeWrites = writes ∧
      active after = scope ∧ (∀ name ∈ locals.map Prod.fst, name ∉ (active after).map Prod.fst) := by
  refine ⟨_, _, bracket_effects epoch scope locals writes sent asserted valid, rfl, rfl, rfl, ?_, ?_⟩
  · simp [active, idle]
  · intro name member
    have disjoint := (List.nodup_append.mp (by simpa [distinct] using valid)).2.2
    simpa [active, idle] using fun present => disjoint name present name member rfl

/-- Two actual completed queries retain the single original scope declaration batch. -/
theorem two_queries (epoch : Nat) (scope first second : List Declaration) (writes : Nat) (sent : List Command)
    (left right : FormulaLowering.Formula) (firstValid : distinct (scope ++ first)) (secondValid : distinct (scope ++ second)) :
    ∃ middle after,
      queryBracket (idle epoch scope writes sent) first left = some (⟨scope ++ first, left⟩, middle) ∧
      queryBracket middle second right = some (⟨scope ++ second, right⟩, after) ∧
      after = idle epoch scope writes (sent ++ queryCommands first left ++ queryCommands second right) := by
  refine ⟨_, _, bracket_effects epoch scope first writes sent left firstValid,
    bracket_effects epoch scope second writes (sent ++ queryCommands first left) right secondValid, ?_⟩
  simp only [List.append_assoc]

/-- Moving fixed declarations outside the bracket leaves the observed logical request unchanged. -/
theorem declaration_motion (epoch : Nat) (scope locals : List Declaration) (asserted : FormulaLowering.Formula)
    (valid : distinct (scope ++ locals)) :
    ∃ oldAfter newAfter,
      queryBracket (idle epoch [] 0 []) (scope ++ locals) asserted = some (⟨scope ++ locals, asserted⟩, oldAfter) ∧
      queryBracket (idle epoch scope 1 [.declare scope]) locals asserted = some (⟨scope ++ locals, asserted⟩, newAfter) ∧
      oldAfter.scope = [] ∧ newAfter.scope = scope ∧ newAfter.scopeWrites = 1 := by
  refine ⟨idle epoch [] 0 (queryCommands (scope ++ locals) asserted),
    idle epoch scope 1 ([.declare scope] ++ queryCommands locals asserted),
    ?_, bracket_effects epoch scope locals 1 [.declare scope] asserted valid, rfl, rfl, rfl⟩
  simpa only [List.nil_append] using bracket_effects epoch [] (scope ++ locals) 0 [] asserted (by simpa using valid)

/-- Cleanup discards any old frame; newContext redeclares scope in the next process epoch. -/
def replaceContext (context : Context) (scope : List Declaration) : Option Context :=
  newContext (context.epoch + 1) scope

/-- Replacement derives a fresh permanent scope even when the discarded query frame remains open. -/
theorem replacement_effects (context : Context) (scope : List Declaration) (valid : distinct scope) :
    replaceContext context scope = some (idle (context.epoch + 1) scope 1 [.declare scope]) :=
  newContext_effects _ _ valid

/-- Control decisions reuse the existing source response and exception mapping. -/
def finishContext (scope : List Declaration) (milliseconds : Int) (attempt : Attempt) (context : Context) : Option (Result × Context) := do
  let decision := SolverAdapter.finish milliseconds attempt
  let after ← if decision.replaceContext then replaceContext context scope else some context
  pure (decision.result, after)

/-- A solver Error starts a new epoch and derives its redeclared scope before propagation. -/
theorem error_redeclares (context : Context) (scope : List Declaration) (valid : distinct scope)
    (milliseconds : Int) (message : String) (reached : Bool) :
    finishContext scope milliseconds (.answered (.error message) reached) context =
      some (.raised (.rejected message), idle (context.epoch + 1) scope 1 [.declare scope]) := by
  simp [finishContext, SolverAdapter.finish, responseVerdict, replacement_effects context scope valid]

/-- Interruption may leave an open frame; replacement removes it and its local declarations. -/
theorem interruption_redeclares (context : Context) (scope : List Declaration) (valid : distinct scope)
    (milliseconds : Int) (message : String) :
    finishContext scope milliseconds (.interrupted message) context =
      some (.raised (.interrupted message), idle (context.epoch + 1) scope 1 [.declare scope]) := by
  simp [finishContext, SolverAdapter.finish, replacement_effects context scope valid]

/-- The source timeout conversion follows the completed bracket and retains that context. -/
theorem timeout_retains (scope : List Declaration) (milliseconds : Int) (context : Context) :
    finishContext scope milliseconds (.answered .unknown true) context = some (.raised (.timeLimit milliseconds), context) := rfl

/-- Successful current preparation and the command interpreter produce the same logical query. -/
theorem current_query (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query)
    (locals : List Declaration) (prepared : localDeclarations given assumptions query = some locals)
    (epoch writes : Nat) (sent : List Command) (valid : distinct (declarations given ++ locals)) :
    ∃ request after,
      queryBracket (idle epoch (declarations given) writes sent) locals
        (assertion assumptions query.antecedent query.consequent) = some (request, after) ∧
      SourceSolverAppliedPreparation.prepare given assumptions query = some request ∧
      request.declared = declarations given ++ locals ∧
      request.asserted = assertion assumptions query.antecedent query.consequent ∧
      after = idle epoch (declarations given) writes (sent ++ queryCommands locals request.asserted) :=
  ⟨_, _, bracket_effects _ _ _ _ _ _ valid, local_prepared _ _ _ _ prepared, rfl, rfl, rfl⟩

/-- The established native name codec retains this complete observed request. -/
theorem encoded_query (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query)
    (locals : List Declaration) (prepared : localDeclarations given assumptions query = some locals) :
    SourceSolverAppliedPreparation.encodedPrepare given assumptions query =
      some (SourceSolverNameSemantics.renamePrepared SourceSolverNameFastEncoding.encode
        ⟨declarations given ++ locals, assertion assumptions query.antecedent query.consequent⟩) := by
  rw [SourceSolverAppliedPreparation.sourcePrepare_encode, local_prepared given assumptions query locals prepared]
  rfl

/-- The observed assertion and admitted sort domains give exactly the existing logical entailment. -/
theorem logical_query (model : FormulaLowering.Model Value) (given : List Declaration)
    (assumptions : List FullSyntax.Formula) (query : Query) (locals : List Declaration)
    (prepared : localDeclarations given assumptions query = some locals)
    (epoch writes : Nat) (sent : List Command) (valid : distinct (declarations given ++ locals)) :
    ∃ request after,
      queryBracket (idle epoch (declarations given) writes sent) locals
        (assertion assumptions query.antecedent query.consequent) = some (request, after) ∧
      SourceSolverAppliedPreparation.prepare given assumptions query = some request ∧
      ((¬∃ env, Admitted model request.declared env ∧ FormulaLowering.Holds model env request.asserted) ↔
        Entails model (declarations given ++ locals) assumptions query.antecedent query.consequent) := by
  obtain ⟨request, after, trace, original, declared, asserted, _⟩ := current_query given assumptions query locals prepared epoch writes sent valid
  refine ⟨request, after, trace, original, ?_⟩
  rw [declared, asserted]
  exact unsat_iff_entails model _ assumptions query.antecedent query.consequent

/-- A sound external response has the same result support for the observed source query. -/
theorem observed_response_sound (model : FormulaLowering.Model Value) (request : Prepared)
    (assumptions : List FullSyntax.Formula) (query : Query)
    (asserted : request.asserted = assertion assumptions query.antecedent query.consequent)
    (milliseconds : Int) (response : Response) (reached : Bool) (correct : ResponseCorrect model request response) :
    ResultSupports (SolverAdapter.finish milliseconds (.answered response reached)).result
      (Entails model request.declared assumptions query.antecedent query.consequent) :=
  SolverAdapter.response_sound model request assumptions query.antecedent query.consequent asserted milliseconds reached response correct

/-- Initialization followed by the literal bracket derives its request and single scope write. -/
theorem initialized_query (epoch : Nat) (scope locals : List Declaration) (asserted : FormulaLowering.Formula)
    (valid : distinct (scope ++ locals)) :
    (do
      let context ← newContext epoch scope
      queryBracket context locals asserted) =
        some (⟨scope ++ locals, asserted⟩, idle epoch scope 1 ([.declare scope] ++ queryCommands locals asserted)) := by
  have scopeValid : distinct scope := (List.nodup_append.mp (by simpa [distinct] using valid)).1
  rw [newContext_effects epoch scope scopeValid]
  exact bracket_effects epoch scope locals 1 [.declare scope] asserted valid

/-- The dispatcher records an optional observed request and the actual returned process context. -/
structure QueryOutcome where
  result : Result
  observed : Option Prepared
  context : Context

/-- This is the source preflight, completed bracket, and response branch in their actual order. -/
def runQuery (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query)
    (milliseconds : Int) (response : Response) (reached : Bool) (context : Context) : Option QueryOutcome := do
  match localDeclarations given assumptions query with
  | none => pure ⟨.returned .unknown, none, context⟩
  | some locals =>
      let (request, next) ← queryBracket context locals (assertion assumptions query.antecedent query.consequent)
      let (answer, after) ← finishContext (declarations given) milliseconds (.answered response reached) next
      pure ⟨answer, some request, after⟩

/-- Rejected source preflight sends no command and retains the process epoch and scope. -/
theorem runQuery_rejected (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query)
    (rejected : localDeclarations given assumptions query = none)
    (milliseconds : Int) (response : Response) (reached : Bool) (context : Context) :
    runQuery given assumptions query milliseconds response reached context = some ⟨.returned .unknown, none, context⟩ := by
  simp [runQuery, rejected]

/-- Every valid completed source query derives one permanent scope batch and no local leakage. -/
theorem runQuery_effects (given : List Declaration) (assumptions : List FullSyntax.Formula) (query : Query)
    (locals : List Declaration) (prepared : localDeclarations given assumptions query = some locals)
    (valid : distinct (declarations given ++ locals)) (epoch : Nat) (sent : List Command)
    (milliseconds : Int) (response : Response) (reached : Bool) :
    ∃ after, runQuery given assumptions query milliseconds response reached (idle epoch (declarations given) 1 sent) =
      some ⟨(SolverAdapter.finish milliseconds (.answered response reached)).result,
        some ⟨declarations given ++ locals, assertion assumptions query.antecedent query.consequent⟩, after⟩ ∧
      after.scope = declarations given ∧ after.frame = none ∧ after.scopeWrites = 1 ∧
      (after.epoch = epoch ∨ after.epoch = epoch + 1) := by
  have trace := bracket_effects epoch (declarations given) locals 1 sent
    (assertion assumptions query.antecedent query.consequent) valid
  have scopeValid : distinct (declarations given) := (List.nodup_append.mp (by simpa [distinct] using valid)).1
  cases response with
  | error message =>
      refine ⟨idle (epoch + 1) (declarations given) 1 [.declare (declarations given)], ?_, rfl, rfl, rfl, Or.inr rfl⟩
      simp only [runQuery, prepared, bind, Option.bind, trace]
      rw [error_redeclares _ _ scopeValid]
      rfl
  | unsat | sat | unknown | unexpected =>
      all_goals
        refine ⟨idle epoch (declarations given) 1 (sent ++ queryCommands locals (assertion assumptions query.antecedent query.consequent)),
          ?_, rfl, rfl, rfl, Or.inl rfl⟩
        simp [runQuery, prepared, trace, finishContext, SolverAdapter.finish]

end MicroCFTA.SourceSolverDeclareOnce
