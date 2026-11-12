import MicroCFTA.SourceSynthesisCurrentProgramAdmission
import MicroCFTA.SourceSynthesisCurrentConstruction
import MicroCFTA.SourceSynthesisRelevantSingletonLookup

/-!
# Current relevant and root admission

The existing raw certificate retains original query tokens. Current key
resolution supplies the resource domain for relevant rows. Root permutation
coverage derives that resolution through one fixed original query lookup.
All accepted bodies retain their exact annotations and Program projections.
These laws concern source syntax. They make no native execution claim.
-/
namespace MicroCFTA.SourceSynthesisCurrentRelevantAdmission
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax (Ty Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression Row Context termsRows relevantRows resolveArguments ofType)
open SourceSynthesisCurrentContext (context constructorCatalog context_types)
open SourceSynthesisCurrentProgramAdmission (Eligible eligible_program_member)
open SourceSynthesisCurrentTypeAdmission (typeIn_iff_admitted)
open SourceSynthesisPr210TypeReflection (encodeTy candidateRigid candidateRigid_eq_iff)
open SourceSynthesisPr211QueryBindings (queryBindings queryBindings_lookup)
open SourceSynthesisOrdinaryTyping (Typed queryLookup)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren_eq_map)
open SourceSynthesisSelections (resolveSelection_empty resolveSelection_spec root_lookup_exists permutations)
open SourceSynthesisSelectionClosure (permutations_spec resolveSelection_take_drop)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

private theorem bind_ok {Error Input Output : Type} (action : Except Error Input)
    (next : Input → Except Error Output) (value : Output) (returned : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases returned
  | ok input => exact ⟨input, rfl, returned⟩

private theorem union_member (holds : Guard → Term Symbol → Bool)
    (members : List Expression) (selected : Expression) (term : Term Symbol)
    (present : selected ∈ members)
    (accepted : evaluate holds [] (mapSyntax literal selected) term) :
    evaluate holds [] (mapSyntax literal (.union members)) term := by
  rw [mapSyntax, evaluate]
  refine ⟨⟨mapSyntax literal selected, ?_⟩, accepted⟩
  rw [mapChildren_eq_map]
  exact List.mem_map.mpr ⟨selected, present, rfl⟩

private theorem token_length {lib : Library} {query : Query} {asArgument : Bool}
    {program : Program} {typ : Ty} {tokens : List (String × Ty)}
    (eligible : Eligible lib query asArgument program typ tokens) : tokens.length ≤ program.components := by
  induction eligible with
  | group => exact Nat.zero_le _
  | argumentOnly => exact Nat.zero_le _
  | queryArgument => exact Nat.zero_le _
  | queryToken => exact Nat.le_refl 1
  | application _first _second _result firstIH secondIH =>
      simp only [List.length_append, Program.components]
      omega
  | conversion _admitted _same ih => exact ih

private theorem components_pos (program : Program) : 0 < program.components := by
  induction program with
  | var _ => exact Nat.zero_lt_succ 0
  | app function argument first second =>
      change 0 < function.components + argument.components
      omega

private theorem lookup_argument_rows (arguments : List (String × Ty)) (name : String) :
    List.lookup name (arguments.map fun entry =>
      (entry.1, (.mk entry.1 top [SourceSynthesisCurrentContext.typeNode entry.2] : Row))) =
      (List.lookup name arguments).map
        (fun typ => (.mk name top [SourceSynthesisCurrentContext.typeNode typ] : Row)) := by
  induction arguments with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, typ⟩ := entry
      by_cases same : name = key
      · subst key; simp
      · have different : (name == key) = false := beq_eq_false_iff_ne.mpr same
        simpa only [List.map_cons, List.lookup, different] using ih

private theorem current_singleton (lib : Library) (query : Query) (name : String) (typ : Ty)
    (found : queryLookup query.queryArguments name = some typ) :
    resolveArguments (context lib query) [name] =
      some [(name, (.mk name top [SourceSynthesisCurrentContext.typeNode typ] : Row))] := by
  rw [resolveArguments, SourceSynthesisRelevantSingletonLookup.resolveSelection_singleton]
  change (List.lookup name (((queryBindings query).map fun entry =>
    (entry.1, (.mk entry.1 top [SourceSynthesisCurrentContext.typeNode entry.2] : Row))).reverse)).map
      (fun row => [(name, row)]) =
        some [(name, (.mk name top [SourceSynthesisCurrentContext.typeNode typ] : Row))]
  rw [← List.map_reverse, lookup_argument_rows]
  have canonical : queryLookup (queryBindings query) name = some typ :=
    (queryBindings_lookup query name).trans found
  exact congrArg (fun result : Option Ty =>
    (result.map fun value => (.mk name top [SourceSynthesisCurrentContext.typeNode value] : Row)).map
      fun row => [(name, row)]) canonical

private theorem empty_observer [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ctx : Context) (asArgument : Bool) (size : Nat) (expression : Expression) (body : Term Symbol)
    (member : expression ∈ termsRows ctx asArgument size)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) body) :
    ∀ rows, relevantRows ctx asArgument size [] = .ok rows →
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal (.union rows)) body := by
  intro rows returned
  have resolved : resolveArguments ctx [] = some [] := resolveSelection_empty ctx.argumentEdges
  rw [relevantRows, resolved] at returned
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at returned
  have same := Except.ok.inj returned
  subst rows
  exact union_member (SourceEqualityPCSGuard.holds formulas solver) _ expression body member accepted

private theorem relevant_of_resolved [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool} {program : Program} {typ : Ty}
    {tokens : List (String × Ty)} (unpruned : lib.libraryAvoid = [])
    (eligible : Eligible lib query asArgument program typ tokens) :
    (∃ winner, resolveArguments (context lib query) (tokens.map Prod.fst) = some winner) →
      Typed lib query program typ ∧ ∃ body,
        (∀ rows, relevantRows (context lib query) asArgument program.components (tokens.map Prod.fst) = .ok rows →
          evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal (.union rows)) body) ∧
        body.atPath [0] = some (candidateRigid typ) ∧ Projection literal Prod.fst body program ∧
        toProgram literal Prod.fst body = program ∧
        (toProgram literal Prod.fst body).components = program.components := by
  induction eligible with
  | group asArgument entry binding rho images =>
      intro _resolved
      obtain ⟨ordinary, body, expression, member, accepted, annotation, projected, decoded, counted⟩ :=
        eligible_program_member formulas solver unpruned (.group asArgument entry binding rho images)
      exact ⟨ordinary, body, empty_observer formulas solver _ _ _ expression body member accepted,
        annotation, projected, decoded, counted⟩
  | argumentOnly entry binding rho images =>
      intro _resolved
      obtain ⟨ordinary, body, expression, member, accepted, annotation, projected, decoded, counted⟩ :=
        eligible_program_member formulas solver unpruned (.argumentOnly entry binding rho images)
      exact ⟨ordinary, body, empty_observer formulas solver _ _ _ expression body member accepted,
        annotation, projected, decoded, counted⟩
  | queryArgument asArgument name typ found =>
      intro _resolved
      obtain ⟨ordinary, body, expression, member, accepted, annotation, projected, decoded, counted⟩ :=
        eligible_program_member formulas solver unpruned (.queryArgument asArgument name typ found)
      exact ⟨ordinary, body, empty_observer formulas solver _ _ _ expression body member accepted,
        annotation, projected, decoded, counted⟩
  | queryToken asArgument token typ found =>
      intro _resolved
      let body : Term Symbol := .node (literal token.1) [candidateRigid typ]
      refine ⟨.queryArgument found, body, ?_, rfl, .component _ _, rfl, rfl⟩
      intro rows returned
      have resolved := current_singleton lib query token.1 typ found
      change relevantRows (context lib query) asArgument 1 [token.1] = .ok rows at returned
      rw [relevantRows, resolved] at returned
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at returned
      have same := Except.ok.inj returned
      subst rows
      exact union_member (SourceEqualityPCSGuard.holds formulas solver) _ _ _ List.mem_cons_self
        (SourceSynthesisAnnotatedProgramWitnesses.argument_member formulas solver token.1 (encodeTy typ))
  | @application asArgument function argument domain codomain left right first second result firstIH secondIH =>
      intro current
      by_cases empty : left ++ right = []
      · obtain ⟨ordinary, body, expression, member, accepted, annotation, projected, decoded, counted⟩ :=
          eligible_program_member formulas solver (asArgument := asArgument) unpruned
            (.application first second result)
        have noNames : (left ++ right).map Prod.fst = [] := congrArg (List.map Prod.fst) empty
        refine ⟨ordinary, body, ?_, annotation, projected, decoded, counted⟩
        simpa only [noNames] using
          empty_observer formulas solver _ _ _ expression body member accepted
      · obtain ⟨winner, resolved⟩ := current
        have named : winner.map Prod.fst = left.map Prod.fst ++ right.map Prod.fst := by
          simpa only [List.map_append] using
            (resolveSelection_spec (context lib query).argumentEdges
              ((left ++ right).map Prod.fst) winner resolved).2
        have winnerLength : winner.length = left.length + right.length := by
          have measured := congrArg List.length named
          simpa only [List.length_map, List.length_append] using measured
        have nonempty : winner ≠ [] := by
          intro missing
          have zero : 0 = left.length + right.length := by
            simpa only [missing, List.length_nil] using winnerLength
          have lengthZero : (left ++ right).length = 0 := by
            rw [List.length_append]
            exact zero.symm
          exact empty (List.eq_nil_of_length_eq_zero lengthZero)
        have takeNames : (winner.take left.length).map Prod.fst = left.map Prod.fst := by
          rw [List.map_take, named]
          exact List.take_left' (by simp only [List.length_map])
        have dropNames : (winner.drop left.length).map Prod.fst = right.map Prod.fst := by
          rw [List.map_drop, named]
          exact List.drop_left' (by simp only [List.length_map])
        obtain ⟨leftResolution, rightResolution⟩ := resolveSelection_take_drop
          (context lib query).argumentEdges ((left ++ right).map Prod.fst) winner resolved left.length
        have leftResolves : ∃ child, resolveArguments (context lib query) (left.map Prod.fst) = some child := by
          simpa only [SourceSynthesisFirstOrderConstruction.resolveArguments, takeNames] using leftResolution
        have rightResolves : ∃ child, resolveArguments (context lib query) (right.map Prod.fst) = some child := by
          simpa only [SourceSynthesisFirstOrderConstruction.resolveArguments, dropNames] using rightResolution
        obtain ⟨functionOrdinary, functionBody, functionObserver, functionAnnotation,
            functionProjected, _functionDecoded, _functionCount⟩ := firstIH leftResolves
        obtain ⟨argumentOrdinary, argumentBody, argumentObserver, argumentAnnotation,
            argumentProjected, _argumentDecoded, _argumentCount⟩ := secondIH rightResolves
        have functionType : functionBody.atPath [0] =
            some (.node (literal "->") [marker, candidateRigid domain, candidateRigid codomain]) := by
          simpa only [candidateRigid, encodeTy, SourceSynthesisFiniteTypeWitnesses.rigidTerm] using functionAnnotation
        have enough : winner.length ≤ function.components + argument.components := by
          have leftBound := token_length first
          have rightBound := token_length second
          omega
        have smaller : function.components < function.components + argument.components := by
          have argumentPositive := components_pos argument
          omega
        have offsetBound : left.length ≤ winner.length := by omega
        have remaining : function.components + argument.components - function.components = argument.components := by omega
        have functionAt : ∀ rows,
            relevantRows (context lib query) false function.components
              ((winner.take left.length).map Prod.fst) = .ok rows →
                evaluate (SourceEqualityPCSGuard.holds formulas solver) []
                  (mapSyntax literal (.union rows)) functionBody := by
          simpa only [takeNames] using functionObserver
        have argumentAt : ∀ rows,
            relevantRows (context lib query) true (function.components + argument.components - function.components)
              ((winner.drop left.length).map Prod.fst) = .ok rows →
                evaluate (SourceEqualityPCSGuard.holds formulas solver) []
                  (mapSyntax literal (.union rows)) argumentBody := by
          simpa only [dropNames, remaining] using argumentObserver
        let body : Term Symbol :=
          .node (literal "app") [candidateRigid codomain, marker, functionBody, argumentBody]
        have observer := SourceSynthesisContextApplications.relevant_application_member_at formulas solver
          (context lib query) (constructorCatalog lib query) (context_types lib query) asArgument
          (function.components + argument.components) function.components left.length
          ((left ++ right).map Prod.fst) winner resolved nonempty enough
          (components_pos function) smaller offsetBound (candidateRigid domain) (candidateRigid codomain)
          functionBody argumentBody functionAt argumentAt functionType argumentAnnotation
          ((typeIn_iff_admitted lib query codomain).mpr result)
        have projected : Projection literal Prod.fst body (.app function argument) :=
          .application _ _ functionProjected argumentProjected
        have decoded := projected.toProgram_eq
        exact ⟨.application functionOrdinary argumentOrdinary, body, observer, rfl,
          projected, decoded, congrArg Program.components decoded⟩
  | @conversion _asArgument _program first second _tokens _admitted same ih =>
      intro resolved
      obtain ⟨ordinary, body, observer, annotation, projected, decoded, counted⟩ := ih resolved
      have encoded := (candidateRigid_eq_iff first second).mpr same
      exact ⟨.conversion ordinary same, body, observer, annotation.trans (congrArg some encoded),
        projected, decoded, counted⟩

/-- Current resolution and raw admission construct actual relevant success for the same body. -/
theorem eligible_relevant_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool} {program : Program} {typ : Ty}
    {tokens : List (String × Ty)} (unpruned : lib.libraryAvoid = [])
    (eligible : Eligible lib query asArgument program typ tokens)
    (resolved : ∃ winner, resolveArguments (context lib query) (tokens.map Prod.fst) = some winner) :
    Typed lib query program typ ∧ ∃ body rows,
      relevantRows (context lib query) asArgument program.components (tokens.map Prod.fst) = .ok rows ∧
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal (.union rows)) body ∧
      body.atPath [0] = some (candidateRigid typ) ∧ Projection literal Prod.fst body program ∧
      toProgram literal Prod.fst body = program ∧
      (toProgram literal Prod.fst body).components = program.components := by
  obtain ⟨ordinary, body, observer, annotation, projected, decoded, counted⟩ :=
    relevant_of_resolved formulas solver unpruned eligible resolved
  obtain ⟨rows, returned⟩ := SourceSynthesisFirstOrderTotality.relevantRows_total_of_resolution
    (context lib query) program.components asArgument (tokens.map Prod.fst) resolved
  exact ⟨ordinary, body, rows, returned, observer rows returned, annotation, projected, decoded, counted⟩

private def tokenRow (query : Query) (token : String × Ty) : String × Row :=
  (token.1, .mk token.1 top
    [SourceSynthesisCurrentContext.typeNode ((queryLookup query.queryArguments token.1).getD token.2)])

private theorem token_names (query : Query) (tokens : List (String × Ty)) :
    (tokens.map (tokenRow query)).map Prod.fst = tokens.map Prod.fst := by
  simp only [List.map_map, Function.comp_def, tokenRow]

private theorem covered_permutation {lib : Library} {query : Query} {tokens : List (String × Ty)}
    (covered : tokens.Perm query.queryArguments) :
    tokens.map (tokenRow query) ∈ permutations (context lib query).argumentEdges := by
  apply (permutations_spec _ _).mpr
  have sourceRows : query.queryArguments.map (tokenRow query) = (context lib query).argumentEdges := by
    simp only [SourceSynthesisCurrentContext.context, queryBindings, List.map_map,
      Function.comp_def]
    rfl
  simpa only [sourceRows] using covered.map (tokenRow query)

private theorem covered_resolution {lib : Library} {query : Query} {tokens : List (String × Ty)}
    (covered : tokens.Perm query.queryArguments) :
    ∃ winner, resolveArguments (context lib query) (tokens.map Prod.fst) = some winner := by
  obtain ⟨winner, resolved⟩ := root_lookup_exists (context lib query).argumentEdges
    (tokens.map (tokenRow query)) (covered_permutation (lib := lib) covered)
  exact ⟨winner, by
    simpa only [SourceSynthesisFirstOrderConstruction.resolveArguments, token_names] using resolved⟩

/-- Original token coverage constructs the actual current root and its same Program witness. -/
theorem uses_root_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {program : Program} {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : Eligible lib query true program query.queryGoal tokens)
    (covered : tokens.Perm query.queryArguments) :
    Typed lib query program query.queryGoal ∧ ∃ expression body,
      SourceSynthesisCurrentConstruction.firstOrderRaw lib query (Int.ofNat program.components) = .ok expression ∧
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression)
        (.node (literal "filter") [candidateRigid query.queryGoal, body]) ∧
      (Term.node (literal "filter") [candidateRigid query.queryGoal, body]).atPath [0] =
        some (candidateRigid query.queryGoal) ∧
      Projection literal Prod.fst (.node (literal "filter") [candidateRigid query.queryGoal, body]) program ∧
      toProgram literal Prod.fst (.node (literal "filter") [candidateRigid query.queryGoal, body]) = program ∧
      (toProgram literal Prod.fst (.node (literal "filter") [candidateRigid query.queryGoal, body])).components =
        program.components := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  obtain ⟨ordinary, body, relevantRowsResult, relevantReturned, relevantAccepted,
      annotation, projected, _decoded, _counted⟩ :=
    eligible_relevant_member formulas solver unpruned eligible (covered_resolution covered)
  obtain ⟨expression, returned⟩ := SourceSynthesisCurrentConstruction.firstOrderRaw_total
    lib query (Int.ofNat program.components) (Int.natCast_nonneg program.components)
  have observed := returned
  have allowed : ¬Int.ofNat program.components < 0 := by
    have nonnegative : 0 ≤ Int.ofNat program.components := Int.natCast_nonneg program.components
    omega
  rw [SourceSynthesisCurrentConstruction.firstOrderRaw, ite_eq_right allowed] at observed
  obtain ⟨chunks, chunksReturned, completed⟩ := bind_ok _ _ _ observed
  have same := Except.ok.inj completed
  subst expression
  have runs := SymbolicDriver.mapM_success_all₂ _ _ _ chunksReturned
  obtain ⟨rows, included, rowsReturned⟩ := SymbolicSmartRows.all₂_child _ _ _ runs
    (tokens.map (tokenRow query)) (covered_permutation (lib := lib) covered)
  have currentRows : relevantRows (context lib query) true program.components (tokens.map Prod.fst) = .ok rows := by
    simpa only [Int.ofNat_eq_natCast, Int.toNat_natCast, token_names] using rowsReturned
  have rowsSame : relevantRowsResult = rows := Except.ok.inj (relevantReturned.symm.trans currentRows)
  have acceptedRows : evaluate holds [] (mapSyntax literal (.union rows)) body := by
    simpa only [rowsSame] using relevantAccepted
  rw [mapSyntax, evaluate] at acceptedRows
  obtain ⟨⟨mapped, present⟩, accepted⟩ := acceptedRows
  rw [mapChildren_eq_map] at present
  obtain ⟨candidate, candidateIncluded, rfl⟩ := List.mem_map.mp present
  have candidatesMember := union_member holds _ candidate body
    (List.mem_flatten.mpr ⟨rows, included, candidateIncluded⟩) accepted
  have goalMember := SourceSynthesisCurrentContext.typeNode_member holds
    (SourceEqualityPCSConstructors.top_true formulas solver) query.queryGoal
  have rootMember := SourceSynthesisAnnotatedProgramWitnesses.ofType_member formulas solver
    (.union chunks.flatten) (SourceSynthesisCurrentContext.typeNode query.queryGoal)
    body (candidateRigid query.queryGoal) candidatesMember goalMember annotation
  have rootProjected : Projection literal Prod.fst
      (.node (literal "filter") [candidateRigid query.queryGoal, body]) program := .filter _ projected
  have rootDecoded := rootProjected.toProgram_eq
  exact ⟨ordinary, _, body, returned, rootMember, rfl, rootProjected, rootDecoded,
    congrArg Program.components rootDecoded⟩

end MicroCFTA.SourceSynthesisCurrentRelevantAdmission
