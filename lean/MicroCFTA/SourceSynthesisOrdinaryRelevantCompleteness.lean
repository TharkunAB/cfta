import MicroCFTA.SourceSynthesisOrdinaryProgramCompleteness
import MicroCFTA.SourceSynthesisRelevantSingletonLookup
import MicroCFTA.SourceSynthesisFirstOrderTotality

/-!
# Admitted ordinary Programs with required query-token coverage

Marked leaves discharge input tokens. Their actual types come from ordinary
last query lookup. Unmarked subtrees can contain additional query uses.
Token permutation coverage preserves duplicate multiplicities. Child calls
resolve the names of each actual winner's take/drop slices again.

The laws derive source membership and constructor success. They do not assume
source typing, future rows, or successful outputs. Empty avoid remains explicit.
Ordinary typing, the public input domain, and per-use admission stay separate.
Component counts do not bound type annotations or establish native execution.
-/
namespace MicroCFTA.SourceSynthesisOrdinaryRelevantCompleteness
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (top)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed Equivalent queryLookup equivalent_rigidTerm)
open SourceSynthesisOrdinaryProgramCompleteness (ProgramEligible eligible_program_terms)
open SourceSynthesisRelevantSingletonLookup (queryLookup_resolve_singleton)
open SourceSynthesisSourceTermsTyping (RelevantTyping)
open SourceSynthesisSelections (resolveSelection_empty resolveSelection_spec root_lookup_exists)
open SourceSynthesisSelectionClosure (permutations_spec resolveSelection_take_drop)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren_eq_map)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

/-- Record ordinary admission and the ordered input tokens discharged by marked query leaves. -/
inductive UsesEligible (lib : Library) (query : Query) :
    Bool → Program → Ty → List (String × Ty) → Prop where
  | unmarked {asArgument : Bool} {program : Program} {typ : Ty}
      (admitted : ProgramEligible lib query asArgument program typ) :
      UsesEligible lib query asArgument program typ []
  | queryArgument {asArgument : Bool} {typ : Ty} (token : String × Ty)
      (found : queryLookup query.queryArguments token.1 = some typ) :
      UsesEligible lib query asArgument (.var token.1) typ [token]
  | application {asArgument : Bool} {function argument : Program} {domain codomain : Ty}
      {left right : List (String × Ty)}
      (first : UsesEligible lib query false function (.tFun domain codomain) left)
      (second : UsesEligible lib query true argument domain right)
      (result : TypeIn (constructorCatalog lib query) (rigidTerm codomain)) :
      UsesEligible lib query asArgument (.app function argument) codomain (left ++ right)
  | conversion {asArgument : Bool} {program : Program} {first second : Ty}
      {tokens : List (String × Ty)}
      (admitted : UsesEligible lib query asArgument program first tokens)
      (same : Equivalent first second) :
      UsesEligible lib query asArgument program second tokens

private def tokenRow (token : String × Ty) : String × Row :=
  (token.1, .mk token.1 top [typeNode top token.2])

private theorem token_names (tokens : List (String × Ty)) :
    (tokens.map tokenRow).map Prod.fst = tokens.map Prod.fst := by
  simp only [List.map_map, Function.comp_def, tokenRow]

private theorem covered_permutation {lib : Library} {query : Query} {tokens : List (String × Ty)}
    (covered : tokens.Perm query.queryArguments) :
    tokens.map tokenRow ∈ SourceSynthesisSelections.permutations (context lib query).argumentEdges := by
  apply (permutations_spec _ _).mpr
  change (tokens.map tokenRow).Perm (query.queryArguments.map tokenRow)
  exact covered.map tokenRow

private theorem covered_resolution {lib : Library} {query : Query} {tokens : List (String × Ty)}
    (covered : tokens.Perm query.queryArguments) :
    ∃ winner, resolveArguments (context lib query) (tokens.map Prod.fst) = some winner := by
  obtain ⟨winner, resolved⟩ := root_lookup_exists (context lib query).argumentEdges
    (tokens.map tokenRow) (covered_permutation (lib := lib) covered)
  exact ⟨winner, by
    simpa only [SourceSynthesisFirstOrderConstruction.resolveArguments, token_names] using resolved⟩

private theorem ordinary_admission {lib : Library} {query : Query} {asArgument : Bool}
    {program : Program} {typ : Ty} {tokens : List (String × Ty)}
    (eligible : UsesEligible lib query asArgument program typ tokens) :
    ProgramEligible lib query asArgument program typ := by
  induction eligible with
  | unmarked admitted => exact admitted
  | queryArgument token found => exact .leaf (.queryArgument found)
  | application first second result firstIH secondIH => exact .application firstIH secondIH result
  | conversion admitted same ih => exact .conversion ih same

private theorem token_length {lib : Library} {query : Query} {asArgument : Bool}
    {program : Program} {typ : Ty} {tokens : List (String × Ty)}
    (eligible : UsesEligible lib query asArgument program typ tokens) :
    tokens.length ≤ program.components := by
  induction eligible with
  | unmarked admitted => exact Nat.zero_le _
  | queryArgument token found => exact Nat.le_refl 1
  | application first second result firstIH secondIH =>
      simp only [List.length_append, Program.components]
      omega
  | conversion admitted same ih => exact ih

private theorem components_pos (program : Program) : 0 < program.components := by
  induction program with
  | var _name => exact Nat.zero_lt_succ 0
  | app function argument first second =>
      change 0 < function.components + argument.components
      omega

private theorem relevant_of_resolved {lib : Library} {query : Query} {asArgument : Bool}
    {program : Program} {typ : Ty} {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : UsesEligible lib query asArgument program typ tokens) :
    (∃ winner, resolveArguments (context lib query) (tokens.map Prod.fst) = some winner) →
      Typed lib query program typ ∧
        ∃ body, RelevantTyping lib query asArgument program.components (tokens.map Prod.fst)
          program (rigidTerm typ) body := by
  induction eligible with
  | @unmarked asArgument program typ admitted =>
      intro _resolved
      obtain ⟨ordinary, body, source⟩ := eligible_program_terms unpruned admitted
      exact ⟨ordinary, body, .empty (resolveSelection_empty (context lib query).argumentEdges) source⟩
  | @queryArgument asArgument typ token found =>
      intro _resolved
      exact ⟨.queryArgument found, .node (literal token.1) [rigidTerm typ],
        .singleton token.1 typ (queryLookup_resolve_singleton lib query token.1 typ found)⟩
  | @application asArgument function argument domain codomain left right first second result firstIH secondIH =>
      intro current
      by_cases empty : left ++ right = []
      · obtain ⟨ordinary, body, source⟩ := eligible_program_terms (asArgument := asArgument) unpruned
          (.application (ordinary_admission first) (ordinary_admission second) result)
        have noNames : (left ++ right).map Prod.fst = [] := congrArg (List.map Prod.fst) empty
        have resolved : resolveArguments (context lib query) ((left ++ right).map Prod.fst) = some [] := by
          rw [noNames]
          exact resolveSelection_empty (context lib query).argumentEdges
        exact ⟨ordinary, body, .empty resolved source⟩
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
        obtain ⟨functionOrdinary, functionTerm, functionSource⟩ := firstIH leftResolves
        obtain ⟨argumentOrdinary, argumentTerm, argumentSource⟩ := secondIH rightResolves
        simp only [rigidTerm] at functionSource
        have functionPositive := components_pos function
        have argumentPositive := components_pos argument
        have enough : winner.length ≤ function.components + argument.components := by
          have leftBound := token_length first
          have rightBound := token_length second
          omega
        have smaller : function.components < function.components + argument.components := by omega
        have offsetBound : left.length ≤ winner.length := by omega
        have remaining : function.components + argument.components - function.components =
            argument.components := by omega
        have functionAt : RelevantTyping lib query false function.components
            ((winner.take left.length).map Prod.fst) function
            (.node (literal "->") [marker, rigidTerm domain, rigidTerm codomain]) functionTerm := by
          simpa only [takeNames] using functionSource
        have argumentAt : RelevantTyping lib query true
            (function.components + argument.components - function.components)
            ((winner.drop left.length).map Prod.fst) argument (rigidTerm domain) argumentTerm := by
          simpa only [dropNames, remaining] using argumentSource
        let body : Term Symbol :=
          .node (literal "app") [rigidTerm codomain, marker, functionTerm, argumentTerm]
        have source : RelevantTyping lib query asArgument (function.components + argument.components)
            ((left ++ right).map Prod.fst) (.app function argument) (rigidTerm codomain) body :=
          .split (left := function.components) (offset := left.length) resolved nonempty enough
            functionPositive smaller offsetBound functionAt argumentAt result
        exact ⟨.application functionOrdinary argumentOrdinary, body, source⟩
  | @conversion asArgument program first second tokens admitted same ih =>
      intro resolved
      obtain ⟨ordinary, body, source⟩ := ih resolved
      refine ⟨.conversion ordinary same, body, ?_⟩
      have encoded := equivalent_rigidTerm first second same
      simpa only [encoded] using source

private theorem covered_relevant {lib : Library} {query : Query} {asArgument : Bool}
    {program : Program} {typ : Ty} {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : UsesEligible lib query asArgument program typ tokens)
    (covered : tokens.Perm query.queryArguments) :
    Typed lib query program typ ∧
      ∃ body, RelevantTyping lib query asArgument program.components (tokens.map Prod.fst)
        program (rigidTerm typ) body :=
  relevant_of_resolved unpruned eligible (covered_resolution covered)

/-- Token coverage constructs membership in an actual relevant row for the same typed Program term. -/
theorem uses_relevant_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool} {program : Program} {typ : Ty}
    {tokens : List (String × Ty)} (unpruned : lib.libraryAvoid = [])
    (eligible : UsesEligible lib query asArgument program typ tokens)
    (covered : tokens.Perm query.queryArguments) :
    Typed lib query program typ ∧
      ∃ body rows expression,
        relevantRows (context lib query) asArgument program.components (tokens.map Prod.fst) = .ok rows ∧
        expression ∈ rows ∧
        evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) body ∧
        body.atPath [0] = some (rigidTerm typ) ∧ Projection literal Prod.fst body program ∧
        toProgram literal Prod.fst body = program ∧
        (toProgram literal Prod.fst body).components = program.components := by
  obtain ⟨ordinary, body, source⟩ := covered_relevant unpruned eligible covered
  obtain ⟨rows, returned⟩ := SourceSynthesisFirstOrderTotality.relevantRows_total_of_resolution
    (context lib query) program.components asArgument (tokens.map Prod.fst) (covered_resolution covered)
  have accepted := SourceSynthesisSourceRelevantTyping.relevantRows_member formulas solver source rows returned
  rw [mapSyntax, evaluate] at accepted
  obtain ⟨⟨mapped, present⟩, checked⟩ := accepted
  rw [mapChildren_eq_map] at present
  obtain ⟨expression, included, rfl⟩ := List.mem_map.mp present
  obtain ⟨annotation, projected, _count⟩ := source.shape
  have decoded := projected.toProgram_eq
  exact ⟨ordinary, body, rows, expression, returned, included, checked, annotation, projected,
    decoded, congrArg Program.components decoded⟩

/-- Covered tokens construct actual root success, filter membership, projection, and decoded count. -/
theorem uses_root_member [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {program : Program} {tokens : List (String × Ty)}
    (unpruned : lib.libraryAvoid = [])
    (eligible : UsesEligible lib query true program query.queryGoal tokens)
    (covered : tokens.Perm query.queryArguments) :
    Typed lib query program query.queryGoal ∧
      ∃ expression body,
        firstOrderRaw lib query (Int.ofNat program.components) = .ok expression ∧
        evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression)
          (.node (literal "filter") [rigidTerm query.queryGoal, body]) ∧
        (Term.node (literal "filter") [rigidTerm query.queryGoal, body]).atPath [0] =
          some (rigidTerm query.queryGoal) ∧
        Projection literal Prod.fst (.node (literal "filter") [rigidTerm query.queryGoal, body]) program ∧
        toProgram literal Prod.fst (.node (literal "filter") [rigidTerm query.queryGoal, body]) = program ∧
        (toProgram literal Prod.fst (.node (literal "filter") [rigidTerm query.queryGoal, body])).components =
          program.components := by
  obtain ⟨ordinary, body, source⟩ := covered_relevant unpruned eligible covered
  have permutation := covered_permutation (lib := lib) covered
  have sizeToNat : (Int.ofNat program.components).toNat = program.components :=
    Int.toNat_natCast program.components
  have nonnegative : 0 ≤ Int.ofNat program.components := Int.natCast_nonneg program.components
  have sourceAtRoot : RelevantTyping lib query true (Int.ofNat program.components).toNat
      ((tokens.map tokenRow).map Prod.fst) program (rigidTerm query.queryGoal) body := by
    simpa only [token_names, sizeToNat] using source
  obtain ⟨expression, returned, accepted, projected, _count⟩ :=
    SourceSynthesisFirstOrderTotality.firstOrderRaw_member_total formulas solver
      (Int.ofNat program.components) nonnegative (tokens.map tokenRow) permutation program body sourceAtRoot
  have decoded := projected.toProgram_eq
  exact ⟨ordinary, expression, body, returned, accepted, rfl, projected, decoded,
    congrArg Program.components decoded⟩

end MicroCFTA.SourceSynthesisOrdinaryRelevantCompleteness
