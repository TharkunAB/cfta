import MicroCFTA.SourceSynthesisTypeUniverseMembership
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.SourceEqualityPCSConstructors

/-!
# A finite typed witness for one original FirstOrder request

The library contains f : a. The query supplies x : A and requests B at size
two. The witness assigns Arrow(A,B) to f and satisfies the actual application
and filter constraints. The same closed native build accepts this witness.
These laws do not cover Curried construction or later enumeration outcomes.
-/
namespace MicroCFTA.SourceSynthesisFiniteApplicationWitness
open Language InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard generalize)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges mapChildren_eq_map)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

/-- The original library has one polymorphic component and no pruning rules. -/
def library : Library :=
  { libraryGroups := [("f", .tVar "a", ["f"])]
    libraryArgumentOnly := []
    libraryAvoid := []
    libraryEncoding := .firstOrder }

/-- The query requires the supplied argument x and the rigid result B. -/
def query : Query :=
  { queryArguments := [("x", .tCons "A" [])]
    queryGoal := .tCons "B" [] }

private def types : Expression := typesOf library query
private def argumentRow : Row := .mk "x" top [typeNode top (.tCons "A" [])]
private def functionRow : Row := component types "f" (.tVar "a")

private def firstApplication : Expression :=
  application types (.union [.node [argumentRow], .node [functionRow]])
    (.union [.node [argumentRow]])

private def secondApplication : Expression :=
  application types (.union [.node [argumentRow]])
    (.union [.node [argumentRow], .node [functionRow], .node []])

/-- Both relevant-table argument allocations remain in their source order. -/
def expression : Expression :=
  ofType (.union [firstApplication, secondApplication]) (typeNode top query.queryGoal)

private def a : Term Symbol := .node (literal "A") []
private def b : Term Symbol := .node (literal "B") []
private def marker : Term Symbol := .node (literal "(->)") []
private def arrow : Term Symbol := .node (literal "->") [marker, a, b]
private def functionTerm : Term Symbol := .node (literal "f") [arrow]
private def argumentTerm : Term Symbol := .node (literal "x") [a]
private def applicationTerm : Term Symbol :=
  .node (literal "app") [b, marker, functionTerm, argumentTerm]

/-- The finite witness retains all Type children and both Program components. -/
def witness : Term Symbol := .node (literal "filter") [b, applicationTerm]

/-- The exact original signed request constructs the stated source expression. -/
theorem source_constructs : firstOrderRaw library query 2 = .ok expression := by
  let ctx := context library query
  have arguments : ctx.argumentEdges = [("x", argumentRow)] := rfl
  have emptyKey : resolveArguments ctx [] = some [] :=
    SourceSynthesisSelections.resolveSelection_empty _
  have singleKey : resolveArguments ctx ["x"] = some [("x", argumentRow)] := by
    rw [resolveArguments, arguments]
    simp [SourceSynthesisSelections.resolveSelection, SourceSynthesisSelections.selections,
      SourceSynthesisSelections.subsequences, SourceSynthesisSelections.nonEmptySubsequences,
      SourceSynthesisSelections.permutations_singleton, SourceSynthesisSelections.permutations_nil,
      SourceSynthesisSelections.lookupLast]
  have emptyCell (asArgument : Bool) : relevantRows ctx asArgument 1 [] =
      .ok (termsRows ctx asArgument 1) := by
    rw [relevantRows, emptyKey]
    rfl
  have singleCell (asArgument : Bool) : relevantRows ctx asArgument 1 ["x"] =
      .ok [.node [argumentRow]] := by
    rw [relevantRows, singleKey]
    rfl
  have splits : positiveSplits 2 = [⟨1, by decide⟩] := by decide
  have choices : List.range 2 = [0, 1] := rfl
  have rows : relevantRows ctx true 2 ["x"] =
      .ok [firstApplication, secondApplication] := by
    rw [relevantRows, singleKey]
    simp only [Bind.bind, Except.bind]
    simp [splits, choices, List.mapM_cons, List.mapM_nil, emptyCell, singleCell,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp [termsRows, ctx, context, library, query,
      firstApplication, secondApplication, types, argumentRow, functionRow]
  change Except.bind
    ((SourceSynthesisSelections.permutations ctx.argumentEdges).mapM fun selected =>
      relevantRows ctx true 2 (selected.map Prod.fst))
    (fun rows => .ok (ofType (.union rows.flatten) (typeNode top query.queryGoal))) = .ok expression
  rw [arguments, SourceSynthesisSelections.permutations_singleton]
  simp only [List.mapM_cons, List.mapM_nil, List.map_cons, List.map_nil, rows,
    Bind.bind, Except.bind, Pure.pure, Except.pure,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

private theorem node_member (holds : Guard → Term Symbol → Bool)
    (name : String) (guard : Guard) (children : List Expression) (terms : List (Term Symbol))
    (accepted : forest holds [] (mapChildren literal children) terms)
    (guardHeld : holds guard (.node (literal name) terms) = true) :
    evaluate holds [] (mapSyntax literal (.node [.mk name guard children]))
      (.node (literal name) terms) := by
  simp only [mapSyntax, mapEdges]
  rw [evaluate]
  refine ⟨⟨.mk (literal name) guard (mapChildren literal children), List.mem_cons_self⟩, ?_⟩
  rw [edgeMeaning]
  exact ⟨terms, rfl, accepted, guardHeld⟩

private theorem union_member (holds : Guard → Term Symbol → Bool)
    (members : List Expression) (selected : Expression) (term : Term Symbol)
    (present : selected ∈ members)
    (accepted : evaluate holds [] (mapSyntax literal selected) term) :
    evaluate holds [] (mapSyntax literal (.union members)) term := by
  rw [mapSyntax, evaluate]
  refine ⟨⟨mapSyntax literal selected, ?_⟩, accepted⟩
  rw [mapChildren_eq_map]
  exact List.mem_map.mpr ⟨selected, present, rfl⟩

private theorem application_equalities : EqualityNormalize.Satisfies applicationTerm
    [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]] := by
  simp [EqualityNormalize.Satisfies, EqualityNormalize.ClassSat, PathsEqual, Term.atPath,
    applicationTerm, functionTerm, argumentTerm, arrow]

private theorem filter_equalities : EqualityNormalize.Satisfies witness [[[0], [1, 0]]] := by
  simp [EqualityNormalize.Satisfies, EqualityNormalize.ClassSat, PathsEqual, Term.atPath,
    witness, applicationTerm]

variable [DecidableEq FullSyntax.Formula]

private theorem eqGuard_true (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (classes : EqualityNormalize.Constraints) (term : Term Symbol)
    (satisfied : EqualityNormalize.Satisfies term classes) :
    SourceEqualityPCSGuard.holds formulas solver (eqGuard classes) term = true := by
  apply (SourceEqualityPCSGuard.holds_exact formulas solver (eqGuard classes) term).mpr
  constructor
  · rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
    exact (SourceEqualityPCSGuard.normalize_sat classes term).mpr satisfied
  · exact ((SourceEqualityPCSGuard.holds_exact formulas solver
      SourceEqualityConstraintConstructors.top term).mp
        (SourceEqualityPCSConstructors.top_true formulas solver term)).2

/-- The finite witness satisfies the original source language under the actual PCS evaluator. -/
theorem source_member (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) witness := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  have topHeld : ∀ term, holds top term = true :=
    SourceEqualityPCSConstructors.top_true formulas solver
  let catalog := constructorCatalog library query
  have aPresent : ("A", 0) ∈ catalog := by
    simp [catalog, constructorCatalog, library, query, constructorsOf]
  have bPresent : ("B", 0) ∈ catalog := by
    simp [catalog, constructorCatalog, library, query, constructorsOf]
  have aUniverse : evaluate holds [] (mapSyntax literal (allTypes top catalog)) a :=
    SourceSynthesisTypeUniverseMembership.constructor_member literal holds topHeld catalog "A" []
      aPresent (by intro child member; cases member)
  have bUniverse : evaluate holds [] (mapSyntax literal (allTypes top catalog)) b :=
    SourceSynthesisTypeUniverseMembership.constructor_member literal holds topHeld catalog "B" []
      bPresent (by intro child member; cases member)
  have arrowUniverse : evaluate holds [] (mapSyntax literal (allTypes top catalog)) arrow :=
    SourceSynthesisTypeUniverseMembership.arrow_member literal holds topHeld catalog a b aUniverse bUniverse
  have rigidA : evaluate holds [] (mapSyntax literal (typeNode top (.tCons "A" []))) a := by
    simp only [typeNode]
    exact node_member holds "A" top [] [] (by simp only [mapChildren, forest]) (topHeld _)
  have rigidB : evaluate holds [] (mapSyntax literal (typeNode top (.tCons "B" []))) b := by
    simp only [typeNode]
    exact node_member holds "B" top [] [] (by simp only [mapChildren, forest]) (topHeld _)
  have markerMember : evaluate holds [] (mapSyntax literal (arrowMarker top)) marker :=
    node_member holds "(->)" top [] [] (by simp only [mapChildren, forest]) (topHeld _)
  have functionMember : evaluate holds [] (mapSyntax literal (.node [functionRow])) functionTerm := by
    apply node_member holds "f" top [generalize types (.tVar "a")] [arrow]
    · simp only [mapChildren, forest]
      exact ⟨SourceSynthesisTypeUniverseMembership.generalize_variable_member
        literal holds catalog "a" arrow arrowUniverse, True.intro⟩
    · exact topHeld _
  have argumentMember : evaluate holds [] (mapSyntax literal (.node [argumentRow])) argumentTerm := by
    apply node_member holds "x" top [typeNode top (.tCons "A" [])] [a]
    · simp only [mapChildren, forest]
      exact ⟨rigidA, True.intro⟩
    · exact topHeld _
  have functionChoice : evaluate holds []
      (mapSyntax literal (.union [.node [argumentRow], .node [functionRow]])) functionTerm :=
    union_member holds _ _ _ (List.mem_cons_of_mem _ List.mem_cons_self) functionMember
  have argumentChoice : evaluate holds []
      (mapSyntax literal (.union [.node [argumentRow]])) argumentTerm :=
    union_member holds _ _ _ List.mem_cons_self argumentMember
  have applicationMember : evaluate holds [] (mapSyntax literal firstApplication) applicationTerm := by
    apply node_member holds "app"
      (eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
      [types, arrowMarker top, .union [.node [argumentRow], .node [functionRow]],
        .union [.node [argumentRow]]] [b, marker, functionTerm, argumentTerm]
    · simp only [mapChildren, forest]
      exact ⟨bUniverse, markerMember, functionChoice, argumentChoice, True.intro⟩
    · exact eqGuard_true formulas solver _ applicationTerm application_equalities
  have candidateMember : evaluate holds []
      (mapSyntax literal (.union [firstApplication, secondApplication])) applicationTerm :=
    union_member holds _ _ _ List.mem_cons_self applicationMember
  apply node_member holds "filter" (eqGuard [[[0], [1, 0]]])
    [typeNode top query.queryGoal, .union [firstApplication, secondApplication]] [b, applicationTerm]
  · simp only [mapChildren, forest]
    exact ⟨rigidB, candidateMember, True.intro⟩
  · exact eqGuard_true formulas solver _ witness filter_equalities

/-- The same actual original build accepts the finite witness in every ambient environment. -/
theorem build_member [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value witness := by
  have mapped : InternedFreshOrdinaryConstruction.build (mapSyntax literal expression) [] empty =
      .done value heap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  rw [InternedGuardedExecution.closed_language _ value heap mapped
    (SourceEqualityPCSGuard.holds formulas solver) ambient]
  exact source_member formulas solver

/-- Closed construction produces an actual native value with this joint finite witness. -/
theorem native_witness [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ (value : Value Symbol Guard) (heap : State Symbol Guard),
      InternedFreshOrdinaryConstruction.build
        (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap ∧
      ∀ ambient, InternedGuardedLanguage.meaning
        (SourceEqualityPCSGuard.holds formulas solver) ambient value witness := by
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete
    (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression)
  exact ⟨value, heap, built, fun ambient => build_member formulas solver value heap built ambient⟩

end MicroCFTA.SourceSynthesisFiniteApplicationWitness
