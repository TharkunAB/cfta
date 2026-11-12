import MicroCFTA.SourceSynthesisSourceTermsTyping
import MicroCFTA.SymbolicSmartRows

/-!
# Actual source results for relevant Program derivations

A source-admissible derivation belongs to each actual successful relevant
result. The proof retains the source resolver winner and the successful
split and offset traversal outputs. Recursive calls resolve the take/drop
names again. The root theorem retains the actual permutation result.

The output equations identify successful results. They do not prove lookup
or all-mapM totality. Ordinary well-typedness does not yet supply a source
admissible derivation. Its universe, pruning, role, and winner conditions
remain separate specification obligations. Curried construction and native
execution correspondence are outside these FirstOrder syntax laws.
-/
namespace MicroCFTA.SourceSynthesisSourceRelevantTyping
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisFiniteTypeWitnesses (rigidTerm)
open SourceSynthesisProgramTermSize (Program Projection)
open SourceSynthesisSourceTermsTyping (TermsTyping RelevantTyping)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren_eq_map)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

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

private theorem positiveSplits_complete (size left : Nat) (positive : 0 < left) (smaller : left < size) :
    ∃ split ∈ positiveSplits size, split.val = left := by
  let index : Fin (size-1) := ⟨left-1, by omega⟩
  refine ⟨⟨left, positive, smaller⟩, ?_, rfl⟩
  apply List.mem_map.mpr
  refine ⟨index, List.mem_finRange index, ?_⟩
  apply Subtype.ext
  change left-1+1 = left
  omega

variable [DecidableEq FullSyntax.Formula]

/-- A relevant derivation belongs to the union of the actual returned rows. -/
theorem relevantRows_member (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {lib : Library} {query : Query}
    {asArgument : Bool} {size : Nat} {names : List String} {program : Program}
    {annotation term : Term Symbol}
    (typed : RelevantTyping lib query asArgument size names program annotation term)
    (rows : List Expression)
    (returned : relevantRows (context lib query) asArgument size names = .ok rows) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal (.union rows)) term := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  induction typed generalizing rows with
  | @empty asArgument size names program annotation term resolved typed =>
      rw [relevantRows, resolved] at returned
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at returned
      have same := Except.ok.inj returned
      subst rows
      obtain ⟨expression, included, accepted⟩ := TermsTyping.member formulas solver typed
      exact union_member holds _ expression term included accepted
  | @singleton asArgument names name typ resolved =>
      rw [relevantRows, resolved] at returned
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at returned
      have same := Except.ok.inj returned
      subst rows
      exact union_member holds _ _ _ List.mem_cons_self
        (SourceSynthesisAnnotatedProgramWitnesses.argument_member formulas solver name typ)
  | @split asArgument size left offset names arguments functionProgram argumentProgram
      domain codomain functionTerm argumentTerm resolved nonempty enough positive smaller offsetBound
      function argument result firstIH secondIH =>
      rw [relevantRows] at returned
      simp only [resolved] at returned
      obtain ⟨actual, actualResult, computed⟩ := bind_ok _ _ _ returned
      have same := Except.ok.inj actualResult
      subst actual
      split at computed
      · contradiction
      · omega
      · split at computed
        · omega
        · obtain ⟨chunks, chunksResult, flattened⟩ := bind_ok _ _ _ computed
          have same := Except.ok.inj flattened
          subst rows
          obtain ⟨split, splitIncluded, splitValue⟩ := positiveSplits_complete size left positive smaller
          have splitRuns := SymbolicDriver.mapM_success_all₂ _ _ _ chunksResult
          obtain ⟨choices, choicesIncluded, choicesResult⟩ :=
            SymbolicSmartRows.all₂_child _ _ _ splitRuns split splitIncluded
          have offsetRuns := SymbolicDriver.mapM_success_all₂ _ _ _ choicesResult
          have offsetIncluded : offset ∈ List.range (arguments.length+1) := List.mem_range.mpr (by omega)
          obtain ⟨expression, expressionIncluded, expressionResult⟩ :=
            SymbolicSmartRows.all₂_child _ _ _ offsetRuns offset offsetIncluded
          obtain ⟨functionRows, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
          obtain ⟨argumentRows, argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
          have same := Except.ok.inj completed
          subst expression
          have functionMember := firstIH functionRows (by simpa only [splitValue] using functionResult)
          have argumentMember := secondIH argumentRows (by simpa only [splitValue] using argumentResult)
          have built := SourceSynthesisAnnotatedProgramWitnesses.application_member formulas solver
            (constructorCatalog lib query) (.union functionRows) (.union argumentRows)
            functionTerm argumentTerm domain codomain functionMember argumentMember
            function.shape.1 argument.shape.1 result
          exact union_member holds _ _ _
            (List.mem_flatten.mpr ⟨choices, choicesIncluded, expressionIncluded⟩) built

/-- A source root derivation has actual filter membership and its existing Program projection. -/
theorem firstOrderRaw_member (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {lib : Library} {query : Query}
    {size : Int} {expression : Expression} {program : Program} {body : Term Symbol}
    (returned : firstOrderRaw lib query size = .ok expression)
    (selected : List (String × Row))
    (permutation : selected ∈ SourceSynthesisSelections.permutations (context lib query).argumentEdges)
    (typed : RelevantTyping lib query true size.toNat (selected.map Prod.fst)
      program (rigidTerm query.queryGoal) body) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression)
      (.node (literal "filter") [rigidTerm query.queryGoal, body]) ∧
    Projection literal Prod.fst (.node (literal "filter") [rigidTerm query.queryGoal, body]) program ∧
    program.components = size.toNat := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  unfold firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    have same := Except.ok.inj completed
    subst expression
    have runs := SymbolicDriver.mapM_success_all₂ _ _ _ chunksResult
    obtain ⟨rows, included, rowsResult⟩ :=
      SymbolicSmartRows.all₂_child _ _ _ runs selected permutation
    have accepted := relevantRows_member formulas solver typed rows rowsResult
    have candidatesMember : evaluate holds [] (mapSyntax literal (.union chunks.flatten)) body := by
      rw [mapSyntax, evaluate] at accepted
      obtain ⟨⟨mapped, present⟩, checked⟩ := accepted
      rw [mapChildren_eq_map] at present
      obtain ⟨candidate, candidateIncluded, rfl⟩ := List.mem_map.mp present
      exact union_member holds _ candidate body
        (List.mem_flatten.mpr ⟨rows, included, candidateIncluded⟩) checked
    have goalMember := SourceSynthesisFiniteTypeWitnesses.typeNode_member holds
      (SourceEqualityPCSConstructors.top_true formulas solver) query.queryGoal
    exact ⟨SourceSynthesisAnnotatedProgramWitnesses.ofType_member formulas solver
      (.union chunks.flatten) (typeNode top query.queryGoal) body (rigidTerm query.queryGoal)
      candidatesMember goalMember typed.shape.1,
      .filter _ typed.shape.2.1, typed.shape.2.2⟩

end MicroCFTA.SourceSynthesisSourceRelevantTyping
