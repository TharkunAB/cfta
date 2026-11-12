import MicroCFTA.SourceSynthesisAnnotatedProgramWitnesses
import MicroCFTA.SourceSynthesisFirstOrderTotality
import MicroCFTA.SymbolicSmartRows

/-!
# Application membership at the actual source context

The existing row evaluators retain the selected split, offset, and child keys.
Both laws preserve the supplied child terms and the literal application term.
No source typing judgment or row algorithm is added. Source construction
totality remains separate from native execution and enumeration completion.
-/
namespace MicroCFTA.SourceSynthesisContextApplications
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax (allTypes)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction
  (Context Expression Row application without termsRows relevantRows resolveArguments positiveSplits)
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren_eq_map)
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

private theorem positiveSplits_complete (size left : Nat) (positive : 0 < left) (smaller : left < size) :
    ∃ split ∈ positiveSplits size, split.val = left := by
  let index : Fin (size-1) := ⟨left-1, by omega⟩
  refine ⟨⟨left, positive, smaller⟩, ?_, rfl⟩
  apply List.mem_map.mpr
  refine ⟨index, List.mem_finRange index, ?_⟩
  apply Subtype.ext
  change left-1+1 = left
  omega

private theorem termsRows_large (ctx : Context) (asArgument : Bool) (size : Nat) (large : 3 ≤ size) :
    termsRows ctx asArgument size = (positiveSplits size).map fun split =>
      application ctx.types (.union (termsRows ctx false split.val))
        (.union (termsRows ctx true (size-split.val))) := by
  obtain ⟨rest, same⟩ : ∃ rest, size = rest+3 := ⟨size-3, by omega⟩
  subst size
  rw [termsRows]

/-- Actual terms children produce the same application term at their combined source size. -/
theorem terms_application_member_at [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ctx : Context) (catalog : List (String × Nat))
    (types : ctx.types = allTypes top catalog) (unpruned : ctx.avoid = [])
    (asArgument : Bool) (left right : Nat) (leftPos : 0 < left) (rightPos : 0 < right)
    (domain codomain functionTerm argumentTerm : Term Symbol)
    (function : ∃ expression ∈ termsRows ctx false left,
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) functionTerm)
    (argument : ∃ expression ∈ termsRows ctx true right,
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) argumentTerm)
    (functionType : functionTerm.atPath [0] =
      some (.node (literal "->") [marker, domain, codomain]))
    (argumentType : argumentTerm.atPath [0] = some domain)
    (result : TypeIn catalog codomain) :
    ∃ expression ∈ termsRows ctx asArgument (left + right),
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression)
        (.node (literal "app") [codomain, marker, functionTerm, argumentTerm]) := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  obtain ⟨functionExpression, functionIncluded, functionMember⟩ := function
  obtain ⟨argumentExpression, argumentIncluded, argumentMember⟩ := argument
  by_cases two : left + right = 2
  · have leftOne : left = 1 := by omega
    have rightOne : right = 1 := by omega
    let fallbackFunction : Expression :=
      .union [without ctx (ctx.avoid.flatMap Prod.fst), .node (ctx.argumentEdges.map Prod.snd)]
    have functionUnion : evaluate holds [] (mapSyntax literal fallbackFunction) functionTerm := by
      have base : functionExpression ∈
          [.node (ctx.argumentEdges.map Prod.snd), .node (ctx.components.map Prod.snd)] := by
        simpa [SourceSynthesisFirstOrderConstruction.termsRows_one, leftOne] using functionIncluded
      simp only [List.mem_cons, List.not_mem_nil, or_false] at base
      rcases base with rfl | rfl
      · exact union_member holds _ _ _ (by simp) functionMember
      · have same : without ctx (ctx.avoid.flatMap Prod.fst) = .node (ctx.components.map Prod.snd) := by
          simp [without, unpruned]
          exact congrArg (List.map Prod.snd)
            (show ctx.components.filter (fun _ => true) = ctx.components from
              List.filter_eq_self.mpr (by intro _ _; rfl))
        exact union_member holds _ (without ctx (ctx.avoid.flatMap Prod.fst)) _ (by simp)
          (by simpa only [same] using functionMember)
    have argumentUnion : evaluate holds []
        (mapSyntax literal (.union (termsRows ctx true 1))) argumentTerm :=
      union_member holds _ argumentExpression _
        (by simpa only [rightOne] using argumentIncluded) argumentMember
    have outer : termsRows ctx asArgument 2 =
        [application ctx.types fallbackFunction (.union (termsRows ctx true 1))] := by
      conv => lhs; rw [termsRows]
      simp only [fallbackFunction, unpruned, List.filterMap_nil, List.nil_append]
    refine ⟨application ctx.types fallbackFunction (.union (termsRows ctx true 1)), ?_, ?_⟩
    · rw [two, outer]
      exact List.mem_singleton.mpr rfl
    · simpa only [types] using
        (SourceSynthesisAnnotatedProgramWitnesses.application_member formulas solver catalog
          fallbackFunction (.union (termsRows ctx true 1)) functionTerm argumentTerm domain codomain
          functionUnion argumentUnion functionType argumentType result)
  · have large : 3 ≤ left + right := by omega
    have smaller : left < left + right := by omega
    obtain ⟨split, included, same⟩ := positiveSplits_complete (left+right) left leftPos smaller
    have functionUnion := union_member holds _ functionExpression _ functionIncluded functionMember
    have argumentUnion := union_member holds _ argumentExpression _ argumentIncluded argumentMember
    let expression : Expression := application ctx.types
      (.union (termsRows ctx false left)) (.union (termsRows ctx true right))
    refine ⟨expression, ?_, ?_⟩
    · rw [termsRows_large ctx asArgument (left+right) large]
      apply List.mem_map.mpr
      refine ⟨split, included, ?_⟩
      have remaining : left+right-left = right := by omega
      simp only [expression, same, remaining]
    · simpa only [expression, types] using
        (SourceSynthesisAnnotatedProgramWitnesses.application_member formulas solver catalog
          (.union (termsRows ctx false left)) (.union (termsRows ctx true right))
          functionTerm argumentTerm domain codomain functionUnion argumentUnion
          functionType argumentType result)

/-- The actual resolved split and offset retain the same application term in every returned row union. -/
theorem relevant_application_member_at [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ctx : Context) (catalog : List (String × Nat)) (types : ctx.types = allTypes top catalog)
    (asArgument : Bool) (size left offset : Nat) (names : List String)
    (winner : List (String × Row)) (resolved : resolveArguments ctx names = some winner)
    (nonempty : winner ≠ []) (enough : winner.length ≤ size)
    (positive : 0 < left) (smaller : left < size) (offsetBound : offset ≤ winner.length)
    (domain codomain functionTerm argumentTerm : Term Symbol)
    (function : ∀ rows,
      relevantRows ctx false left ((winner.take offset).map Prod.fst) = .ok rows →
        evaluate (SourceEqualityPCSGuard.holds formulas solver) []
          (mapSyntax literal (.union rows)) functionTerm)
    (argument : ∀ rows,
      relevantRows ctx true (size-left) ((winner.drop offset).map Prod.fst) = .ok rows →
        evaluate (SourceEqualityPCSGuard.holds formulas solver) []
          (mapSyntax literal (.union rows)) argumentTerm)
    (functionType : functionTerm.atPath [0] =
      some (.node (literal "->") [marker, domain, codomain]))
    (argumentType : argumentTerm.atPath [0] = some domain) (result : TypeIn catalog codomain) :
    ∀ rows, relevantRows ctx asArgument size names = .ok rows →
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal (.union rows))
        (.node (literal "app") [codomain, marker, functionTerm, argumentTerm]) := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  obtain ⟨actualRows, actualReturned⟩ :=
    SourceSynthesisFirstOrderTotality.relevantRows_total_of_resolution ctx size asArgument names
      ⟨winner, resolved⟩
  have accepted : evaluate holds [] (mapSyntax literal (.union actualRows))
      (.node (literal "app") [codomain, marker, functionTerm, argumentTerm]) := by
    have returned := actualReturned
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
        subst actualRows
        obtain ⟨split, splitIncluded, splitValue⟩ := positiveSplits_complete size left positive smaller
        have splitRuns := SymbolicDriver.mapM_success_all₂ _ _ _ chunksResult
        obtain ⟨choices, choicesIncluded, choicesResult⟩ :=
          SymbolicSmartRows.all₂_child _ _ _ splitRuns split splitIncluded
        have offsetRuns := SymbolicDriver.mapM_success_all₂ _ _ _ choicesResult
        have offsetIncluded : offset ∈ List.range (winner.length+1) := List.mem_range.mpr (by omega)
        obtain ⟨expression, expressionIncluded, expressionResult⟩ :=
          SymbolicSmartRows.all₂_child _ _ _ offsetRuns offset offsetIncluded
        obtain ⟨functionRows, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
        obtain ⟨argumentRows, argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
        have same := Except.ok.inj completed
        subst expression
        have functionMember := function functionRows (by simpa only [splitValue] using functionResult)
        have argumentMember := argument argumentRows (by simpa only [splitValue] using argumentResult)
        have built : evaluate holds []
            (mapSyntax literal (application ctx.types (.union functionRows) (.union argumentRows)))
            (.node (literal "app") [codomain, marker, functionTerm, argumentTerm]) := by
          simpa only [types] using
            (SourceSynthesisAnnotatedProgramWitnesses.application_member formulas solver catalog
              (.union functionRows) (.union argumentRows) functionTerm argumentTerm domain codomain
              functionMember argumentMember functionType argumentType result)
        exact union_member holds _ _ _
          (List.mem_flatten.mpr ⟨choices, choicesIncluded, expressionIncluded⟩) built
  intro rows returned
  have same : actualRows = rows := Except.ok.inj (actualReturned.symm.trans returned)
  simpa only [same] using accepted

end MicroCFTA.SourceSynthesisContextApplications
