import MicroCFTA.SourceSynthesisSelectionClosure
import MicroCFTA.SourceSynthesisSourceRelevantTyping
import MicroCFTA.SymbolicNormalizationTotal

/-!
# Total source construction at nonnegative sizes

Every actual resolved winner supplies valid take/drop lookup keys.
The size induction covers every split and offset, including unused rows.
Construction success does not imply that the resulting language is inhabited.
Ordinary typing admissibility and native execution remain separate.
-/
namespace MicroCFTA.SourceSynthesisFirstOrderTotality
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisSelections
open SourceSynthesisSelectionClosure

/-- A current resolved key supplies every actual recursive table lookup. -/
theorem relevantRows_total_of_resolution (ctx : Context) (size : Nat) :
    ∀ (asArgument : Bool) (names : List String),
      (∃ winner, resolveArguments ctx names = some winner) →
      ∃ rows, relevantRows ctx asArgument size names = .ok rows := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro asArgument names resolved
      obtain ⟨winner, resolved⟩ := resolved
      have selected := (resolveSelection_spec ctx.argumentEdges names winner resolved).1
      let offsetAction (split : {left : Nat // 0 < left ∧ left < size}) (offset : Nat) :
          Except MissingKey Expression := do
        let function ← relevantRows ctx false split.val ((winner.take offset).map Prod.fst)
        let argument ← relevantRows ctx true (size - split.val) ((winner.drop offset).map Prod.fst)
        pure (application ctx.types (.union function) (.union argument))
      let splitAction (split : {left : Nat // 0 < left ∧ left < size}) :
          Except MissingKey (List Expression) := do
        let choices ← (List.range (winner.length + 1)).mapM (offsetAction split)
        pure choices
      have splitTotal : ∀ split ∈ positiveSplits size, ∃ choices, splitAction split = .ok choices := by
        intro split _included
        obtain ⟨choices, choicesRun⟩ := SymbolicDriver.pure_mapM_total (offsetAction split)
          (List.range (winner.length + 1)) (by
            intro offset _included
            have leftSelected := take_mem_selections ctx.argumentEdges winner selected offset
            have rightSelected := drop_mem_selections ctx.argumentEdges winner selected offset
            obtain ⟨leftWinner, leftResolved⟩ := resolveSelection_exists _ _ leftSelected
            obtain ⟨rightWinner, rightResolved⟩ := resolveSelection_exists _ _ rightSelected
            obtain ⟨functionRows, functionRun⟩ := ih split.val split.property.2 false
              ((winner.take offset).map Prod.fst) ⟨leftWinner, leftResolved⟩
            have smaller : size - split.val < size := by
              have bounds := split.property
              omega
            obtain ⟨argumentRows, argumentRun⟩ := ih (size - split.val) smaller true
              ((winner.drop offset).map Prod.fst) ⟨rightWinner, rightResolved⟩
            refine ⟨application ctx.types (.union functionRows) (.union argumentRows), ?_⟩
            simp only [offsetAction, functionRun, argumentRun, Bind.bind, Except.bind,
              Pure.pure, Except.pure])
        refine ⟨choices, ?_⟩
        simp only [splitAction, choicesRun]
      obtain ⟨chunks, chunksRun⟩ := SymbolicDriver.pure_mapM_total splitAction (positiveSplits size) splitTotal
      rw [relevantRows, resolved]
      simp only [Bind.bind, Except.bind]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨[], rfl⟩
        · refine ⟨chunks.flatten, ?_⟩
          change (positiveSplits size).mapM splitAction >>= _ = _
          rw [chunksRun]
          rfl

/-- Source cell success is equivalent to resolution of its current names key. -/
theorem relevantRows_ok_iff_resolves (ctx : Context) (asArgument : Bool) (size : Nat)
    (names : List String) :
    (∃ rows, relevantRows ctx asArgument size names = .ok rows) ↔
      ∃ winner, resolveArguments ctx names = some winner := by
  constructor
  · rintro ⟨rows, returned⟩
    cases resolved : resolveArguments ctx names with
    | none =>
        rw [relevantRows, resolved] at returned
        cases returned
    | some winner => exact ⟨winner, rfl⟩
  · exact relevantRows_total_of_resolution ctx size asArgument names

/-- Every nonnegative source request has an actual successful constructor expression. -/
theorem firstOrderRaw_total (lib : SourceSynthesisTypeSyntax.Library)
    (query : SourceSynthesisTypeSyntax.Query) (size : Int) (nonnegative : 0 ≤ size) :
    ∃ expression, firstOrderRaw lib query size = .ok expression := by
  have allowed : ¬size < 0 := by omega
  let ctx := context lib query
  obtain ⟨chunks, chunksRun⟩ := SymbolicDriver.pure_mapM_total
    (fun arguments => relevantRows ctx true size.toNat (arguments.map Prod.fst))
    (permutations ctx.argumentEdges) (by
      intro arguments included
      exact relevantRows_total_of_resolution ctx size.toNat true (arguments.map Prod.fst)
        (root_lookup_exists ctx.argumentEdges arguments included))
  refine ⟨ofType (.union chunks.flatten) (SourceSynthesisTypeSyntax.typeNode
    SourceSynthesisGeneralizeSyntax.top query.queryGoal), ?_⟩
  rw [firstOrderRaw, ite_eq_right allowed]
  change (permutations ctx.argumentEdges).mapM _ >>= _ = _
  rw [chunksRun]
  rfl

/-- The source constructor accepts exactly the nonnegative signed size domain. -/
theorem firstOrderRaw_ok_iff_nonnegative (lib : SourceSynthesisTypeSyntax.Library)
    (query : SourceSynthesisTypeSyntax.Query) (size : Int) :
    (∃ expression, firstOrderRaw lib query size = .ok expression) ↔ 0 ≤ size := by
  constructor
  · rintro ⟨expression, returned⟩
    by_cases nonnegative : 0 ≤ size
    · exact nonnegative
    · have failed := firstOrderRaw_negative lib query size (by omega)
      rw [failed] at returned
      cases returned
  · exact firstOrderRaw_total lib query size

/-- Current source data derives a successful root expression and its typed witness. -/
theorem firstOrderRaw_member_total [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : SourceSynthesisTypeSyntax.Library} {query : SourceSynthesisTypeSyntax.Query}
    (size : Int) (nonnegative : 0 ≤ size)
    (selected : List (String × Row))
    (permutation : selected ∈ permutations (context lib query).argumentEdges)
    (program : SourceSynthesisProgramTermSize.Program)
    (body : Language.Term (SourceObservations.Label FullSyntax.Formula))
    (typed : SourceSynthesisSourceTermsTyping.RelevantTyping lib query true size.toNat
      (selected.map Prod.fst) program
      (SourceSynthesisFiniteTypeWitnesses.rigidTerm query.queryGoal) body) :
    ∃ expression, firstOrderRaw lib query size = .ok expression ∧
      InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) []
        (SourceSynthesisProgramBuildRolesGeneric.mapSyntax
          SourceSynthesisLabelProgramBuildRoles.literal expression)
        (.node (SourceSynthesisLabelProgramBuildRoles.literal "filter")
          [SourceSynthesisFiniteTypeWitnesses.rigidTerm query.queryGoal, body]) ∧
      SourceSynthesisProgramTermSize.Projection SourceSynthesisLabelProgramBuildRoles.literal Prod.fst
        (.node (SourceSynthesisLabelProgramBuildRoles.literal "filter")
          [SourceSynthesisFiniteTypeWitnesses.rigidTerm query.queryGoal, body]) program ∧
      program.components = size.toNat := by
  obtain ⟨expression, returned⟩ := firstOrderRaw_total lib query size nonnegative
  exact ⟨expression, returned, SourceSynthesisSourceRelevantTyping.firstOrderRaw_member
    formulas solver returned selected permutation typed⟩

end MicroCFTA.SourceSynthesisFirstOrderTotality
