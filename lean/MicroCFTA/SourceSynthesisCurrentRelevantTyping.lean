import MicroCFTA.SourceSynthesisCurrentTermsTyping
import MicroCFTA.SourceSynthesisSelectionOrigins
import MicroCFTA.SymbolicNormalization

/-!
# Ordinary typing of current relevant rows

The proof observes one actual source result and one accepted term.
It retains the same Program, projection, component count and annotation.
It permits duplicate query names and all source avoid rules.
It does not assert inclusion in unrestricted terms rows or native completion.
-/
namespace MicroCFTA.SourceSynthesisCurrentRelevantTyping
open Language
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax (Ty Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction
  (Expression Row termsRows termsRows_one relevantRows resolveArguments application positiveSplits)
open SourceSynthesisCurrentContext (context)
open SourceSynthesisProgramBuildRolesGeneric
  (mapSyntax mapChildren mapEdges mapEdges_eq_map mapChildren_eq_map)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisPr210TypeReflection (candidateRigid)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

private theorem bind_ok {Error Input Output : Type} (action : Except Error Input)
    (next : Input → Except Error Output) (value : Output)
    (returned : action.bind next = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases returned
  | ok input => exact ⟨input, rfl, returned⟩

private theorem mapM_preserves {Error Input Output : Type} (P : Output → Prop)
    (action : Input → Except Error Output) (inputs : List Input) (outputs : List Output)
    (checked : ∀ input output, action input = .ok output → P output)
    (returned : inputs.mapM action = .ok outputs) : ∀ output ∈ outputs, P output := by
  have related := SymbolicDriver.mapM_success_all₂ action inputs outputs returned
  have certificates := related.imp (fun input output success =>
    iff_of_true True.intro (checked input output success))
  exact (SymbolicDriver.all₂_forall_iff (fun _ => True) P inputs outputs certificates).mp (by simp)

private theorem node_inclusion (holds : Guard → Term Symbol → Bool)
    (rows targets : List Row) (term : Term Symbol)
    (included : ∀ row ∈ rows, row ∈ targets)
    (accepted : evaluate holds [] (mapSyntax literal (.node rows)) term) :
    evaluate holds [] (mapSyntax literal (.node targets)) term := by
  rw [mapSyntax, evaluate] at accepted ⊢
  obtain ⟨⟨mapped, member⟩, checked⟩ := accepted
  refine ⟨⟨mapped, ?_⟩, checked⟩
  rw [mapEdges_eq_map] at member ⊢
  obtain ⟨row, original, rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨row, included row original, rfl⟩

variable [DecidableEq FullSyntax.Formula]

private abbrev Receipt (lib : Library) (query : Query) (count : Nat) (term : Term Symbol) :=
  ∃ program typ, Typed lib query program typ ∧ Projection literal Prod.fst term program ∧
    toProgram literal Prod.fst term = program ∧ program.components = count ∧
    term.atPath [0] = some (candidateRigid typ)

private theorem query_row_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (row : Row) (term : Term Symbol)
    (included : row ∈ (context lib query).argumentEdges.map Prod.snd)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (.node [row])) term) : Receipt lib query 1 term := by
  have actual := node_inclusion _ [row] ((context lib query).argumentEdges.map Prod.snd) term
    (fun selected present => by
      have same := List.mem_singleton.mp present
      subst selected
      exact included) accepted
  obtain ⟨name, typ, _shape, typed, path, projected, decoded, _counted, _origin⟩ :=
    SourceSynthesisCurrentLeafTyping.size_one_typed formulas solver
      (lib := lib) (query := query) (asArgument := true)
      (expression := .node ((context lib query).argumentEdges.map Prod.snd))
      (by rw [termsRows_one]; simp) actual
  exact ⟨.var name, typ, typed, projected, decoded, rfl, path⟩

private theorem union_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {count : Nat} {expressions : List Expression} {term : Term Symbol}
    (checked : ∀ expression ∈ expressions, ∀ child,
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) child →
        Receipt lib query count child)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (.union expressions)) term) : Receipt lib query count term := by
  rw [mapSyntax, evaluate] at accepted
  obtain ⟨⟨mapped, member⟩, observed⟩ := accepted
  rw [mapChildren_eq_map] at member
  obtain ⟨expression, original, rfl⟩ := List.mem_map.mp member
  exact checked expression original term observed

private theorem application_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (lib : Library) (query : Query)
    {leftCount rightCount : Nat} {function argument : Expression} {term : Term Symbol}
    (first : ∀ child, evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal function) child → Receipt lib query leftCount child)
    (second : ∀ child, evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal argument) child → Receipt lib query rightCount child)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (application (context lib query).types function argument)) term) :
    Receipt lib query (leftCount + rightCount) term := by
  simp only [application, mapSyntax, mapEdges] at accepted
  rw [evaluate] at accepted
  obtain ⟨⟨edge, member⟩, observed⟩ := accepted
  have same := List.mem_singleton.mp member
  subst edge
  rw [edgeMeaning] at observed
  obtain ⟨terms, rfl, children, guardHeld⟩ := observed
  rcases terms with _ | ⟨annotation, _ | ⟨actualMarker, _ | ⟨functionTerm, _ | ⟨argumentTerm, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
    simp only [mapChildren, forest, and_false] at children
  obtain ⟨functionProgram, functionType, functionTyped, functionProjection, _functionDecoded,
      functionCount, functionAnnotation⟩ := first functionTerm children.2.2.1
  obtain ⟨argumentProgram, argumentType, argumentTyped, argumentProjection, _argumentDecoded,
      argumentCount, argumentAnnotation⟩ := second argumentTerm children.2.2.2.1
  have actualForest : forest (SourceEqualityPCSGuard.holds formulas solver) []
      (mapChildren literal [(context lib query).types, SourceSynthesisTypeSyntax.arrowMarker top,
        function, argument]) [annotation, actualMarker, functionTerm, argumentTerm] := by
    simpa only [mapChildren, forest] using children
  obtain ⟨resultType, typed, annotationSame, projected⟩ :=
    SourceSynthesisCurrentApplicationTyping.application_typed formulas solver lib query function argument
      annotation actualMarker functionTerm argumentTerm functionProgram argumentProgram functionType argumentType
      actualForest guardHeld functionTyped functionProjection functionAnnotation
      argumentTyped argumentProjection argumentAnnotation
  refine ⟨.app functionProgram argumentProgram, resultType, typed, projected,
    projected.toProgram_eq, ?_, ?_⟩
  · simp only [Program.components, functionCount, argumentCount]
  · simpa only [Term.atPath, List.getElem?_cons_zero, Option.bind_some] using congrArg some annotationSame

/-- Actual relevant-row acceptance retains ordinary typing and the same counted Program. -/
theorem relevant_typed
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (asArgument : Bool) (count : Nat)
    (names : List String) (rows : List Expression)
    (returned : relevantRows (context lib query) asArgument count names = .ok rows)
    (expression : Expression) (member : expression ∈ rows) (term : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ program typ, Typed lib query program typ ∧ Projection literal Prod.fst term program ∧
      toProgram literal Prod.fst term = program ∧ program.components = count ∧
      term.atPath [0] = some (candidateRigid typ) := by
  have checked : ∀ size asArgument names rows,
      relevantRows (context lib query) asArgument size names = .ok rows →
      ∀ expression ∈ rows, ∀ term,
        evaluate (SourceEqualityPCSGuard.holds formulas solver) []
          (mapSyntax literal expression) term → Receipt lib query size term := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
        intro asArgument names rows returned
        rw [relevantRows] at returned
        cases resolved : resolveArguments (context lib query) names with
        | none => simp only [resolved] at returned; cases returned
        | some arguments =>
            simp only [resolved] at returned
            obtain ⟨actual, actualResult, computed⟩ := bind_ok _ _ _ returned
            have same := Except.ok.inj actualResult
            subst actual
            have argumentsIncluded : ∀ entry ∈ arguments,
                entry ∈ (context lib query).argumentEdges :=
              SourceSynthesisSelectionOrigins.resolveSelection_subset
                (context lib query).argumentEdges names arguments resolved
            split at computed
            · have same := Except.ok.inj computed
              subst rows
              intro expression member term accepted
              exact SourceSynthesisCurrentTermsTyping.terms_typed formulas solver lib query
                asArgument size expression term member accepted
            · have same := Except.ok.inj computed
              subst rows
              intro expression member term accepted
              have same := List.mem_singleton.mp member
              subst expression
              apply query_row_receipt formulas solver lib query _ term ?_ accepted
              exact List.mem_map.mpr ⟨_, argumentsIncluded _ List.mem_cons_self, rfl⟩
            · split at computed
              · have same := Except.ok.inj computed
                subst rows
                intro expression member
                cases member
              · obtain ⟨chunks, chunksResult, flattened⟩ := bind_ok _ _ _ computed
                have same := Except.ok.inj flattened
                subst rows
                have chunksChecked : ∀ chunk ∈ chunks, ∀ expression ∈ chunk, ∀ term,
                    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
                      (mapSyntax literal expression) term → Receipt lib query size term := by
                  apply mapM_preserves (fun chunk => ∀ expression ∈ chunk, ∀ term,
                    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
                      (mapSyntax literal expression) term → Receipt lib query size term)
                    _ _ _ _ chunksResult
                  intro split choices choicesResult
                  apply mapM_preserves (fun expression => ∀ term,
                    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
                      (mapSyntax literal expression) term → Receipt lib query size term)
                    _ _ _ _ choicesResult
                  intro offset expression expressionResult
                  obtain ⟨function, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
                  obtain ⟨argument, argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
                  have same := Except.ok.inj completed
                  subst expression
                  intro term accepted
                  have result := application_receipt formulas solver lib query
                    (leftCount := split.val) (rightCount := size - split.val)
                    (fun child observed => union_receipt formulas solver
                      (fun alternative inside term observed =>
                        ih split.val split.property.2 false _ function functionResult
                          alternative inside term observed) observed)
                    (fun child observed => union_receipt formulas solver
                      (fun alternative inside term observed =>
                        ih (size - split.val) (by have positive := split.property.1; omega)
                          true _ argument argumentResult alternative inside term observed) observed)
                    accepted
                  simpa only [Nat.add_sub_of_le (Nat.le_of_lt split.property.2)] using result
                intro expression member term accepted
                obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
                exact chunksChecked chunk included expression inside term accepted
  exact checked count asArgument names rows returned expression member term accepted

end MicroCFTA.SourceSynthesisCurrentRelevantTyping
