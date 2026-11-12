import MicroCFTA.SourceSynthesisCurrentTermsEligibility
import MicroCFTA.SourceSynthesisSelectionOrigins
import MicroCFTA.SymbolicNormalization

/-!
# Raw eligibility of current relevant rows

The actual successful table result supplies every recursive source row.
Marked tokens retain their original payloads and ordered duplicate occurrences.
Each marked leaf has the actual last query type, not the token payload type.
The same term retains its Program, annotation, decoder and component count.
This result permits every source avoid rule. It does not establish root coverage.
-/
namespace MicroCFTA.SourceSynthesisCurrentRelevantEligibility
open Language
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax (Ty Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction
  (Expression Row relevantRows resolveArguments application)
open SourceSynthesisCurrentContext (context typeNode)
open SourceSynthesisPr211QueryBindings (queryBindings queryBindings_member)
open SourceSynthesisOrdinaryTyping (queryLookup)
open SourceSynthesisProgramBuildRolesGeneric
  (mapSyntax mapChildren mapEdges mapChildren_eq_map)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisCurrentProgramAdmission (Eligible)
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

private abbrev Receipt [DecidableEq FullSyntax.Formula]
    (lib : Library) (query : Query) (asArgument : Bool)
    (count : Nat) (tokens : List (String × Ty)) (term : Term Symbol) :=
  ∃ program typ, Eligible lib query asArgument program typ tokens ∧
    Projection literal Prod.fst term program ∧ toProgram literal Prod.fst term = program ∧
    program.components = count ∧ term.atPath [0] = some (candidateRigid typ)

private theorem query_row_receipt [DecidableEq FullSyntax.Formula]
    (holds : Guard → Term Symbol → Bool)
    (lib : Library) (query : Query) (asArgument : Bool)
    (entry : String × Row) (tokens : List (String × Ty)) (term : Term Symbol)
    (included : entry ∈ (context lib query).argumentEdges)
    (named : tokens.map Prod.fst = [entry.1])
    (accepted : evaluate holds [] (mapSyntax literal (.node [entry.2])) term) :
    Receipt lib query asArgument 1 tokens term := by
  change entry ∈ (queryBindings query).map (fun binding =>
    (binding.1, (.mk binding.1 top [typeNode binding.2] : Row))) at included
  obtain ⟨binding, present, rfl⟩ := List.mem_map.mp included
  simp only [mapSyntax, mapEdges] at accepted
  rw [evaluate] at accepted
  obtain ⟨⟨edge, included⟩, checked⟩ := accepted
  have same := List.mem_singleton.mp included
  subst edge
  rw [edgeMeaning] at checked
  obtain ⟨terms, rfl, children, _guardHeld⟩ := checked
  rcases terms with _ | ⟨annotation, _ | ⟨_, _⟩⟩ <;>
    simp only [mapChildren, forest, and_false] at children
  have exactType := SourceSynthesisCurrentRigidTypeReification.current_typeNode_only
    holds binding.2 annotation children.1
  subst annotation
  have length : tokens.length = 1 := by
    simpa only [List.length_map, List.length_cons, List.length_nil] using congrArg List.length named
  cases tokens with
  | nil => simp at length
  | cons token remaining =>
      cases remaining with
      | nil =>
          have tokenName : token.1 = binding.1 := (List.cons.inj named).1
          have found : queryLookup query.queryArguments token.1 = some binding.2 := by
            rw [tokenName]
            exact queryBindings_member query binding.1 binding.2 present
          have eligible : Eligible lib query asArgument (.var binding.1) binding.2 [token] := by
            simpa only [tokenName] using (Eligible.queryToken asArgument token binding.2 found)
          exact ⟨.var binding.1, binding.2, eligible, .component _ _, rfl, rfl, rfl⟩
      | cons next rest => simp only [List.length_cons] at length; omega

private theorem union_receipt [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool} {count : Nat}
    {tokens : List (String × Ty)} {expressions : List Expression} {term : Term Symbol}
    (checked : ∀ expression ∈ expressions, ∀ child,
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) child →
        Receipt lib query asArgument count tokens child)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (.union expressions)) term) :
    Receipt lib query asArgument count tokens term := by
  rw [mapSyntax, evaluate] at accepted
  obtain ⟨⟨mapped, member⟩, observed⟩ := accepted
  rw [mapChildren_eq_map] at member
  obtain ⟨expression, original, rfl⟩ := List.mem_map.mp member
  exact checked expression original term observed

private theorem application_receipt [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (lib : Library) (query : Query)
    {asArgument : Bool} {leftCount rightCount : Nat} {function argument : Expression}
    {left right : List (String × Ty)} {term : Term Symbol}
    (first : ∀ child, evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal function) child → Receipt lib query false leftCount left child)
    (second : ∀ child, evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal argument) child → Receipt lib query true rightCount right child)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (application (context lib query).types function argument)) term) :
    Receipt lib query asArgument (leftCount + rightCount) (left ++ right) term := by
  simp only [application, mapSyntax, mapEdges] at accepted
  rw [evaluate] at accepted
  obtain ⟨⟨edge, member⟩, observed⟩ := accepted
  have same := List.mem_singleton.mp member
  subst edge
  rw [edgeMeaning] at observed
  obtain ⟨terms, rfl, children, guardHeld⟩ := observed
  rcases terms with _ | ⟨annotation, _ | ⟨actualMarker, _ | ⟨functionTerm, _ | ⟨argumentTerm, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
    simp only [mapChildren, forest, and_false] at children
  obtain ⟨functionProgram, functionType, functionEligible, functionProjection, _functionDecoded,
      functionCount, functionAnnotation⟩ := first functionTerm children.2.2.1
  obtain ⟨argumentProgram, argumentType, argumentEligible, argumentProjection, _argumentDecoded,
      argumentCount, argumentAnnotation⟩ := second argumentTerm children.2.2.2.1
  have actualForest : forest (SourceEqualityPCSGuard.holds formulas solver) []
      (mapChildren literal [(context lib query).types, SourceSynthesisTypeSyntax.arrowMarker top,
        function, argument]) [annotation, actualMarker, functionTerm, argumentTerm] := by
    simpa only [mapChildren, forest] using children
  obtain ⟨resultType, eligible, annotationSame, projected⟩ :=
    SourceSynthesisCurrentApplicationEligibility.application_eligible formulas solver lib query asArgument
      function argument annotation actualMarker functionTerm argumentTerm functionProgram argumentProgram
      functionType argumentType left right actualForest guardHeld
      functionEligible functionProjection functionAnnotation
      argumentEligible argumentProjection argumentAnnotation
  refine ⟨.app functionProgram argumentProgram, resultType, eligible, projected,
    projected.toProgram_eq, ?_, ?_⟩
  · simp only [Program.components, functionCount, argumentCount]
  · simpa only [Term.atPath, List.getElem?_cons_zero, Option.bind_some] using congrArg some annotationSame

/-- Actual relevant acceptance retains raw eligibility with the exact requested token names. -/
theorem relevant_eligible [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (asArgument : Bool) (count : Nat)
    (names : List String) (rows : List Expression)
    (returned : relevantRows (context lib query) asArgument count names = .ok rows)
    (tokens : List (String × Ty)) (tokenNames : tokens.map Prod.fst = names)
    (expression : Expression) (member : expression ∈ rows) (term : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ program typ, Eligible lib query asArgument program typ tokens ∧
      Projection literal Prod.fst term program ∧ toProgram literal Prod.fst term = program ∧
      program.components = count ∧ term.atPath [0] = some (candidateRigid typ) := by
  have checked : ∀ size asArgument names rows,
      relevantRows (context lib query) asArgument size names = .ok rows →
      ∀ tokens : List (String × Ty), tokens.map Prod.fst = names →
      ∀ expression ∈ rows, ∀ term,
        evaluate (SourceEqualityPCSGuard.holds formulas solver) []
          (mapSyntax literal expression) term → Receipt lib query asArgument size tokens term := by
    intro size
    induction size using Nat.strongRecOn with
    | ind size ih =>
        intro asArgument names rows returned tokens tokenNames
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
            have winnerNames := (SourceSynthesisSelections.resolveSelection_spec
              (context lib query).argumentEdges names arguments resolved).2
            have aligned : tokens.map Prod.fst = arguments.map Prod.fst :=
              tokenNames.trans winnerNames.symm
            split at computed
            · have same := Except.ok.inj computed
              subst rows
              have empty : tokens = [] := List.eq_nil_of_length_eq_zero (by
                simpa only [List.length_map, List.length_nil] using congrArg List.length aligned)
              subst tokens
              intro expression member term accepted
              exact SourceSynthesisCurrentTermsEligibility.terms_eligible formulas solver lib query
                asArgument size expression term member accepted
            · have same := Except.ok.inj computed
              subst rows
              intro expression member term accepted
              have same := List.mem_singleton.mp member
              subst expression
              exact query_row_receipt (SourceEqualityPCSGuard.holds formulas solver)
                lib query asArgument _ tokens term (argumentsIncluded _ List.mem_cons_self)
                (by simpa only [List.map_cons, List.map_nil] using aligned) accepted
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
                      (mapSyntax literal expression) term → Receipt lib query asArgument size tokens term := by
                  apply mapM_preserves (fun chunk => ∀ expression ∈ chunk, ∀ term,
                    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
                      (mapSyntax literal expression) term → Receipt lib query asArgument size tokens term)
                    _ _ _ _ chunksResult
                  intro split choices choicesResult
                  apply mapM_preserves (fun expression => ∀ term,
                    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
                      (mapSyntax literal expression) term → Receipt lib query asArgument size tokens term)
                    _ _ _ _ choicesResult
                  intro offset expression expressionResult
                  obtain ⟨function, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
                  obtain ⟨argument, argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
                  have same := Except.ok.inj completed
                  subst expression
                  intro term accepted
                  have result := application_receipt formulas solver lib query
                    (asArgument := asArgument)
                    (leftCount := split.val) (rightCount := size - split.val)
                    (left := tokens.take offset) (right := tokens.drop offset)
                    (fun child observed => union_receipt formulas solver
                      (fun alternative inside term observed =>
                        ih split.val split.property.2 false _ function functionResult
                          (tokens.take offset)
                          (by simpa only [List.map_take] using congrArg (List.take offset) aligned)
                          alternative inside term observed) observed)
                    (fun child observed => union_receipt formulas solver
                      (fun alternative inside term observed =>
                        ih (size - split.val) (by have positive := split.property.1; omega)
                          true _ argument argumentResult (tokens.drop offset)
                          (by simpa only [List.map_drop] using congrArg (List.drop offset) aligned)
                          alternative inside term observed) observed)
                    accepted
                  simpa only [Nat.add_sub_of_le (Nat.le_of_lt split.property.2),
                    List.take_append_drop] using result
                intro expression member term accepted
                obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
                exact chunksChecked chunk included expression inside term accepted
  exact checked count asArgument names rows returned tokens tokenNames expression member term accepted

end MicroCFTA.SourceSynthesisCurrentRelevantEligibility
