import MicroCFTA.SourceSynthesisCurrentRelevantEligibility
import MicroCFTA.SourceSynthesisQueryTokenPermutation
import MicroCFTA.SourceSynthesisCurrentRelevantAdmission
import MicroCFTA.SourceSynthesisCurrentConstruction
import MicroCFTA.SymbolicScope

/-!
# Exact eligibility of the current FirstOrder source root

The actual construction result supplies its successful row calls.
The accepted filter retains the same body, goal, Program and component count.
Type conversion uses the documented Fun/2 equivalence.
Marked tokens retain the original query payloads and duplicate occurrences.
The converse projected language result requires an empty avoid list.
Neither result establishes native execution.
-/
namespace MicroCFTA.SourceSynthesisCurrentRootEligibility
open Language
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (eqGuard)
open SourceSynthesisFirstOrderConstruction (Expression Row relevantRows ofType)
open SourceSynthesisCurrentContext (context)
open SourceSynthesisProgramBuildRolesGeneric
  (mapSyntax mapChildren mapEdges mapChildren_eq_map)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisCurrentProgramAdmission (Eligible)
open SourceSynthesisPr210TypeReflection (candidateRigid candidateRigid_eq_iff)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

private theorem output_origin {A B : Type} {relation : A → B → Prop}
    {inputs : List A} {outputs : List B} (linked : All₂ relation inputs outputs)
    {output : B} (member : output ∈ outputs) :
    ∃ input, input ∈ inputs ∧ relation input output := by
  induction linked with
  | nil => cases member
  | @cons input first inputs outputs head tail ih =>
      rcases List.mem_cons.mp member with rfl | inside
      · exact ⟨input, by simp, head⟩
      · obtain ⟨other, present, related⟩ := ih inside
        exact ⟨other, List.mem_cons_of_mem input present, related⟩

/-- Actual root acceptance derives eligibility and all original marked query tokens. -/
theorem root_eligible [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (term : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ program tokens,
      Eligible lib query true program query.queryGoal tokens ∧
      tokens.Perm query.queryArguments ∧
      Projection literal Prod.fst term program ∧
      toProgram literal Prod.fst term = program ∧
      program.components = signed.toNat ∧
      term.atPath [0] = some (candidateRigid query.queryGoal) := by
  rw [SourceSynthesisCurrentConstruction.firstOrderRaw] at returned
  split at returned
  · cases returned
  · cases traversed : (SourceSynthesisSelections.permutations
        (context lib query).argumentEdges).mapM (fun selected =>
          relevantRows (context lib query) true signed.toNat (selected.map Prod.fst)) with
    | error error => simp only [traversed] at returned; cases returned
    | ok chunks =>
      simp only [traversed] at returned
      cases returned
      simp only [ofType, mapSyntax, mapEdges] at accepted
      rw [evaluate] at accepted
      obtain ⟨⟨edge, member⟩, observed⟩ := accepted
      have same := List.mem_singleton.mp member
      subst edge
      rw [edgeMeaning] at observed
      obtain ⟨terms, rfl, children, guardHeld⟩ := observed
      rcases terms with _ | ⟨goal, _ | ⟨body, _ | ⟨_, _⟩⟩⟩ <;>
        simp only [mapChildren, forest, and_false] at children
      have goalSame := SourceSynthesisCurrentRigidTypeReification.current_typeNode_only
        (SourceEqualityPCSGuard.holds formulas solver) query.queryGoal goal children.1
      subst goal
      have bodyAccepted := children.2.1
      rw [mapSyntax, evaluate] at bodyAccepted
      obtain ⟨⟨mapped, included⟩, observedBody⟩ := bodyAccepted
      rw [mapChildren_eq_map] at included
      obtain ⟨candidate, original, rfl⟩ := List.mem_map.mp included
      obtain ⟨rows, chunkMember, rowMember⟩ := List.mem_flatten.mp original
      have runs := SymbolicDriver.mapM_success_all₂ _ _ _ traversed
      obtain ⟨selected, selectedMember, rowsReturned⟩ := output_origin runs chunkMember
      have selectedPermutation :=
        (SourceSynthesisSelectionClosure.permutations_spec _ _).mp selectedMember
      have namePermutation := selectedPermutation.map Prod.fst
      rw [SourceSynthesisCurrentContext.context_argument_names] at namePermutation
      obtain ⟨tokens, covered, tokenNames⟩ :=
        SourceSynthesisQueryTokenPermutation.original_tokens query (selected.map Prod.fst) namePermutation
      obtain ⟨program, typ, eligible, projected, _decoded, counted, annotation⟩ :=
        SourceSynthesisCurrentRelevantEligibility.relevant_eligible formulas solver lib query
          true signed.toNat (selected.map Prod.fst) rows rowsReturned tokens tokenNames
          candidate rowMember body observedBody
      have satisfied : EqualityNormalize.Satisfies
          (.node (literal "filter") [candidateRigid query.queryGoal, body])
          [[[0], [1, 0]]] := by
        have raw := ((SourceEqualityPCSGuard.holds_exact formulas solver _ _).mp guardHeld).1
        rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source] at raw
        exact (SourceEqualityPCSGuard.normalize_sat _ _).mp raw
      obtain ⟨common, goalPath, bodyPath⟩ :=
        (satisfied [[0], [1, 0]] (by simp)) [0] (by simp) [1, 0] (by simp) (by decide)
      have bodyAtGoal : body.atPath [0] = some (candidateRigid query.queryGoal) := by
        simpa only [Term.atPath, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.bind_some] using bodyPath.trans goalPath.symm
      have encoded : candidateRigid typ = candidateRigid query.queryGoal :=
        Option.some.inj (annotation.symm.trans bodyAtGoal)
      have eligibleGoal : Eligible lib query true program query.queryGoal tokens :=
        .conversion eligible ((candidateRigid_eq_iff typ query.queryGoal).mp encoded)
      have rootProjected := Projection.filter (candidateRigid query.queryGoal) projected
      exact ⟨program, tokens, eligibleGoal, covered, rootProjected,
        rootProjected.toProgram_eq, counted, rfl⟩

/-- With no avoid rules, projected source acceptance is exactly marked raw eligibility. -/
theorem projected_language_iff [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (unpruned : lib.libraryAvoid = []) (program : Program) :
    (∃ (expression : Expression) (term : Term Symbol),
      SourceSynthesisCurrentConstruction.firstOrderRaw lib query (Int.ofNat program.components) = .ok expression ∧
      evaluate (SourceEqualityPCSGuard.holds formulas solver) [] (mapSyntax literal expression) term ∧
      toProgram literal Prod.fst term = program) ↔
    ∃ tokens, Eligible lib query true program query.queryGoal tokens ∧
      tokens.Perm query.queryArguments := by
  constructor
  · rintro ⟨expression, term, returned, accepted, decoded⟩
    obtain ⟨actual, tokens, eligible, covered, _projected, actualDecoded, _counted, _annotation⟩ :=
      root_eligible formulas solver lib query (Int.ofNat program.components) expression returned term accepted
    have same : actual = program := actualDecoded.symm.trans decoded
    exact ⟨tokens, same ▸ eligible, covered⟩
  · rintro ⟨tokens, eligible, covered⟩
    obtain ⟨_typed, expression, body, returned, accepted, _annotation, _projected, decoded, _counted⟩ :=
      SourceSynthesisCurrentRelevantAdmission.uses_root_member formulas solver unpruned eligible covered
    exact ⟨expression, .node (literal "filter") [candidateRigid query.queryGoal, body],
      returned, accepted, decoded⟩

end MicroCFTA.SourceSynthesisCurrentRootEligibility
