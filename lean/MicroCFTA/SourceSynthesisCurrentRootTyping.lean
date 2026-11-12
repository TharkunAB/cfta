import MicroCFTA.SourceSynthesisCurrentRelevantTyping
import MicroCFTA.SourceSynthesisCurrentConstruction
import MicroCFTA.SymbolicScope

/-!
# Ordinary typing of the current FirstOrder source root

The actual construction result supplies its successful row calls.
The accepted filter retains the same body, goal, Program and component count.
Type conversion uses the documented Fun/2 equivalence.
This result does not establish native execution or query-use coverage.
-/
namespace MicroCFTA.SourceSynthesisCurrentRootTyping
open Language
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (eqGuard)
open SourceSynthesisFirstOrderConstruction (Expression Row relevantRows ofType)
open SourceSynthesisCurrentContext (context)
open SourceSynthesisProgramBuildRolesGeneric
  (mapSyntax mapChildren mapEdges mapChildren_eq_map)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisPr210TypeReflection (candidateRigid candidateRigid_eq_iff)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

/-- Every accepted current root decodes to the same ordinary Program at its goal. -/
theorem firstOrderRaw_typed [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (term : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ program body,
      term = .node (literal "filter") [candidateRigid query.queryGoal, body] ∧
      Typed lib query program query.queryGoal ∧
      term.atPath [0] = some (candidateRigid query.queryGoal) ∧
      body.atPath [0] = some (candidateRigid query.queryGoal) ∧
      Projection literal Prod.fst term program ∧
      toProgram literal Prod.fst term = program ∧
      program.components = signed.toNat := by
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
      have calls : ∀ rows ∈ chunks, ∃ selected : List (String × Row),
          relevantRows (context lib query) true signed.toNat (selected.map Prod.fst) = .ok rows :=
        SymbolicDriver.all₂_right_forall _ _ _ _ runs
          (fun selected _ returned => ⟨selected, returned⟩)
      obtain ⟨selected, rowsReturned⟩ := calls rows chunkMember
      obtain ⟨program, typ, typed, projected, _decoded, counted, annotation⟩ :=
        SourceSynthesisCurrentRelevantTyping.relevant_typed formulas solver lib query
          true signed.toNat (selected.map Prod.fst) rows rowsReturned candidate rowMember
          body observedBody
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
      have typedGoal : Typed lib query program query.queryGoal :=
        .conversion typed ((candidateRigid_eq_iff typ query.queryGoal).mp encoded)
      have rootProjected := Projection.filter (candidateRigid query.queryGoal) projected
      exact ⟨program, body, rfl, typedGoal, rfl, bodyAtGoal, rootProjected,
        rootProjected.toProgram_eq, counted⟩

end MicroCFTA.SourceSynthesisCurrentRootTyping
