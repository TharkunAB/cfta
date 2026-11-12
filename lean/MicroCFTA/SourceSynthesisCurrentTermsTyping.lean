import MicroCFTA.SourceSynthesisCurrentApplicationTyping
import MicroCFTA.SourceSynthesisCurrentLeafTyping

/-!
# Ordinary typing of current unrestricted terms rows

Actual row membership and guarded acceptance determine one ordinary Program.
The result retains the same projection, decoder, component count and annotation.
Size-two avoid pools embed into genuine size-one source pools.
This result does not establish relevant rows, root coverage or native behavior.
-/
namespace MicroCFTA.SourceSynthesisCurrentTermsTyping
open Language
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax (Ty Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction
  (Expression Row termsRows termsRows_one application without)
open SourceSynthesisCurrentContext (context)
open SourceSynthesisProgramBuildRolesGeneric
  (mapSyntax mapChildren mapEdges mapEdges_eq_map mapChildren_eq_map)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisPr210TypeReflection (candidateRigid)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

variable [DecidableEq FullSyntax.Formula]

private abbrev Receipt (lib : Library) (query : Query) (count : Nat) (term : Term Symbol) :=
  ∃ program typ, Typed lib query program typ ∧ Projection literal Prod.fst term program ∧
    toProgram literal Prod.fst term = program ∧ program.components = count ∧
    term.atPath [0] = some (candidateRigid typ)

private theorem leaf_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool} {expression : Expression} {term : Term Symbol}
    (member : expression ∈ termsRows (context lib query) asArgument 1)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) : Receipt lib query 1 term := by
  obtain ⟨name, typ, _shape, typed, path, projected, decoded, _counted, _origin⟩ :=
    SourceSynthesisCurrentLeafTyping.size_one_typed formulas solver member accepted
  exact ⟨.var name, typ, typed, projected, decoded, rfl, path⟩

omit [DecidableEq FullSyntax.Formula] in
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

private theorem selected_components
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (select : String × Row → Bool) (term : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (.node (((context lib query).components.filter select).map Prod.snd))) term) :
    Receipt lib query 1 term := by
  apply leaf_receipt formulas solver (asArgument := false)
    (expression := .node ((context lib query).components.map Prod.snd))
  · rw [termsRows_one]
    simp
  · apply node_inclusion _ _ _ term ?_ accepted
    intro row member
    obtain ⟨entry, selected, same⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨entry, (List.mem_filter.mp selected).1, same⟩

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

omit [DecidableEq FullSyntax.Formula] in
/-- Actual current terms-row acceptance retains ordinary typing and the same counted Program. -/
theorem terms_typed [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (asArgument : Bool) (count : Nat)
    (expression : Expression) (term : Term Symbol)
    (member : expression ∈ termsRows (context lib query) asArgument count)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ program typ, Typed lib query program typ ∧ Projection literal Prod.fst term program ∧
      toProgram literal Prod.fst term = program ∧ program.components = count ∧
      term.atPath [0] = some (candidateRigid typ) := by
  change Receipt lib query count term
  revert asArgument expression term
  induction count using Nat.strongRecOn with
  | ind count ih =>
      intro asArgument expression term member accepted
      cases count with
      | zero => simp only [termsRows, List.not_mem_nil] at member
      | succ count =>
          cases count with
          | zero => exact leaf_receipt formulas solver member accepted
          | succ count =>
              cases count with
              | zero =>
                  rw [termsRows] at member
                  rcases List.mem_append.mp member with restricted | ordinary
                  · obtain ⟨⟨functions, arguments⟩, _included, selected⟩ := List.mem_filterMap.mp restricted
                    cases arguments with
                    | none => cases selected
                    | some excluded =>
                        have same := Option.some.inj selected
                        subst expression
                        refine application_receipt formulas solver lib query
                          (leftCount := 1) (rightCount := 1) ?_ ?_ accepted
                        · intro child observed
                          exact selected_components formulas solver lib query _ child observed
                        · intro child observed
                          apply union_receipt formulas solver ?_ observed
                          intro alternative inside child observed
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                          rcases inside with rfl | rfl | rfl
                          · exact selected_components formulas solver lib query _ child observed
                          · exact leaf_receipt formulas solver (asArgument := true)
                              (expression := .node ((context lib query).argumentEdges.map Prod.snd))
                              (by rw [termsRows_one]; simp) observed
                          · exact leaf_receipt formulas solver (asArgument := true)
                              (expression := (context lib query).argumentOnly)
                              (by rw [termsRows_one]; simp) observed
                  · have same := List.mem_singleton.mp ordinary
                    subst expression
                    refine application_receipt formulas solver lib query
                      (leftCount := 1) (rightCount := 1) ?_ ?_ accepted
                    · intro child observed
                      apply union_receipt formulas solver ?_ observed
                      intro alternative inside child observed
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                      rcases inside with rfl | rfl
                      · exact selected_components formulas solver lib query _ child observed
                      · exact leaf_receipt formulas solver (asArgument := false)
                          (expression := .node ((context lib query).argumentEdges.map Prod.snd))
                          (by rw [termsRows_one]; simp) observed
                    · intro child observed
                      apply union_receipt formulas solver ?_ observed
                      intro alternative inside child observed
                      exact ih 1 (by decide) true alternative child inside observed
              | succ rest =>
                  rw [termsRows] at member
                  obtain ⟨split, _included, rfl⟩ := List.mem_map.mp member
                  have result := application_receipt formulas solver lib query
                    (leftCount := split.val) (rightCount := rest + 3 - split.val)
                    (fun child observed => union_receipt formulas solver
                      (fun alternative inside term observed =>
                        ih split.val split.property.2 false alternative term inside observed) observed)
                    (fun child observed => union_receipt formulas solver
                      (fun alternative inside term observed =>
                        ih (rest + 3 - split.val) (by have positive := split.property.1; omega)
                          true alternative term inside observed) observed) accepted
                  simpa only [Nat.add_sub_of_le (Nat.le_of_lt split.property.2)] using result

end MicroCFTA.SourceSynthesisCurrentTermsTyping
