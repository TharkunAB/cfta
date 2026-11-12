import MicroCFTA.SourceSynthesisCurrentContext

/-!
# Exact terms of current rigid Type instructions

A rigid Type instruction accepts only its own finite encoding.
The proof retains ordered children and the two-argument Fun alias.
The current instance observes the escaped source Type on the same term.
-/
namespace MicroCFTA.SourceSynthesisCurrentRigidTypeReification
open Language
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges)
open SourceSynthesisFiniteTypeWitnesses (rigidTerm)
open SourceSynthesisPr210TypeReflection (candidateRigid)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

private theorem forest_exact (holds : Guard → Term Symbol → Bool)
    (plans : List (Expr Guard)) (known : List (Term Symbol))
    (pointwise : All₂ (fun plan expected => ∀ term,
      evaluate holds [] (mapSyntax literal plan) term → term = expected) plans known)
    (terms : List (Term Symbol))
    (accepted : forest holds [] (mapChildren literal plans) terms) : terms = known := by
  induction pointwise generalizing terms with
  | nil =>
      cases terms with
      | nil => rfl
      | cons first rest => simp only [mapChildren, forest] at accepted
  | @cons plan expected plans known own later ih =>
      cases terms with
      | nil => simp only [mapChildren, forest] at accepted
      | cons first rest =>
          simp only [mapChildren, forest] at accepted
          rw [own first accepted.1, ih rest accepted.2]

private theorem node_exact (holds : Guard → Term Symbol → Bool) (name : String)
    (plans : List (Expr Guard)) (known : List (Term Symbol))
    (pointwise : All₂ (fun plan expected => ∀ term,
      evaluate holds [] (mapSyntax literal plan) term → term = expected) plans known)
    (term : Term Symbol)
    (accepted : evaluate holds [] (mapSyntax literal (.node [.mk name top plans])) term) :
    term = .node (literal name) known := by
  simp only [mapSyntax, mapEdges] at accepted
  rw [evaluate] at accepted
  obtain ⟨⟨edge, member⟩, held⟩ := accepted
  have same : edge = .mk (literal name) top (mapChildren literal plans) :=
    List.mem_singleton.mp member
  subst edge
  rw [edgeMeaning] at held
  obtain ⟨terms, rfl, children, _guard⟩ := held
  exact congrArg (Term.node (literal name)) (forest_exact holds plans known pointwise terms children)

private theorem arrow_exact (holds : Guard → Term Symbol → Bool) (argument result : Ty)
    (left : ∀ term, evaluate holds [] (mapSyntax literal (typeNode top argument)) term →
      term = rigidTerm argument)
    (right : ∀ term, evaluate holds [] (mapSyntax literal (typeNode top result)) term →
      term = rigidTerm result) :
    ∀ term, evaluate holds [] (mapSyntax literal (typeNode top (.tFun argument result))) term →
      term = rigidTerm (.tFun argument result) := by
  have marker := node_exact holds "(->)" [] [] All₂.nil
  simpa only [typeNode, rigidTerm, arrowType, arrowMarker] using
    node_exact holds "->" [.node [.mk "(->)" top []], typeNode top argument, typeNode top result]
      [.node (literal "(->)") [], rigidTerm argument, rigidTerm result]
      (.cons marker (.cons left (.cons right .nil)))

/-- An accepted rigid instruction has exactly the original ordered rigid term. -/
theorem typeNode_only (holds : Guard → Term Symbol → Bool) (typ : Ty) :
    ∀ term, evaluate holds [] (mapSyntax literal (typeNode top typ)) term → term = rigidTerm typ := by
  induction typ using Ty.rec
    (motive_2 := fun types => All₂ (fun plan expected => ∀ term,
      evaluate holds [] (mapSyntax literal plan) term → term = expected)
      (types.map (typeNode top)) (types.map rigidTerm)) with
  | tVar name =>
      simpa only [typeNode, rigidTerm] using node_exact holds (variableSymbol name) [] [] .nil
  | tFun argument result left right => exact arrow_exact holds argument result left right
  | tCons name arguments children =>
      have ordinary := node_exact holds name (arguments.map (typeNode top)) (arguments.map rigidTerm) children
      cases arguments with
      | nil => simpa only [typeNode, rigidTerm] using ordinary
      | cons first rest =>
          cases rest with
          | nil => simpa only [typeNode, rigidTerm] using ordinary
          | cons second rest =>
              cases rest with
              | cons third tail => simpa only [typeNode, rigidTerm] using ordinary
              | nil =>
                  by_cases alias : name = "Fun"
                  · cases children with
                    | cons firstOnly remaining =>
                        cases remaining with
                        | cons secondOnly _ =>
                            simpa only [typeNode, rigidTerm, alias, ↓reduceIte] using
                              arrow_exact holds first second firstOnly secondOnly
                  · simpa only [typeNode, rigidTerm, alias, ↓reduceIte, List.map_cons, List.map_nil] using ordinary
  | nil => exact .nil
  | cons first rest own later => exact .cons own later

/-- Current escaped Type acceptance retains the exact same raw candidate encoding. -/
theorem current_typeNode_only (holds : Guard → Term Symbol → Bool) (typ : Ty)
    (term : Term Symbol)
    (accepted : evaluate holds []
      (mapSyntax literal (SourceSynthesisCurrentContext.typeNode typ)) term) :
    term = candidateRigid typ := by
  exact typeNode_only holds (SourceSynthesisPr210TypeReflection.encodeTy typ) term accepted

end MicroCFTA.SourceSynthesisCurrentRigidTypeReification
