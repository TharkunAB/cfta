import MicroCFTA.SourceSynthesisGeneralizeFiniteInstances

/-!
# Finite source Type witnesses

Structural witnesses derive membership in the actual recursive universe.
Each scheme occurrence can use its own substitution. Only demanded images
need universe witnesses. Rigid query types use their exact source encoding,
including variable names and the two-argument Fun alias.

These laws do not supply a whole Program or a successful original request.
-/
namespace MicroCFTA.SourceSynthesisFiniteTypeWitnesses
open Language
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top variables generalize)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

/-- A finite Type uses only the actual universe alternatives. -/
inductive TypeIn (catalog : List (String × Nat)) : Term Symbol → Prop where
  | leaf (name : String) (present : name ∈ ["var1", "var2", "var3", "var4"]) :
      TypeIn catalog (.node (literal name) [])
  | node (name : String) (children : List (Term Symbol))
      (present : (name, children.length) ∈ catalog)
      (checked : ∀ child ∈ children, TypeIn catalog child) :
      TypeIn catalog (.node (literal name) children)
  | arrow (argument result : Term Symbol)
      (first : TypeIn catalog argument) (second : TypeIn catalog result) :
      TypeIn catalog (.node (literal "->") [.node (literal "(->)") [], argument, result])

/-- Structural admission proves actual membership without a native result premise. -/
theorem TypeIn.member (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true) {catalog : List (String × Nat)}
    {term : Term Symbol} (witness : TypeIn catalog term) :
    evaluate holds [] (mapSyntax literal (allTypes top catalog)) term := by
  induction witness with
  | leaf name present =>
      exact SourceSynthesisTypeUniverseMembership.variable_member literal holds topHeld catalog name present
  | node name children present _checked ih =>
      exact SourceSynthesisTypeUniverseMembership.constructor_member literal holds topHeld
        catalog name children present ih
  | arrow argument result _first _second left right =>
      exact SourceSynthesisTypeUniverseMembership.arrow_member literal holds topHeld
        catalog argument result left right

/-- Rigid encoding retains all source variables and ordinary constructor arities. -/
def rigidTerm : Ty → Term Symbol
  | .tVar name => .node (literal (variableSymbol name)) []
  | .tFun argument result =>
      .node (literal "->") [.node (literal "(->)") [], rigidTerm argument, rigidTerm result]
  | .tCons name [argument, result] =>
      if name = "Fun" then
        .node (literal "->") [.node (literal "(->)") [], rigidTerm argument, rigidTerm result]
      else .node (literal name) [rigidTerm argument, rigidTerm result]
  | .tCons name arguments => .node (literal name) (arguments.map rigidTerm)

private theorem node_member (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true) (name : String)
    (children : List (Expr Guard)) (terms : List (Term Symbol))
    (accepted : forest holds [] (mapChildren literal children) terms) :
    evaluate holds [] (mapSyntax literal (.node [.mk name top children]))
      (.node (literal name) terms) := by
  simp only [mapSyntax, mapEdges]
  rw [evaluate]
  refine ⟨⟨.mk (literal name) top (mapChildren literal children), List.mem_cons_self⟩, ?_⟩
  rw [edgeMeaning]
  exact ⟨terms, rfl, accepted, topHeld _⟩

private theorem mapped_forest (holds : Guard → Term Symbol → Bool) (types : List Ty)
    (checked : ∀ typ ∈ types,
      evaluate holds [] (mapSyntax literal (typeNode top typ)) (rigidTerm typ)) :
    forest holds [] (mapChildren literal (types.map (typeNode top))) (types.map rigidTerm) := by
  induction types with
  | nil => simp only [List.map_nil, mapChildren, forest]
  | cons first rest ih =>
      simp only [List.map_cons, mapChildren, forest]
      exact ⟨checked first List.mem_cons_self,
        ih (fun typ member => checked typ (List.mem_cons_of_mem _ member))⟩

private theorem arrow_member (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true) (argument result : Expr Guard)
    (first second : Term Symbol)
    (left : evaluate holds [] (mapSyntax literal argument) first)
    (right : evaluate holds [] (mapSyntax literal result) second) :
    evaluate holds [] (mapSyntax literal (arrowType top argument result))
      (.node (literal "->") [.node (literal "(->)") [], first, second]) := by
  apply node_member holds topHeld "->" [arrowMarker top, argument, result]
    [.node (literal "(->)") [], first, second]
  simp only [mapChildren, forest]
  exact ⟨node_member holds topHeld "(->)" [] [] (by simp only [mapChildren, forest]),
    left, right, True.intro⟩

/-- Every finite rigid source type accepts its own encoding without universe admission. -/
theorem typeNode_member (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true) (typ : Ty) :
    evaluate holds [] (mapSyntax literal (typeNode top typ)) (rigidTerm typ) := by
  induction typ using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types,
      evaluate holds [] (mapSyntax literal (typeNode top typ)) (rigidTerm typ)) with
  | tVar name =>
      simpa only [typeNode, rigidTerm] using
        node_member holds topHeld (variableSymbol name) [] [] (by simp only [mapChildren, forest])
  | tFun argument result first second =>
      simpa only [typeNode, rigidTerm] using
        arrow_member holds topHeld (typeNode top argument) (typeNode top result)
          (rigidTerm argument) (rigidTerm result) first second
  | tCons name arguments children =>
      have ordinary :
          evaluate holds [] (mapSyntax literal (.node [.mk name top (arguments.map (typeNode top))]))
            (.node (literal name) (arguments.map rigidTerm)) :=
        node_member holds topHeld name _ _ (mapped_forest holds arguments children)
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
                  · simpa only [typeNode, rigidTerm, alias, ↓reduceIte] using
                      arrow_member holds topHeld (typeNode top first) (typeNode top second)
                        (rigidTerm first) (rigidTerm second)
                        (children first (by simp)) (children second (by simp))
                  · simpa only [typeNode, rigidTerm, alias, ↓reduceIte, List.map_cons, List.map_nil] using ordinary
  | nil => rename_i typ member; cases member
  | cons first rest own later =>
      rename_i typ member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact later typ member

variable [DecidableEq FullSyntax.Formula]

/-- Structural images discharge all demanded universe premises of a complex scheme. -/
theorem generalize_member_of_TypeIn (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (catalog : List (String × Nat))
    (typ : Ty) (substitution : String → Term Symbol)
    (images : ∀ name ∈ variables typ, TypeIn catalog (substitution name)) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (generalize (allTypes top catalog) typ))
      (SourceSynthesisGeneralizeFiniteInstances.instantiate substitution typ) := by
  apply SourceSynthesisGeneralizeFiniteInstances.generalize_member formulas solver catalog typ substitution
  intro name demanded
  exact TypeIn.member (SourceEqualityPCSGuard.holds formulas solver)
    (SourceEqualityPCSConstructors.top_true formulas solver) (images name demanded)

end MicroCFTA.SourceSynthesisFiniteTypeWitnesses
