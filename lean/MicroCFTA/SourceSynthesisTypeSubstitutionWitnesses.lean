import MicroCFTA.SourceSynthesisSourceTermsTyping
import Lean.Elab.Tactic.Simp

/-!
# Ordinary type substitution at actual source leaves

Raw substitution replaces each original type variable once. A compatibility
condition excludes original constant leaves that source generalization
recognizes as encoded variables. It does not change the public input domain.
Each component occurrence supplies its own raw and encoded substitutions.

These laws derive literal source leaves and size-one terms from current
bindings. They do not define conventional Program typing or prove its full
source admissibility. Encoded substitution lifting remains explicit. Rigid
query arguments need no type-universe premise.
-/
namespace MicroCFTA.SourceSynthesisTypeSubstitutionWitnesses
open Language
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (top variables isVariableSymbol)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisGeneralizeFiniteInstances (instantiate)
open SourceSynthesisSourceTermsTyping (LeafTyping TermsTyping argumentOnlyRows oneRows)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

/-- Substitute raw variable names once, without descending into inserted images. -/
def substTy (substitution : String → Ty) : Ty → Ty
  | .tVar name => substitution name
  | .tFun argument result => .tFun (substTy substitution argument) (substTy substitution result)
  | .tCons name children => .tCons name (children.map (substTy substitution))

/-- Original constant leaves must not be recognized as encoded source variables. -/
def AliasSafe : Ty → Prop
  | .tVar _ => True
  | .tFun argument result => AliasSafe argument ∧ AliasSafe result
  | .tCons name children =>
      (children = [] → isVariableSymbol name = false) ∧ (∀ child ∈ children, AliasSafe child)

-- Obtain the private worker from its public wrapper. Use no generated private name.
private def unfoldVariableWorker : Lean.Elab.Tactic.TacticM Unit := do
  let definition ← Lean.getConstInfoDefn ``typeVariables
  let worker := definition.value.bindingBody!.getAppArgs.back!.getAppFn.constName!
  let some equations ← Lean.Meta.getEqnsFor? worker
    | throwError "The typeVariables worker has no constructor equations"
  let mut rules : Lean.Meta.SimpTheorems := {}
  for equation in equations do
    rules ← rules.addConst equation
  let context ← Lean.Meta.Simp.mkContext (simpTheorems := #[rules])
    (congrTheorems := ← Lean.Meta.getSimpCongrTheorems)
  let (remaining, _) ← Lean.Meta.simpTarget (← Lean.Elab.Tactic.getMainGoal) context
  Lean.Elab.Tactic.replaceMainGoal remaining.toList

private theorem typeVariables_fun_member (name : String) (argument result : Ty) :
    name ∈ typeVariables (.tFun argument result) ↔
      name ∈ typeVariables argument ∨ name ∈ typeVariables result := by
  simp only [typeVariables, List.mem_eraseDups]
  run_tac unfoldVariableWorker
  exact List.mem_append

private theorem typeVariables_child_member (name constructorName : String)
    (children : List Ty) (child : Ty) (included : child ∈ children)
    (member : name ∈ typeVariables child) : name ∈ typeVariables (.tCons constructorName children) := by
  simp only [typeVariables, List.mem_eraseDups] at member ⊢
  run_tac unfoldVariableWorker
  exact List.mem_flatMap.mpr ⟨child, included, member⟩

/-- Compatible variable images make ordinary substitution agree with source instantiation. -/
theorem instantiate_rigid_of_compatible (scheme : Ty) (rho : String → Ty)
    (sigma : String → Term Symbol) (safe : AliasSafe scheme)
    (coherent : ∀ name ∈ typeVariables scheme, sigma (variableSymbol name) = rigidTerm (rho name)) :
    instantiate sigma scheme = rigidTerm (substTy rho scheme) := by
  revert safe coherent
  induction scheme using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types, AliasSafe typ →
      (∀ name ∈ typeVariables typ, sigma (variableSymbol name) = rigidTerm (rho name)) →
      instantiate sigma typ = rigidTerm (substTy rho typ)) with
  | tVar name =>
      intro _safe coherent
      have member : name ∈ typeVariables (.tVar name) := by
        simp only [typeVariables, List.mem_eraseDups]
        run_tac unfoldVariableWorker
        exact List.mem_cons_self
      simpa only [instantiate, substTy] using coherent name member
  | tFun argument result first second =>
      intro safe coherent
      simp only [AliasSafe] at safe
      have firstEq := first safe.1 (fun name member => coherent name
        ((typeVariables_fun_member name argument result).mpr (.inl member)))
      have secondEq := second safe.2 (fun name member => coherent name
        ((typeVariables_fun_member name argument result).mpr (.inr member)))
      simp only [instantiate, substTy, rigidTerm]
      change Term.node (literal "->") [marker, instantiate sigma argument, instantiate sigma result] =
        Term.node (literal "->") [marker, rigidTerm (substTy rho argument), rigidTerm (substTy rho result)]
      rw [firstEq, secondEq]
  | tCons name arguments children =>
      intro safe coherent
      simp only [AliasSafe] at safe
      have checked : ∀ typ ∈ arguments, instantiate sigma typ = rigidTerm (substTy rho typ) := by
        intro typ member
        exact children typ member (safe.2 typ member) (fun key included => coherent key
          (typeVariables_child_member key name arguments typ member included))
      have mapped : arguments.map (instantiate sigma) = (arguments.map (substTy rho)).map rigidTerm := by
        rw [List.map_map]
        apply List.map_congr_left
        intro typ member
        exact checked typ member
      have ordinary := congrArg (fun terms => Term.node (literal name) terms) mapped
      cases arguments with
      | nil =>
          have notVariable := safe.1 rfl
          simp only [instantiate, substTy, rigidTerm, notVariable, Bool.false_eq_true, ↓reduceIte,
            List.map_nil]
      | cons first rest =>
          cases rest with
          | nil => simpa only [instantiate, substTy, rigidTerm, List.map_cons, List.map_nil] using ordinary
          | cons second rest =>
              cases rest with
              | cons third tail =>
                  simpa only [instantiate, substTy, rigidTerm, List.map_cons, List.map_nil] using ordinary
              | nil =>
                  by_cases alias : name = "Fun"
                  · subst name
                    have firstEq := checked first (by simp)
                    have secondEq := checked second (by simp)
                    simp only [instantiate, substTy, rigidTerm, List.map_cons, List.map_nil, ↓reduceIte]
                    change Term.node (literal "->") [marker, instantiate sigma first, instantiate sigma second] =
                      Term.node (literal "->") [marker, rigidTerm (substTy rho first), rigidTerm (substTy rho second)]
                    rw [firstEq, secondEq]
                  · simpa only [instantiate, substTy, rigidTerm, alias, ↓reduceIte, List.map_cons,
                      List.map_nil] using ordinary
  | nil =>
      rename_i typ member _safe _coherent
      cases member
  | cons first rest own later =>
      rename_i typ member safe coherent
      rcases List.mem_cons.mp member with rfl | member
      · exact own safe coherent
      · exact later typ member safe coherent

/-- One component instance has its conventional rigid annotation and literal leaf value. -/
theorem component_instance_leaf (catalog : List (String × Nat)) (name : String) (scheme : Ty)
    (rho : String → Ty) (sigma : String → Term Symbol) (safe : AliasSafe scheme)
    (coherent : ∀ key ∈ typeVariables scheme, sigma (variableSymbol key) = rigidTerm (rho key))
    (images : ∀ key ∈ variables scheme, TypeIn catalog (sigma key)) :
    LeafTyping catalog (component (allTypes top catalog) name scheme) (.var name)
      (rigidTerm (substTy rho scheme)) (.node (literal name) [rigidTerm (substTy rho scheme)]) := by
  have typed := LeafTyping.component (catalog := catalog) name scheme sigma images
  rw [instantiate_rigid_of_compatible scheme rho sigma safe coherent] at typed
  exact typed

/-- An actual group binding supplies a size-one source term at either role flag. -/
theorem component_instance_terms (lib : Library) (query : Query) (asArgument : Bool)
    (entry : String × Ty × List String) (binding : entry ∈ lib.libraryGroups)
    (rho : String → Ty) (sigma : String → Term Symbol) (safe : AliasSafe entry.2.1)
    (coherent : ∀ key ∈ typeVariables entry.2.1, sigma (variableSymbol key) = rigidTerm (rho key))
    (images : ∀ key ∈ variables entry.2.1, TypeIn (constructorCatalog lib query) (sigma key)) :
    TermsTyping lib query asArgument 1 (.var entry.1) (rigidTerm (substTy rho entry.2.1))
      (.node (literal entry.1) [rigidTerm (substTy rho entry.2.1)]) := by
  let row := component (context lib query).types entry.1 entry.2.1
  have selected : row ∈ (context lib query).components.map Prod.snd :=
    List.mem_map.mpr ⟨(entry.1, row), List.mem_map.mpr ⟨entry, binding, rfl⟩, rfl⟩
  apply TermsTyping.leaf (row := row)
  · unfold oneRows
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr selected)))
  · exact component_instance_leaf (constructorCatalog lib query) entry.1 entry.2.1 rho sigma safe coherent images

/-- An actual argument-only binding supplies a size-one term with its required true flag. -/
theorem argumentOnly_instance_terms (lib : Library) (query : Query)
    (entry : String × Ty) (binding : entry ∈ lib.libraryArgumentOnly)
    (rho : String → Ty) (sigma : String → Term Symbol) (safe : AliasSafe entry.2)
    (coherent : ∀ key ∈ typeVariables entry.2, sigma (variableSymbol key) = rigidTerm (rho key))
    (images : ∀ key ∈ variables entry.2, TypeIn (constructorCatalog lib query) (sigma key)) :
    TermsTyping lib query true 1 (.var entry.1) (rigidTerm (substTy rho entry.2))
      (.node (literal entry.1) [rigidTerm (substTy rho entry.2)]) := by
  apply TermsTyping.leaf (row := component (context lib query).types entry.1 entry.2)
  · unfold oneRows
    apply List.mem_append.mpr
    apply Or.inr
    change component (context lib query).types entry.1 entry.2 ∈ argumentOnlyRows lib query
    exact List.mem_map.mpr ⟨entry, binding, rfl⟩
  · exact component_instance_leaf (constructorCatalog lib query) entry.1 entry.2 rho sigma safe coherent images

/-- An actual rigid query binding supplies a size-one term without universe admission. -/
theorem query_argument_terms (lib : Library) (query : Query) (asArgument : Bool)
    (entry : String × Ty) (binding : entry ∈ query.queryArguments) :
    TermsTyping lib query asArgument 1 (.var entry.1) (rigidTerm entry.2)
      (.node (literal entry.1) [rigidTerm entry.2]) := by
  let row : Row := .mk entry.1 top [typeNode top entry.2]
  have selected : row ∈ (context lib query).argumentEdges.map Prod.snd :=
    List.mem_map.mpr ⟨(entry.1, row), List.mem_map.mpr ⟨entry, binding, rfl⟩, rfl⟩
  apply TermsTyping.leaf (row := row)
  · unfold oneRows
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl selected)))
  · exact LeafTyping.argument (catalog := constructorCatalog lib query) entry.1 entry.2

end MicroCFTA.SourceSynthesisTypeSubstitutionWitnesses
