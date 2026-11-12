import MicroCFTA.SourceSynthesisFirstOrderTotality
import MicroCFTA.SourceSynthesisEncodedSubstitutionLift
import MicroCFTA.NumberedTerms

/-!
# Fixed component count with unbounded finite annotations

One FirstOrder source expression accepts all terms in this family.
Every term projects to the same two-component Program.
The exact native size is twice the annotation depth plus fourteen.

The source documents unresolved annotation types as intentional behavior.
An opaque enumeration result can represent the family.
These laws do not prove divergence, a Haskell defect, or failure of a
bound on finite representatives of opaque results.
-/
namespace MicroCFTA.SourceSynthesisProgramNativeSizeUnbounded
open Language
open SourceSynthesisTypeSyntax
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisProgramTermSize (Program Projection toProgram)
open SourceSynthesisSourceTermsTyping (LeafTyping TermsTyping RelevantTyping
  oneRows fallbackFunctionRows)
open SourceSynthesisTypeSubstitutionWitnesses (AliasSafe)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

private def intTy : Ty := .tCons "Int" []
private def listTy (typ : Ty) : Ty := .tCons "List" [typ]
private def ignoreTy : Ty := .tFun (listTy (.tVar "a")) intTy
private def nilTy : Ty := listTy (.tVar "a")

private def nestedType : Nat → Ty
  | 0 => intTy
  | n + 1 => listTy (nestedType n)

/-- Keep one unpruned FirstOrder library for all annotation depths. -/
def library : Library :=
  { libraryGroups := [("ignore", ignoreTy, ["ignore"]), ("nil", nilTy, ["nil"])]
    libraryArgumentOnly := []
    libraryAvoid := []
    libraryEncoding := .firstOrder }

/-- Fix the result type and use no query arguments. -/
def query : Query :=
  { queryArguments := []
    queryGoal := intTy }

/-- Both component occurrences remain the same at every annotation depth. -/
def program : Program := .app (.var "ignore") (.var "nil")

private def marker : Term Symbol := .node (literal "(->)") []

private def functionTerm (n : Nat) : Term Symbol :=
  .node (literal "ignore")
    [.node (literal "->")
      [marker, rigidTerm (listTy (nestedType n)), rigidTerm intTy]]

private def argumentTerm (n : Nat) : Term Symbol :=
  .node (literal "nil") [rigidTerm (listTy (nestedType n))]

private def bodyTerm (n : Nat) : Term Symbol :=
  .node (literal "app") [rigidTerm intTy, marker, functionTerm n, argumentTerm n]

/-- Retain the complete source filter and both explicit type annotations. -/
def rootTerm (n : Nat) : Term Symbol :=
  .node (literal "filter") [rigidTerm intTy, bodyTerm n]

private theorem catalog_eq :
    constructorCatalog library query = [("List", 1), ("Int", 0)] := by
  simp [constructorCatalog, library, query, ignoreTy, nilTy, listTy, intTy, constructorsOf,
    List.eraseDups_cons]

private theorem int_member :
    TypeIn (constructorCatalog library query) (rigidTerm intTy) := by
  simp only [intTy, rigidTerm, List.map_nil]
  refine TypeIn.node (catalog := constructorCatalog library query) "Int" [] ?_ ?_
  · rw [catalog_eq]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · intro child member
    cases member

private theorem nested_member (n : Nat) :
    TypeIn (constructorCatalog library query) (rigidTerm (nestedType n)) := by
  induction n with
  | zero => exact int_member
  | succ n ih =>
      simp only [nestedType, listTy, rigidTerm, List.map_cons, List.map_nil]
      refine TypeIn.node (catalog := constructorCatalog library query)
        "List" [rigidTerm (nestedType n)] ?_ ?_
      · rw [catalog_eq]
        exact List.mem_cons_self
      · intro child member
        have same := List.mem_singleton.mp member
        subst child
        exact ih

private theorem nil_safe : AliasSafe nilTy := by
  rw [nilTy, listTy, AliasSafe]
  constructor
  · intro impossible
    cases impossible
  · intro child member
    have same := List.mem_singleton.mp member
    subst child
    rw [AliasSafe]
    exact True.intro

private theorem ignore_safe : AliasSafe ignoreTy := by
  rw [ignoreTy, AliasSafe]
  constructor
  · exact nil_safe
  · rw [intTy, AliasSafe]
    constructor
    · intro _empty
      rfl
    · intro child member
      cases member

private theorem body_typing (n : Nat) :
    TermsTyping library query true 2 program (rigidTerm intTy) (bodyTerm n) := by
  have functionLeaf : LeafTyping (constructorCatalog library query)
      (component (context library query).types "ignore" ignoreTy) (.var "ignore")
      (.node (literal "->") [marker, rigidTerm (listTy (nestedType n)), rigidTerm intTy])
      (functionTerm n) := by
    have actual := SourceSynthesisEncodedSubstitutionLift.component_instance_leaf
      (constructorCatalog library query) "ignore" ignoreTy (fun _ => nestedType n)
      ignore_safe (by intro raw _member; exact nested_member n)
    simpa only [ignoreTy, listTy, intTy, SourceSynthesisTypeSubstitutionWitnesses.substTy,
      List.map_cons, List.map_nil, rigidTerm, functionTerm, marker, context, typesOf] using actual
  have argumentLeaf : LeafTyping (constructorCatalog library query)
      (component (context library query).types "nil" nilTy) (.var "nil")
      (rigidTerm (listTy (nestedType n))) (argumentTerm n) := by
    have actual := SourceSynthesisEncodedSubstitutionLift.component_instance_leaf
      (constructorCatalog library query) "nil" nilTy (fun _ => nestedType n)
      nil_safe (by intro raw _member; exact nested_member n)
    simpa only [nilTy, listTy, SourceSynthesisTypeSubstitutionWitnesses.substTy,
      List.map_cons, List.map_nil, rigidTerm, argumentTerm, context, typesOf] using actual
  have selectedFunction : component (context library query).types "ignore" ignoreTy ∈
      fallbackFunctionRows (context library query) := by
    exact List.mem_cons_self
  have selectedArgument : component (context library query).types "nil" nilTy ∈
      oneRows library query true := by
    exact List.mem_cons_of_mem _ List.mem_cons_self
  exact TermsTyping.fallback selectedFunction functionLeaf
    (TermsTyping.leaf selectedArgument argumentLeaf) int_member

private theorem nested_size (n : Nat) :
    NumberedTerms.size (rigidTerm (nestedType n)) = n + 1 := by
  induction n with
  | zero =>
      simp only [nestedType, intTy, rigidTerm, List.map_nil,
        NumberedTerms.size, NumberedTerms.forestSize]
  | succ n ih =>
      simp only [nestedType, listTy, rigidTerm, List.map_cons, List.map_nil,
        NumberedTerms.size, NumberedTerms.forestSize]
      omega

private theorem root_size (n : Nat) : NumberedTerms.size (rootTerm n) = 2 * n + 14 := by
  have sized := nested_size n
  simp only [rootTerm, bodyTerm, functionTerm, argumentTerm, marker, listTy, intTy,
    rigidTerm, NumberedTerms.size, NumberedTerms.forestSize, List.map_cons, List.map_nil]
  omega

/-- One actual source expression accepts every exact two-component member of the family. -/
theorem fixed_program_unbounded_annotations [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ expression, firstOrderRaw library query (2 : Int) = .ok expression ∧
      ∀ n,
        InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) []
          (mapSyntax literal expression) (rootTerm n) ∧
        Projection literal Prod.fst (rootTerm n) program ∧
        toProgram literal Prod.fst (rootTerm n) = program ∧
        program.components = 2 ∧
        NumberedTerms.size (rootTerm n) = 2 * n + 14 := by
  obtain ⟨expression, returned⟩ :=
    SourceSynthesisFirstOrderTotality.firstOrderRaw_total library query 2 (by decide)
  refine ⟨expression, returned, ?_⟩
  intro n
  have relevant : RelevantTyping library query true 2 [] program
      (rigidTerm intTy) (bodyTerm n) :=
    .empty (SourceSynthesisSelections.resolveSelection_empty _) (body_typing n)
  obtain ⟨accepted, projected, _counted⟩ :=
    SourceSynthesisSourceRelevantTyping.firstOrderRaw_member formulas solver returned []
      (by
        change [] ∈ SourceSynthesisSelections.permutations ([] : List (String × Row))
        rw [SourceSynthesisSelections.permutations_nil]
        exact List.mem_cons_self) relevant
  exact ⟨accepted, projected, projected.toProgram_eq, rfl, root_size n⟩

/-- No native-size bound covers all these accepted terms of one fixed source expression. -/
theorem no_native_size_bound [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ expression, firstOrderRaw library query (2 : Int) = .ok expression ∧
      ∀ bound, ∃ term,
        InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) []
          (mapSyntax literal expression) term ∧
        Projection literal Prod.fst term program ∧
        toProgram literal Prod.fst term = program ∧
        program.components = 2 ∧ bound < NumberedTerms.size term := by
  obtain ⟨expression, returned, members⟩ := fixed_program_unbounded_annotations formulas solver
  refine ⟨expression, returned, ?_⟩
  intro bound
  obtain ⟨accepted, projected, decoded, counted, sized⟩ := members bound
  refine ⟨rootTerm bound, accepted, projected, decoded, counted, ?_⟩
  omega

end MicroCFTA.SourceSynthesisProgramNativeSizeUnbounded
