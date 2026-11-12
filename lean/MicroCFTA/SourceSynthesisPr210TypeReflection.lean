import MicroCFTA.SourceSynthesisPr210ConstructorEscape
import MicroCFTA.SourceSynthesisEncodedSubstitutionLift
import MicroCFTA.SourceSynthesisOrdinaryTyping

/-!
# FirstOrder rigid types in the PR 210 candidate encoding

The candidate source head is 79f74df2c3c9d3c864e57a960cb64c8c28883ec9.
PR 210 is merged. Historical encoders stay unchanged.
The decoder recovers raw types up to the documented Fun/2 arrow alias.
It is not a validator for arbitrary native terms or guards.
-/
namespace MicroCFTA.SourceSynthesisPr210TypeReflection
open Language
open SourceSynthesisTypeSyntax (Ty variableSymbol)
open SourceSynthesisGeneralizeSyntax (isVariableSymbol variableSymbol_recognized)
open SourceSynthesisPr210ConstructorEscape
  (escapeConstructor decodeConstructor decode_escapeConstructor
    escapeConstructor_injective escapeConstructor_separate)
open SourceSynthesisEncodedSubstitutionLift (decodeVariable decode_variableSymbol)
open SourceSynthesisFiniteTypeWitnesses (rigidTerm)
open SourceSynthesisOrdinaryTyping (normalizeTy Equivalent)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

private theorem escape_fun : escapeConstructor "Fun" = "Fun" := by
  have variablePrefix : "Fun".startsWith "var_" = false := by
    apply String.startsWith_string_eq_false_iff.mpr
    change ¬ (['v', 'a', 'r', '_'] <+: ['F', 'u', 'n'])
    decide
  have constructorPrefix : "Fun".startsWith "con:" = false := by
    apply String.startsWith_string_eq_false_iff.mpr
    change ¬ (['c', 'o', 'n', ':'] <+: ['F', 'u', 'n'])
    decide
  simp [escapeConstructor, variablePrefix, constructorPrefix]

private theorem escape_fun_iff (name : String) :
    escapeConstructor name = "Fun" ↔ name = "Fun" := by
  constructor
  · intro same
    exact escapeConstructor_injective (same.trans escape_fun.symm)
  · rintro rfl
    exact escape_fun

/-- Change constructor names and retain every raw variable and ordered argument. -/
def encodeTy : Ty → Ty
  | .tVar name => .tVar name
  | .tFun argument result => .tFun (encodeTy argument) (encodeTy result)
  | .tCons name children => .tCons (escapeConstructor name) (children.map encodeTy)

/-- Use the historical rigid tree encoder on the candidate constructor names. -/
def candidateRigid (typ : Ty) : Term Symbol := rigidTerm (encodeTy typ)

/-- Decode candidate type trees; other finite trees have an arbitrary raw result. -/
def decodeType : Term Symbol → Ty
  | .node symbol children =>
      if isVariableSymbol symbol.1 && children.isEmpty then
        .tVar (decodeVariable symbol.1)
      else if symbol.1 = "->" then
        match children with
        | [_marker, argument, result] => .tFun (decodeType argument) (decodeType result)
        | others => .tCons (decodeConstructor symbol.1) (others.map decodeType)
      else .tCons (decodeConstructor symbol.1) (children.map decodeType)

private theorem decode_variable (name : String) :
    decodeType (.node (literal (variableSymbol name)) []) = .tVar name := by
  simp [decodeType, SourceSynthesisLabelProgramBuildRoles.literal,
    variableSymbol_recognized, decode_variableSymbol]

private theorem decode_arrow (argument result : Term Symbol) :
    decodeType (.node (literal "->") [marker, argument, result]) =
      .tFun (decodeType argument) (decodeType result) := by
  simp [decodeType, SourceSynthesisLabelProgramBuildRoles.literal]

private theorem decode_constructor (name : String) (children : List (Term Symbol)) :
    decodeType (.node (literal (escapeConstructor name)) children) =
      .tCons name (children.map decodeType) := by
  have separated := escapeConstructor_separate name
  rcases children with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;>
    simp [decodeType, SourceSynthesisLabelProgramBuildRoles.literal,
      separated.1, separated.2.1, decode_escapeConstructor]

private theorem type_properties (typ : Ty) :
    decodeType (candidateRigid typ) = normalizeTy typ ∧
      normalizeTy (encodeTy typ) = encodeTy (normalizeTy typ) := by
  induction typ using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types,
      decodeType (candidateRigid typ) = normalizeTy typ ∧
        normalizeTy (encodeTy typ) = encodeTy (normalizeTy typ)) with
  | tVar name =>
      constructor
      · simpa only [candidateRigid, encodeTy, rigidTerm, normalizeTy] using decode_variable name
      · simp only [encodeTy, normalizeTy]
  | tFun argument result first second =>
      simp only [candidateRigid] at first second
      constructor
      · simp only [candidateRigid, encodeTy, rigidTerm, normalizeTy, decode_arrow]
        rw [first.1, second.1]
      · simp only [encodeTy, normalizeTy]
        rw [first.2, second.2]
  | tCons name arguments children =>
      have decodedMap : (arguments.map candidateRigid).map decodeType = arguments.map normalizeTy := by
        rw [List.map_map]
        apply List.map_congr_left
        intro typ member
        exact (children typ member).1
      have normalizedMap : (arguments.map encodeTy).map normalizeTy =
          (arguments.map normalizeTy).map encodeTy := by
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro typ member
        exact (children typ member).2
      have decodedOrdinary := congrArg (Ty.tCons name) decodedMap
      have normalizedOrdinary := congrArg (Ty.tCons (escapeConstructor name)) normalizedMap
      cases arguments with
      | nil =>
          constructor
          · simp only [candidateRigid, encodeTy, List.map_nil, rigidTerm, normalizeTy, decode_constructor]
          · simp only [encodeTy, normalizeTy, List.map_nil]
      | cons first rest =>
          cases rest with
          | nil =>
              constructor
              · simpa only [candidateRigid, encodeTy, List.map_cons, List.map_nil,
                  rigidTerm, normalizeTy, decode_constructor] using decodedOrdinary
              · simpa only [encodeTy, normalizeTy, List.map_cons, List.map_nil] using normalizedOrdinary
          | cons second rest =>
              cases rest with
              | cons third tail =>
                  constructor
                  · simpa only [candidateRigid, encodeTy, List.map_cons, List.map_nil,
                      rigidTerm, normalizeTy, decode_constructor, List.map_map,
                      Function.comp_def] using decodedOrdinary
                  · simpa only [encodeTy, normalizeTy, List.map_cons, List.map_nil] using normalizedOrdinary
              | nil =>
                  have firstProperties := children first (by simp)
                  have secondProperties := children second (by simp)
                  simp only [candidateRigid] at firstProperties secondProperties
                  by_cases alias : name = "Fun"
                  · subst name
                    constructor
                    · simp only [candidateRigid, encodeTy, List.map_cons, List.map_nil, escape_fun,
                        rigidTerm, normalizeTy, ↓reduceIte, decode_arrow]
                      rw [firstProperties.1, secondProperties.1]
                    · simp only [encodeTy, List.map_cons, List.map_nil, escape_fun, normalizeTy, ↓reduceIte]
                      rw [firstProperties.2, secondProperties.2]
                  · have escapedOrdinary : escapeConstructor name ≠ "Fun" := by
                      intro same
                      exact alias ((escape_fun_iff name).mp same)
                    constructor
                    · simpa only [candidateRigid, encodeTy, List.map_cons, List.map_nil, rigidTerm,
                        normalizeTy, alias, escapedOrdinary, ↓reduceIte, decode_constructor] using decodedOrdinary
                    · simpa only [encodeTy, normalizeTy, List.map_cons, List.map_nil,
                        alias, escapedOrdinary, ↓reduceIte] using normalizedOrdinary
  | nil =>
      rename_i typ member
      cases member
  | cons first rest own later =>
      rename_i typ member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact later typ member

/-- Decoding recovers every raw FirstOrder type up to its documented arrow alias. -/
theorem decode_candidateRigid (typ : Ty) :
    decodeType (candidateRigid typ) = normalizeTy typ :=
  (type_properties typ).1

/-- Candidate FirstOrder tree equality is exactly ordinary raw-type equivalence. -/
theorem candidateRigid_eq_iff (first second : Ty) :
    candidateRigid first = candidateRigid second ↔ Equivalent first second := by
  constructor
  · intro same
    have decoded := congrArg decodeType same
    simpa only [Equivalent, decode_candidateRigid] using decoded
  · intro same
    change normalizeTy first = normalizeTy second at same
    have respects (typ : Ty) : candidateRigid (normalizeTy typ) = candidateRigid typ := by
      unfold candidateRigid
      rw [← (type_properties typ).2]
      exact SourceSynthesisOrdinaryTyping.rigidTerm_normalize (encodeTy typ)
    have normalized := congrArg candidateRigid same
    rw [respects first, respects second] at normalized
    exact normalized

end MicroCFTA.SourceSynthesisPr210TypeReflection
