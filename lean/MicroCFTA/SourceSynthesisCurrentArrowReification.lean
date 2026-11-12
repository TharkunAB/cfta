import MicroCFTA.SourceSynthesisPr210TypeReflection

/-!
# Arrow shape of current rigid types

Every current rigid raw type excludes the internal marker leaf.
A marker at child0 therefore identifies the complete arrow layout.
The raw type is equivalent to that arrow under the documented Fun/2 alias.
These facts require no type-universe admission and apply to rigid query types.
They do not invert Program acceptance or assert runtime correspondence.
-/
namespace MicroCFTA.SourceSynthesisCurrentArrowReification
open Language
open SourceSynthesisTypeSyntax (Ty variableSymbol)
open SourceSynthesisGeneralizeSyntax (isVariableSymbol variableSymbol_recognized)
open SourceSynthesisFiniteTypeWitnesses (rigidTerm)
open SourceSynthesisPr210TypeReflection (encodeTy candidateRigid candidateRigid_eq_iff)
open SourceSynthesisPr210ConstructorEscape (escapeConstructor escapeConstructor_separate)
open SourceSynthesisOrdinaryTyping (Equivalent)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

private theorem variable_not_marker (name : String) : variableSymbol name ≠ "(->)" := by
  have noPrefix : "(->)".startsWith "var_" = false := by
    apply String.startsWith_string_eq_false_iff.mpr
    change ¬ (['v', 'a', 'r', '_'] <+: ['(', '-', '>', ')'])
    decide
  have excluded : isVariableSymbol "(->)" = false := by
    simp [isVariableSymbol, noPrefix]
  intro same
  have recognized := variableSymbol_recognized name
  rw [same, excluded] at recognized
  cases recognized

private theorem candidate_shape (typ : Ty) :
    (∃ name, candidateRigid typ = .node (literal (variableSymbol name)) []) ∨
    (∃ argument result, candidateRigid typ = .node (literal "->")
      [marker, candidateRigid argument, candidateRigid result]) ∨
    (∃ (name : String) (children : List Ty), candidateRigid typ =
      .node (literal (escapeConstructor name)) (children.map candidateRigid)) := by
  cases typ with
  | tVar name =>
      exact .inl ⟨name, by simp only [candidateRigid, encodeTy, rigidTerm]⟩
  | tFun argument result =>
      exact .inr (.inl ⟨argument, result, by simp only [candidateRigid, encodeTy, rigidTerm]⟩)
  | tCons name children =>
      have ordinary (same : candidateRigid (.tCons name children) =
          .node (literal (escapeConstructor name)) (children.map candidateRigid)) :
          (∃ raw, candidateRigid (.tCons name children) = .node (literal (variableSymbol raw)) []) ∨
          (∃ argument result, candidateRigid (.tCons name children) = .node (literal "->")
            [marker, candidateRigid argument, candidateRigid result]) ∨
          (∃ (raw : String) (arguments : List Ty), candidateRigid (.tCons name children) =
            .node (literal (escapeConstructor raw)) (arguments.map candidateRigid)) :=
        .inr (.inr ⟨name, children, same⟩)
      cases children with
      | nil => exact ordinary (by simp only [candidateRigid, encodeTy, rigidTerm, List.map_nil])
      | cons first rest =>
          cases rest with
          | nil =>
              exact ordinary
                (by simp only [candidateRigid, encodeTy, rigidTerm, List.map_cons, List.map_nil])
          | cons second rest =>
              cases rest with
              | cons third tail =>
                  apply ordinary
                  simp only [candidateRigid, encodeTy, rigidTerm, List.map_cons,
                    List.map_map, Function.comp_def]
                  rfl
              | nil =>
                  by_cases alias : escapeConstructor name = "Fun"
                  · exact .inr (.inl ⟨first, second, by
                      simp only [candidateRigid, encodeTy, rigidTerm, List.map_cons,
                        List.map_nil, alias, ↓reduceIte]⟩)
                  · exact ordinary (by simp only [candidateRigid, encodeTy, rigidTerm,
                      List.map_cons, List.map_nil, alias, ↓reduceIte])

/-- No current rigid raw type is the internal arrow marker leaf. -/
theorem candidateRigid_ne_marker (typ : Ty) :
    candidateRigid typ ≠ .node (literal "(->)") [] := by
  intro same
  rcases candidate_shape typ with ⟨name, shape⟩ | ⟨argument, result, shape⟩ | ⟨name, children, shape⟩
  · have labels := congrArg Prod.fst (Term.node.inj (shape.symm.trans same)).1
    exact variable_not_marker name labels
  · have impossible : [marker, candidateRigid argument, candidateRigid result] = [] :=
      (Term.node.inj (shape.symm.trans same)).2
    cases impossible
  · have labels := congrArg Prod.fst (Term.node.inj (shape.symm.trans same)).1
    exact (escapeConstructor_separate name).2.2 labels

/-- A marker at child0 identifies the full arrow layout, modulo the Fun/2 alias. -/
theorem marker_child_arrow (typ : Ty)
    (markerAt : (candidateRigid typ).atPath [0] = some marker) :
    ∃ argument result : Ty,
      Equivalent typ (.tFun argument result) ∧
      candidateRigid typ = .node (literal "->")
        [marker, candidateRigid argument, candidateRigid result] := by
  rcases candidate_shape typ with ⟨name, shape⟩ | ⟨argument, result, shape⟩ | ⟨name, children, shape⟩
  · have impossible : (none : Option (Term Symbol)) = some marker := by
      simpa only [shape, Term.atPath, List.getElem?_nil, Option.bind_none] using markerAt
    cases impossible
  · refine ⟨argument, result, ?_, shape⟩
    apply (candidateRigid_eq_iff typ (.tFun argument result)).mp
    have canonical : candidateRigid (.tFun argument result) = .node (literal "->")
        [marker, candidateRigid argument, candidateRigid result] := by
      simp only [candidateRigid, encodeTy, rigidTerm]
    exact shape.trans canonical.symm
  · cases children with
    | nil =>
        have impossible : (none : Option (Term Symbol)) = some marker := by
          simpa only [shape, List.map_nil, Term.atPath, List.getElem?_nil, Option.bind_none] using markerAt
        cases impossible
    | cons first rest =>
        have selected : some (candidateRigid first) = some marker := by
          simpa only [shape, List.map_cons, Term.atPath, List.getElem?_cons_zero,
            Option.bind_some] using markerAt
        exact False.elim (candidateRigid_ne_marker first (Option.some.inj selected))

end MicroCFTA.SourceSynthesisCurrentArrowReification
