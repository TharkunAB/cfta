import MicroCFTA.SourceSynthesisCurrentContext
import MicroCFTA.SourceSynthesisTypeUniverseExact

/-!
# Exact raw type admission in the current FirstOrder universe

RawAdmitted checks the four rigid variable names and current constructor
signatures at each occurrence. Only Fun with two arguments is an arrow alias.
The current catalog supplies tag separation without an input restriction.
These laws concern demanded substitution images and application results.
They do not require every rigid query or goal type to enter the universe.
-/
namespace MicroCFTA.SourceSynthesisCurrentTypeAdmission
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax (Ty Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top isVariableSymbol variableSymbol_recognized)
open SourceSynthesisPr210ConstructorEscape
  (escapeConstructor escapeConstructor_injective escapeConstructor_separate)
open SourceSynthesisPr210TypeReflection (encodeTy candidateRigid)
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisEncodedSubstitutionLift (decodeVariable decode_variableSymbol)
open SourceSynthesisCurrentContext (constructorCatalog constructorCatalog_separate context context_types)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

/-- Check raw variables and each current signature, with the Fun/2 arrow alias. -/
def RawAdmitted (catalog : List (String × Nat)) : Ty → Prop
  | .tVar name => name ∈ ["a", "b", "c", "d"]
  | .tFun argument result => RawAdmitted catalog argument ∧ RawAdmitted catalog result
  | .tCons name children =>
      (if name = "Fun" ∧ children.length = 2 then True
       else (escapeConstructor name, children.length) ∈ catalog) ∧
      ∀ child ∈ children, RawAdmitted catalog child

private theorem node_shape {first second : String} {left right : List (Term Symbol)}
    (same : Term.node (literal first) left = .node (literal second) right) :
    first = second ∧ left = right := by
  have parts := Term.node.inj same
  exact ⟨congrArg Prod.fst parts.1, parts.2⟩

private theorem typeIn_cases (catalog : List (String × Nat)) (term : Term Symbol)
    (admitted : TypeIn catalog term) :
    (∃ name, name ∈ ["var1", "var2", "var3", "var4"] ∧ term = .node (literal name) []) ∨
    (∃ name children, (name, children.length) ∈ catalog ∧
      (∀ child ∈ children, TypeIn catalog child) ∧ term = .node (literal name) children) ∨
    (∃ argument result, TypeIn catalog argument ∧ TypeIn catalog result ∧
      term = .node (literal "->") [marker, argument, result]) := by
  cases admitted with
  | leaf name present => exact .inl ⟨name, present, rfl⟩
  | node name children present checked => exact .inr (.inl ⟨name, children, present, checked, rfl⟩)
  | arrow argument result first second => exact .inr (.inr ⟨argument, result, first, second, rfl⟩)

private theorem variable_typeIn_iff (lib : Library) (query : Query) (raw : String) :
    TypeIn (constructorCatalog lib query)
      (.node (literal (SourceSynthesisTypeSyntax.variableSymbol raw)) []) ↔
      raw ∈ ["a", "b", "c", "d"] := by
  constructor
  · intro admitted
    rcases typeIn_cases _ _ admitted with ⟨name, present, same⟩ |
      ⟨name, children, present, _checked, same⟩ |
      ⟨argument, result, _first, _second, same⟩
    · have encoded : SourceSynthesisTypeSyntax.variableSymbol raw ∈
          ["var1", "var2", "var3", "var4"] := by
        rw [(node_shape same).1]
        exact present
      have decoded := List.mem_map_of_mem (f := decodeVariable) encoded
      rw [decode_variableSymbol] at decoded
      simpa only [List.map_cons, List.map_nil, decodeVariable] using decoded
    · have separated := constructorCatalog_separate lib query (name, children.length) present
      have recognized : isVariableSymbol name = true := by
        rw [← (node_shape same).1]
        exact variableSymbol_recognized raw
      have impossible := separated.1
      rw [recognized] at impossible
      cases impossible
    · have impossible := (node_shape same).2
      cases impossible
  · intro present
    apply TypeIn.leaf
    simpa only [List.map_cons, List.map_nil, SourceSynthesisTypeSyntax.variableSymbol] using
      List.mem_map_of_mem (f := SourceSynthesisTypeSyntax.variableSymbol) present

private theorem arrow_typeIn_iff (lib : Library) (query : Query)
    (argument result : Term Symbol) :
    TypeIn (constructorCatalog lib query) (.node (literal "->") [marker, argument, result]) ↔
      TypeIn (constructorCatalog lib query) argument ∧ TypeIn (constructorCatalog lib query) result := by
  constructor
  · intro admitted
    rcases typeIn_cases _ _ admitted with ⟨name, _present, same⟩ |
      ⟨name, children, present, _checked, same⟩ |
      ⟨first, second, firstIn, secondIn, same⟩
    · have impossible := (node_shape same).2
      cases impossible
    · have separated := constructorCatalog_separate lib query (name, children.length) present
      exact False.elim (separated.2.1 (node_shape same).1.symm)
    · have children := (node_shape same).2
      have firstSame := (List.cons.inj (List.cons.inj children).2).1
      have secondSame := (List.cons.inj (List.cons.inj (List.cons.inj children).2).2).1
      rw [firstSame, secondSame]
      exact ⟨firstIn, secondIn⟩
  · rintro ⟨first, second⟩
    exact TypeIn.arrow argument result first second

private theorem constructor_typeIn_iff (lib : Library) (query : Query)
    (name : String) (children : List (Term Symbol)) :
    TypeIn (constructorCatalog lib query) (.node (literal (escapeConstructor name)) children) ↔
      (escapeConstructor name, children.length) ∈ constructorCatalog lib query ∧
        ∀ child ∈ children, TypeIn (constructorCatalog lib query) child := by
  constructor
  · intro admitted
    rcases typeIn_cases _ _ admitted with ⟨key, present, same⟩ |
      ⟨key, terms, present, checked, same⟩ |
      ⟨argument, result, _first, _second, same⟩
    · have recognized : isVariableSymbol key = true := by
        simp [isVariableSymbol, present]
      have impossible := (escapeConstructor_separate name).1
      rw [(node_shape same).1, recognized] at impossible
      cases impossible
    · have names := (node_shape same).1
      have termsSame := (node_shape same).2
      rw [← names, ← termsSame] at present
      rw [← termsSame] at checked
      exact ⟨present, checked⟩
    · exact False.elim ((escapeConstructor_separate name).2.1 (node_shape same).1)
  · rintro ⟨present, checked⟩
    exact TypeIn.node (escapeConstructor name) children present checked

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

private theorem escaped_fun_iff (name : String) :
    escapeConstructor name = "Fun" ↔ name = "Fun" := by
  constructor
  · intro same
    exact escapeConstructor_injective (same.trans escape_fun.symm)
  · rintro rfl
    exact escape_fun

private theorem rigid_constructor (name : String) (arguments : List Ty)
    (ordinary : ¬(name = "Fun" ∧ arguments.length = 2)) :
    candidateRigid (.tCons name arguments) =
      .node (literal (escapeConstructor name)) (arguments.map candidateRigid) := by
  cases arguments with
  | nil => simp only [candidateRigid, encodeTy, rigidTerm, List.map_nil]
  | cons first rest =>
      cases rest with
      | nil => simp only [candidateRigid, encodeTy, rigidTerm, List.map_cons, List.map_nil]
      | cons second rest =>
          cases rest with
          | cons third tail =>
              simp only [candidateRigid, encodeTy, rigidTerm, List.map_cons,
                List.map_map, Function.comp_def]
              rfl
          | nil =>
              have notFun : name ≠ "Fun" := by
                intro same
                exact ordinary ⟨same, rfl⟩
              have escapedNotFun : escapeConstructor name ≠ "Fun" := by
                intro same
                exact notFun ((escaped_fun_iff name).mp same)
              simp only [candidateRigid, encodeTy, rigidTerm, List.map_cons, List.map_nil,
                escapedNotFun, ↓reduceIte]

/-- Current universe witnesses are exactly the structural raw admission criterion. -/
theorem typeIn_iff_admitted (lib : Library) (query : Query) (typ : Ty) :
    TypeIn (constructorCatalog lib query) (candidateRigid typ) ↔
      RawAdmitted (constructorCatalog lib query) typ := by
  induction typ using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types,
      TypeIn (constructorCatalog lib query) (candidateRigid typ) ↔
        RawAdmitted (constructorCatalog lib query) typ) with
  | tVar name =>
      simpa only [candidateRigid, encodeTy, rigidTerm, RawAdmitted] using
        variable_typeIn_iff lib query name
  | tFun argument result first second =>
      have shape : candidateRigid (.tFun argument result) =
          .node (literal "->") [marker, candidateRigid argument, candidateRigid result] := by
        simp only [candidateRigid, encodeTy, rigidTerm]
      rw [shape, arrow_typeIn_iff]
      simpa only [RawAdmitted] using and_congr first second
  | tCons name arguments children =>
      by_cases alias : name = "Fun" ∧ arguments.length = 2
      · obtain ⟨rfl, length⟩ := alias
        obtain ⟨argument, result, rfl⟩ : ∃ first second, arguments = [first, second] :=
          ⟨_, _, List.eq_getElem_of_length_eq_two arguments length⟩
        have first := children argument (by simp)
        have second := children result (by simp)
        have shape : candidateRigid (.tCons "Fun" [argument, result]) =
            .node (literal "->") [marker, candidateRigid argument, candidateRigid result] := by
          simp only [candidateRigid, encodeTy, rigidTerm, List.map_cons, List.map_nil,
            escape_fun, ↓reduceIte]
        rw [shape, arrow_typeIn_iff]
        simpa [RawAdmitted] using and_congr first second
      · have mapped :
            (∀ child ∈ arguments.map candidateRigid, TypeIn (constructorCatalog lib query) child) ↔
              ∀ child ∈ arguments, RawAdmitted (constructorCatalog lib query) child := by
          constructor
          · intro admitted child member
            exact (children child member).mp
              (admitted _ (List.mem_map_of_mem (f := candidateRigid) member))
          · intro admitted term member
            obtain ⟨child, present, rfl⟩ := List.mem_map.mp member
            exact (children child present).mpr (admitted child present)
        rw [rigid_constructor name arguments alias, constructor_typeIn_iff]
        simp only [RawAdmitted, alias, ↓reduceIte, List.length_map]
        exact and_congr Iff.rfl mapped
  | nil =>
      rename_i typ member
      cases member
  | cons first rest own later =>
      rename_i typ member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact later typ member

/-- The same criterion characterizes the actual current context's type syntax. -/
theorem universe_member_iff_admitted (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true)
    (lib : Library) (query : Query) (typ : Ty) :
    evaluate holds [] (mapSyntax literal (context lib query).types) (candidateRigid typ) ↔
      RawAdmitted (constructorCatalog lib query) typ := by
  rw [context_types]
  exact (SourceSynthesisTypeUniverseExact.allTypes_member_iff_TypeIn
    holds topHeld (constructorCatalog lib query) (candidateRigid typ)).trans
      (typeIn_iff_admitted lib query typ)

end MicroCFTA.SourceSynthesisCurrentTypeAdmission
