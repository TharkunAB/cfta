import MicroCFTA.SourceSynthesisCurrentTypeAdmission

/-!
# Raw representatives of current FirstOrder universe members

Each structural universe witness has an admitted raw type with the same
encoded term. Constructor names come from the actual current catalog.
The catalog excludes the genuine Fun/2 constructor signature.
The proof retains ordered children and uses the existing raw Ty syntax.
It does not establish whole Program soundness or native correspondence.
-/
namespace MicroCFTA.SourceSynthesisCurrentTypeReification
open Language
open InternedGuardedSyntax (evaluate)
open SourceSynthesisTypeSyntax (Ty Library Query variableSymbol)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisPr210ConstructorEscape (escapeConstructor escapeConstructor_injective)
open SourceSynthesisPr210TypeReflection (encodeTy candidateRigid)
open SourceSynthesisFiniteTypeWitnesses (TypeIn rigidTerm)
open SourceSynthesisEncodedSubstitutionLift (decodeVariable)
open SourceSynthesisCurrentContext (constructorsOf constructorCatalog context context_types)
open SourceSynthesisCurrentTypeAdmission (RawAdmitted typeIn_iff_admitted)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
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

private theorem escaped_fun_iff (name : String) :
    escapeConstructor name = "Fun" ↔ name = "Fun" := by
  constructor
  · intro same
    exact escapeConstructor_injective (same.trans escape_fun.symm)
  · rintro rfl
    exact escape_fun

private theorem constructorsOf_origin (typ : Ty) :
    ∀ entry ∈ constructorsOf typ, ∃ raw,
      entry.1 = escapeConstructor raw ∧ ¬(entry.1 = "Fun" ∧ entry.2 = 2) := by
  induction typ using Ty.rec
    (motive_2 := fun types => ∀ typ ∈ types, ∀ entry ∈ constructorsOf typ, ∃ raw,
      entry.1 = escapeConstructor raw ∧ ¬(entry.1 = "Fun" ∧ entry.2 = 2)) with
  | tVar _ =>
      intro entry member
      simp only [constructorsOf, List.not_mem_nil] at member
  | tFun _ _ first second =>
      intro entry member
      rw [constructorsOf] at member
      rcases List.mem_append.mp member with own | later
      · exact first entry own
      · exact second entry later
  | tCons name children childIH =>
      intro entry member
      rw [constructorsOf] at member
      rcases List.mem_append.mp member with own | later
      · by_cases alias : name = "Fun" ∧ children.length = 2
        · rw [ite_eq_left alias] at own
          cases own
        · have same : entry = (escapeConstructor name, children.length) := by
            simpa only [alias, ↓reduceIte, List.mem_singleton] using own
          subst entry
          refine ⟨name, rfl, ?_⟩
          rintro ⟨encodedFun, arity⟩
          exact alias ⟨(escaped_fun_iff name).mp encodedFun, arity⟩
      · obtain ⟨child, present, occurs⟩ := List.mem_flatMap.mp later
        exact childIH child present entry occurs
  | nil =>
      rename_i typ member entry occurs
      cases member
  | cons _ _ own later =>
      rename_i typ member entry occurs
      rcases List.mem_cons.mp member with rfl | member
      · exact own entry occurs
      · exact later typ member entry occurs

private theorem catalog_origin (lib : Library) (query : Query)
    (entry : String × Nat) (member : entry ∈ constructorCatalog lib query) :
    ∃ raw, entry.1 = escapeConstructor raw ∧ ¬(entry.1 = "Fun" ∧ entry.2 = 2) := by
  simp only [constructorCatalog, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    or_assoc] at member
  rcases member with ⟨source, _present, found⟩ | ⟨source, _present, found⟩ |
    ⟨source, _present, found⟩ | found
  · exact constructorsOf_origin source.2.1 entry found
  · exact constructorsOf_origin source.2 entry found
  · exact constructorsOf_origin source.2 entry found
  · exact constructorsOf_origin query.queryGoal entry found

private theorem candidate_constructor (name : String) (arguments : List Ty)
    (ordinary : ¬(escapeConstructor name = "Fun" ∧ arguments.length = 2)) :
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
              have notFun : escapeConstructor name ≠ "Fun" := by
                intro same
                exact ordinary ⟨same, rfl⟩
              simp only [candidateRigid, encodeTy, rigidTerm, List.map_cons, List.map_nil,
                notFun, ↓reduceIte]

private theorem reify_children (children : List (Term Symbol))
    (checked : ∀ child ∈ children, ∃ typ, candidateRigid typ = child) :
    ∃ types : List Ty, types.map candidateRigid = children := by
  induction children with
  | nil => exact ⟨[], rfl⟩
  | cons child rest ih =>
      obtain ⟨typ, own⟩ := checked child List.mem_cons_self
      obtain ⟨types, later⟩ := ih (fun term member => checked term (List.mem_cons_of_mem _ member))
      exact ⟨typ :: types, by simp only [List.map_cons, own, later]⟩

private theorem exists_raw (lib : Library) (query : Query) (term : Term Symbol)
    (admitted : TypeIn (constructorCatalog lib query) term) :
    ∃ typ, candidateRigid typ = term := by
  induction admitted with
  | leaf name present =>
      have inverse : variableSymbol (decodeVariable name) = name := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at present
        rcases present with rfl | rfl | rfl | rfl <;> rfl
      refine ⟨.tVar (decodeVariable name), ?_⟩
      simp only [candidateRigid, encodeTy, rigidTerm, inverse]
  | node name children present _checked ih =>
      obtain ⟨rawName, names, ordinary⟩ := catalog_origin lib query (name, children.length) present
      obtain ⟨types, encoded⟩ := reify_children children ih
      have length : types.length = children.length := by
        have sizes := congrArg List.length encoded
        simpa only [List.length_map] using sizes
      have notAlias : ¬(escapeConstructor rawName = "Fun" ∧ types.length = 2) := by
        rw [← names, length]
        exact ordinary
      refine ⟨.tCons rawName types, ?_⟩
      rw [candidate_constructor rawName types notAlias, encoded, ← names]
  | arrow argument result _first _second firstIH secondIH =>
      obtain ⟨rawArgument, first⟩ := firstIH
      obtain ⟨rawResult, second⟩ := secondIH
      refine ⟨.tFun rawArgument rawResult, ?_⟩
      have shape : candidateRigid (.tFun rawArgument rawResult) =
          .node (literal "->") [marker, candidateRigid rawArgument, candidateRigid rawResult] := by
        simp only [candidateRigid, encodeTy, rigidTerm]
      rw [shape, first, second]

/-- Every current structural universe term is the encoding of an admitted raw type. -/
theorem typeIn_reify (lib : Library) (query : Query) (term : Term Symbol)
    (admitted : TypeIn (constructorCatalog lib query) term) :
    ∃ typ, RawAdmitted (constructorCatalog lib query) typ ∧ candidateRigid typ = term := by
  obtain ⟨typ, same⟩ := exists_raw lib query term admitted
  have encoded : TypeIn (constructorCatalog lib query) (candidateRigid typ) := by
    rw [same]
    exact admitted
  exact ⟨typ, (typeIn_iff_admitted lib query typ).mp encoded, same⟩

/-- Current type-syntax membership has an admitted raw representative of the same term. -/
theorem universe_reify (holds : Guard → Term Symbol → Bool)
    (topHeld : ∀ term, holds top term = true)
    (lib : Library) (query : Query) (term : Term Symbol)
    (member : evaluate holds [] (mapSyntax literal (context lib query).types) term) :
    ∃ typ, RawAdmitted (constructorCatalog lib query) typ ∧ candidateRigid typ = term := by
  rw [context_types] at member
  exact typeIn_reify lib query term
    ((SourceSynthesisTypeUniverseExact.allTypes_member_iff_TypeIn
      holds topHeld (constructorCatalog lib query) term).mp member)

end MicroCFTA.SourceSynthesisCurrentTypeReification
