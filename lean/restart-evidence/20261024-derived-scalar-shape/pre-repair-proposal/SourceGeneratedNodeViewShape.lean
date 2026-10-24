import MicroCFTA.SourceDeriveNodeViewNames

/-!
# Ordered scalar shapes from node-view declarations

Inputs are observations of reification, name lookup and character tests.
The output records scalar shape only. This does not execute Template Haskell
or derive the Generic, NodeView, HasFTA or codec extraction laws.
-/
namespace MicroCFTA.SourceGeneratedNodeViewShape

/-- Constructor forms retain the source distinctions used by deriveNode. -/
inductive Constructor where
  | normalC (name : String) (fields : Nat)
  | recC (name : String) (fields : Nat)
  | infixC (name : String)
  | forallC
  | gadtC
  | recGadtC
  deriving DecidableEq, Repr

/-- Context entries are opaque because the source tests only whether they exist. -/
inductive Reified where
  | dataD (context : List Unit) (constructors : List Constructor)
  | newtypeD (context : List Unit) (constructor : Constructor)
  | other
  deriving DecidableEq, Repr

/-- Each unit field denotes one plain scalar child parameter. -/
structure ScalarShape where
  name : String
  fields : List Unit
  deriving DecidableEq, Repr

/-- The shape retains the generated type name and every ordered constructor. -/
structure ViewShape where
  name : String
  constructors : List ScalarShape
  deriving DecidableEq, Repr

/-- Unsupported forms retain the literal source diagnostic. -/
def unsupported (source feature : String) : String :=
  "deriveNode " ++ source ++ ": " ++ feature ++ " need a manual node view"

/-- A collision reports the exact generated name. -/
def collision (source generated : String) : String :=
  "deriveNode " ++ source ++ ": " ++ generated ++
    " is already in scope; hide or rename the existing name"

/-- Character classification is an explicit boundary to Data.Char.isUpper. -/
def upperName (upper : Char → Bool) (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: _ => upper first

/-- The caller supplies one namespace's observed lookup results. -/
def generatedName (source : String) (upper : Char → Bool)
    (inScope : String → Bool) (name : String) : Except String String :=
  if upperName upper name = true then
    if inScope (name ++ "Node") = true then .error (collision source (name ++ "Node"))
    else .ok (name ++ "Node")
  else .error (unsupported source "symbolic names")

/-- Name validity uses character and lookup inputs, not a desired generation result. -/
def ValidName (upper : Char → Bool) (inScope : String → Bool) (name : String) : Prop :=
  upperName upper name = true ∧ inScope (name ++ "Node") = false

private def namedScalar (source : String) (upper : Char → Bool)
    (valuesInScope : String → Bool) (name : String) (arity : Nat) : Except String ScalarShape := do
  let generated ← generatedName source upper valuesInScope name
  pure ⟨generated, List.replicate arity ()⟩

/-- Constructor classification precedes value-namespace lookup. -/
def generateConstructor (source : String) (upper : Char → Bool)
    (valuesInScope : String → Bool) : Constructor → Except String ScalarShape
  | .normalC name fields | .recC name fields => namedScalar source upper valuesInScope name fields
  | .infixC name => namedScalar source upper valuesInScope name 2
  | .forallC => .error (unsupported source "existential or constrained constructors")
  | .gadtC | .recGadtC => .error (unsupported source "GADT constructors")

/-- This condition checks source forms and names independently of the output. -/
def ValidConstructor (upper : Char → Bool) (valuesInScope : String → Bool) : Constructor → Prop
  | .normalC name _ | .recC name _ | .infixC name => ValidName upper valuesInScope name
  | _ => False

/-- Rejected forms have no admitted shape; their arbitrary projection is never returned. -/
def scalarShape : Constructor → ScalarShape
  | .normalC name fields | .recC name fields => ⟨name ++ "Node", List.replicate fields ()⟩
  | .infixC name => ⟨name ++ "Node", [(), ()]⟩
  | _ => ⟨"", []⟩

private def checkedDatatype (source : String) (upper : Char → Bool)
    (typesInScope valuesInScope : String → Bool) : List Unit → List Constructor → Except String ViewShape
  | [], constructors => do
      let name ← generatedName source upper typesInScope source
      let alternatives ← constructors.mapM (generateConstructor source upper valuesInScope)
      pure ⟨name, alternatives⟩
  | _ :: _, _ => .error (unsupported source "datatype contexts")

/-- Reification, context, type-name and ordered constructor checks occur in source order. -/
def derive (source : String) (upper : Char → Bool) (typesInScope valuesInScope : String → Bool)
    (reified : Except String Reified) : Except String ViewShape := do
  match ← reified with
  | .dataD context constructors => checkedDatatype source upper typesInScope valuesInScope context constructors
  | .newtypeD context constructor => checkedDatatype source upper typesInScope valuesInScope context [constructor]
  | .other => .error (unsupported source "type synonyms and data families")

private theorem bind_ok_iff (first : Except String α) (next : α → Except String β) (result : β) :
    first.bind next = .ok result ↔ ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Except.bind]

/-- A generated name is exactly the suffix name when both independent tests pass. -/
theorem generatedName_success (source : String) (upper : Char → Bool) (inScope : String → Bool)
    (name result : String) :
    generatedName source upper inScope name = .ok result ↔
      ValidName upper inScope name ∧ result = name ++ "Node" := by
  cases first : upperName upper name <;> cases present : inScope (name ++ "Node") <;>
    simp [generatedName, ValidName, first, present, eq_comm]

private theorem namedScalar_success (source : String) (upper : Char → Bool)
    (valuesInScope : String → Bool) (name : String) (arity : Nat) (result : ScalarShape) :
    namedScalar source upper valuesInScope name arity = .ok result ↔
      ValidName upper valuesInScope name ∧ result = ⟨name ++ "Node", List.replicate arity ()⟩ := by
  cases first : upperName upper name <;> cases present : valuesInScope (name ++ "Node") <;>
    simp [namedScalar, generatedName, ValidName, first, present, Except.bind, eq_comm]

/-- Success derives the exact field count, scalar fields and generated constructor name. -/
theorem constructor_success (source : String) (upper : Char → Bool) (valuesInScope : String → Bool)
    (constructor : Constructor) (result : ScalarShape) :
    generateConstructor source upper valuesInScope constructor = .ok result ↔
      ValidConstructor upper valuesInScope constructor ∧ result = scalarShape constructor := by
  cases constructor <;> simp [generateConstructor, ValidConstructor, scalarShape, namedScalar_success]

/-- Successful traversal preserves the complete original constructor order. -/
theorem constructors_success (source : String) (upper : Char → Bool) (valuesInScope : String → Bool)
    (constructors : List Constructor) (result : List ScalarShape) :
    constructors.mapM (generateConstructor source upper valuesInScope) = .ok result ↔
      (∀ constructor ∈ constructors, ValidConstructor upper valuesInScope constructor) ∧
      result = constructors.map scalarShape := by
  induction constructors generalizing result with
  | nil => simp
  | cons first rest ih =>
      rw [List.mapM_cons, bind_ok_iff]
      constructor
      · rintro ⟨head, headDone, continued⟩
        obtain ⟨tail, tailDone, final⟩ := (bind_ok_iff _ _ _).mp continued
        obtain ⟨headValid, rfl⟩ := (constructor_success source upper valuesInScope first head).mp headDone
        obtain ⟨tailValid, rfl⟩ := (ih tail).mp tailDone
        refine ⟨?_, (Except.ok.inj final).symm⟩
        intro constructor member
        rcases List.mem_cons.mp member with rfl | later
        · exact headValid
        · exact tailValid constructor later
      · rintro ⟨valid, rfl⟩
        refine ⟨scalarShape first,
          (constructor_success source upper valuesInScope first _).mpr ⟨valid first (by simp), rfl⟩, ?_⟩
        apply (bind_ok_iff _ _ _).mpr
        exact ⟨rest.map scalarShape, (ih _).mpr ⟨fun constructor member =>
          valid constructor (List.mem_cons_of_mem first member), rfl⟩, rfl⟩

/-- Accepted data declarations give exactly the ordered scalar shape. -/
theorem derive_data_success (source : String) (upper : Char → Bool)
    (typesInScope valuesInScope : String → Bool) (constructors : List Constructor) (result : ViewShape) :
    derive source upper typesInScope valuesInScope (.ok (.dataD [] constructors)) = .ok result ↔
      ValidName upper typesInScope source ∧
      (∀ constructor ∈ constructors, ValidConstructor upper valuesInScope constructor) ∧
      result = ⟨source ++ "Node", constructors.map scalarShape⟩ := by
  change (generatedName source upper typesInScope source >>= fun name =>
    constructors.mapM (generateConstructor source upper valuesInScope) >>= fun alternatives =>
      pure (ViewShape.mk name alternatives)) = .ok result ↔ _
  rw [bind_ok_iff]
  constructor
  · rintro ⟨name, nameDone, continued⟩
    obtain ⟨nameValid, rfl⟩ := (generatedName_success source upper typesInScope source name).mp nameDone
    obtain ⟨alternatives, alternativesDone, final⟩ := (bind_ok_iff _ _ _).mp continued
    obtain ⟨valid, rfl⟩ := (constructors_success source upper valuesInScope constructors alternatives).mp alternativesDone
    exact ⟨nameValid, valid, (Except.ok.inj final).symm⟩
  · rintro ⟨nameValid, valid, rfl⟩
    refine ⟨source ++ "Node", (generatedName_success source upper typesInScope source _).mpr ⟨nameValid, rfl⟩, ?_⟩
    exact (bind_ok_iff _ _ _).mpr ⟨constructors.map scalarShape,
      (constructors_success source upper valuesInScope constructors _).mpr ⟨valid, rfl⟩, rfl⟩

/-- A source newtype uses the same checks with its singleton constructor list. -/
theorem derive_newtype (source : String) (upper : Char → Bool) (typesInScope valuesInScope : String → Bool)
    (context : List Unit) (constructor : Constructor) :
    derive source upper typesInScope valuesInScope (.ok (.newtypeD context constructor)) =
      derive source upper typesInScope valuesInScope (.ok (.dataD context [constructor])) := rfl

/-- A native reification failure precedes every modeled validation step. -/
theorem reify_error (source : String) (upper : Char → Bool) (typesInScope valuesInScope : String → Bool)
    (error : String) : derive source upper typesInScope valuesInScope (.error error) = .error error := rfl

/-- An unsupported reified declaration is rejected before name lookup. -/
theorem declaration_error (source : String) (upper : Char → Bool) (typesInScope valuesInScope : String → Bool) :
    derive source upper typesInScope valuesInScope (.ok .other) =
      .error (unsupported source "type synonyms and data families") := rfl

/-- A datatype context precedes type-name and constructor-name errors. -/
theorem context_error (source : String) (upper : Char → Bool) (typesInScope valuesInScope : String → Bool)
    (first : Unit) (rest : List Unit) (constructors : List Constructor) :
    derive source upper typesInScope valuesInScope (.ok (.dataD (first :: rest) constructors)) =
      .error (unsupported source "datatype contexts") := rfl

/-- A type-namespace collision precedes every constructor validation. -/
theorem type_collision (source : String) (upper : Char → Bool) (typesInScope valuesInScope : String → Bool)
    (constructors : List Constructor) (first : upperName upper source = true)
    (present : typesInScope (source ++ "Node") = true) :
    derive source upper typesInScope valuesInScope (.ok (.dataD [] constructors)) =
      .error (collision source (source ++ "Node")) := by
  simp [derive, checkedDatatype, generatedName, first, present, Except.bind]

/-- Every generated suffix name satisfies the existing positional name contract. -/
theorem generated_names_pass (names : List String) :
    SourceDeriveNodeViewNames.checkNames (names.map fun name => (name, name ++ "Node")) = .ok () := by
  apply (SourceDeriveNodeViewNames.checkNames_exact _).mpr
  intro pair member
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  exact ⟨"Node".toList, String.toList_append.symm⟩

end MicroCFTA.SourceGeneratedNodeViewShape
