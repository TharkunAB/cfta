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
  /-- An ordinary positional constructor retains its arity. -/
  | normalC (name : String) (fields : Nat)
  /-- A record constructor retains its field count. -/
  | recC (name : String) (fields : Nat)
  /-- A named infix constructor has two fields. -/
  | infixC (name : String)
  /-- Quantified or constrained constructors are rejected. -/
  | forallC
  /-- A positional GADT constructor is rejected. -/
  | gadtC
  /-- A record GADT constructor is rejected. -/
  | recGadtC
  deriving DecidableEq, Repr

/-- Context entries are opaque because the source tests only whether they exist. -/
inductive Reified where
  /-- An ordinary datatype retains context and constructor order. -/
  | dataD (context : List Unit) (constructors : List Constructor)
  /-- A newtype retains context and its one constructor. -/
  | newtypeD (context : List Unit) (constructor : Constructor)
  /-- Other reified forms need a manual view. -/
  | other
  deriving DecidableEq, Repr

/-- Each unit field denotes one plain scalar child parameter. -/
structure ScalarShape where
  /-- The constructor base name has the Node suffix. -/
  name : String
  /-- Each unit is one plain scalar field. -/
  fields : List Unit
  deriving DecidableEq, Repr

/-- The shape retains the generated type name and every ordered constructor. -/
structure ViewShape where
  /-- The generated type base name has the Node suffix. -/
  name : String
  /-- Generated constructors retain source order. -/
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

/-- A trailing hash cannot precede the appended Node suffix in a declaration name. -/
def endsInHash (name : String) : Bool := name.toList.getLast? == some '#'

/-- The caller supplies one namespace's observed lookup results. -/
def generatedName (source : String) (upper : Char → Bool)
    (inScope : String → Bool) (name : String) : Except String String :=
  if upperName upper name = true then
    if endsInHash name = true then .error (unsupported source "names ending in #")
    else if inScope (name ++ "Node") = true then .error (collision source (name ++ "Node"))
    else .ok (name ++ "Node")
  else .error (unsupported source "symbolic names")

/-- Name validity uses character and lookup inputs, not a desired generation result. -/
def ValidName (upper : Char → Bool) (inScope : String → Bool) (name : String) : Prop :=
  upperName upper name = true ∧ endsInHash name = false ∧ inScope (name ++ "Node") = false

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

/-- A generated name is exactly the suffix name when all independent tests pass. -/
theorem generatedName_success (source : String) (upper : Char → Bool) (inScope : String → Bool)
    (name result : String) :
    generatedName source upper inScope name = .ok result ↔
      ValidName upper inScope name ∧ result = name ++ "Node" := by
  cases first : upperName upper name <;> cases suffix : endsInHash name <;>
    cases present : inScope (name ++ "Node") <;>
      simp [generatedName, ValidName, first, suffix, present]
  all_goals exact eq_comm

private theorem namedScalar_success (source : String) (upper : Char → Bool)
    (valuesInScope : String → Bool) (name : String) (arity : Nat) (result : ScalarShape) :
    namedScalar source upper valuesInScope name arity = .ok result ↔
      ValidName upper valuesInScope name ∧ result = ⟨name ++ "Node", List.replicate arity ()⟩ := by
  change (generatedName source upper valuesInScope name).bind
    (fun generated => .ok ⟨generated, List.replicate arity ()⟩) = .ok result ↔ _
  rw [bind_ok_iff]
  constructor
  · rintro ⟨generated, done, final⟩
    obtain ⟨valid, rfl⟩ := (generatedName_success source upper valuesInScope name generated).mp done
    exact ⟨valid, (Except.ok.inj final).symm⟩
  · rintro ⟨valid, rfl⟩
    exact ⟨name ++ "Node", (generatedName_success source upper valuesInScope name _).mpr ⟨valid, rfl⟩, rfl⟩

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
  | nil =>
      change (.ok [] : Except String (List ScalarShape)) = .ok result ↔ _
      simp [eq_comm]
  | cons first rest ih =>
      rw [List.mapM_cons]
      change (generateConstructor source upper valuesInScope first).bind
        (fun head => (rest.mapM (generateConstructor source upper valuesInScope)).bind
          (fun tail => .ok (head :: tail))) = .ok result ↔ _
      rw [bind_ok_iff]
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

/-- Earlier valid constructors precede the first rejected occurrence. -/
theorem constructors_first_error (source : String) (upper : Char → Bool)
    (valuesInScope : String → Bool) (earlier later : List Constructor) (bad : Constructor)
    (error : String) (valid : ∀ constructor ∈ earlier, ValidConstructor upper valuesInScope constructor)
    (failed : generateConstructor source upper valuesInScope bad = .error error) :
    (earlier ++ bad :: later).mapM (generateConstructor source upper valuesInScope) = .error error := by
  induction earlier with
  | nil =>
      rw [List.nil_append, List.mapM_cons]
      change (generateConstructor source upper valuesInScope bad).bind _ = .error error
      rw [failed]
      rfl
  | cons first rest ih =>
      have firstDone := (constructor_success source upper valuesInScope first (scalarShape first)).mpr
        ⟨valid first (by simp), rfl⟩
      have restValid : ∀ constructor ∈ rest, ValidConstructor upper valuesInScope constructor :=
        fun constructor member => valid constructor (List.mem_cons_of_mem first member)
      rw [List.cons_append, List.mapM_cons]
      change (generateConstructor source upper valuesInScope first).bind
        (fun head => ((rest ++ bad :: later).mapM (generateConstructor source upper valuesInScope)).bind
          (fun tail => .ok (head :: tail))) = .error error
      rw [firstDone]
      change ((rest ++ bad :: later).mapM (generateConstructor source upper valuesInScope)).bind _ = .error error
      rw [ih restValid]
      rfl

/-- Accepted data declarations give exactly the ordered scalar shape. -/
theorem derive_data_success (source : String) (upper : Char → Bool)
    (typesInScope valuesInScope : String → Bool) (constructors : List Constructor) (result : ViewShape) :
    derive source upper typesInScope valuesInScope (.ok (.dataD [] constructors)) = .ok result ↔
      ValidName upper typesInScope source ∧
      (∀ constructor ∈ constructors, ValidConstructor upper valuesInScope constructor) ∧
      result = ⟨source ++ "Node", constructors.map scalarShape⟩ := by
  change (generatedName source upper typesInScope source).bind (fun name =>
    (constructors.mapM (generateConstructor source upper valuesInScope)).bind (fun alternatives =>
      .ok (ViewShape.mk name alternatives))) = .ok result ↔ _
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
    (plain : endsInHash source = false) (present : typesInScope (source ++ "Node") = true) :
    derive source upper typesInScope valuesInScope (.ok (.dataD [] constructors)) =
      .error (collision source (source ++ "Node")) := by
  change (generatedName source upper typesInScope source).bind _ = .error _
  have failed : generatedName source upper typesInScope source = .error (collision source (source ++ "Node")) := by
    simp [generatedName, first, plain, present]
  rw [failed]
  rfl

/-- A trailing-hash rejection precedes either namespace collision check. -/
theorem generatedName_hash (source : String) (upper : Char → Bool) (inScope : String → Bool)
    (name : String) (first : upperName upper name = true) (suffix : endsInHash name = true) :
    generatedName source upper inScope name = .error (unsupported source "names ending in #") := by
  simp [generatedName, first, suffix]

/-- A rejected type suffix precedes every constructor check. -/
theorem type_hash_error (source : String) (upper : Char → Bool)
    (typesInScope valuesInScope : String → Bool) (constructors : List Constructor)
    (first : upperName upper source = true) (suffix : endsInHash source = true) :
    derive source upper typesInScope valuesInScope (.ok (.dataD [] constructors)) =
      .error (unsupported source "names ending in #") := by
  change (generatedName source upper typesInScope source).bind _ = .error _
  rw [generatedName_hash source upper typesInScope source first suffix]
  rfl

/-- Every generated suffix name satisfies the existing positional name contract. -/
theorem generated_names_pass (names : List String) :
    SourceDeriveNodeViewNames.checkNames (names.map fun name => (name, name ++ "Node")) = .ok () := by
  apply (SourceDeriveNodeViewNames.checkNames_exact _).mpr
  intro pair member
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  exact ⟨"Node".toList, String.toList_append.symm⟩

end MicroCFTA.SourceGeneratedNodeViewShape
