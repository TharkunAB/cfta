import MicroCFTA.SourceCurrentConstrainedCap
import MicroCFTA.SourceEqualityProjectionGraph
import MicroCFTA.SourceEqualityClassTarget

/-!
# Initial signed path masks above hereditary recursive values

The mask inspects the supplied finite syntax. A hereditary value accepts any
remaining path. An ordinary step checks every selected row child. Stored
union alternatives keep the same path. An empty path requires hereditary
annotations at its endpoint. Missing signed positions impose no condition.

This mask does not assert that a path call completes. A bare reference can
carry annotations, but a nonempty successful projection cannot start there.
Actual recursive head and edit preservation remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapPaths
open InternedConstructorTemplates SourceEqualityAnnotationLanguage
open SourceEqualityProjectionGraph
open SourceCurrentConstrainedCap (Cap)
variable {Symbol Guard : Type}

/-- Each initial path reaches only hereditary endpoints or hereditary recursive boundaries. -/
inductive Supported (valid : Guard → Prop) : List Int → Value Symbol Guard → Prop where
  /-- Hereditary guards permit every remaining path inside this value. -/
  | plain (path : List Int) (annotated : Annotated valid value) : Supported valid path value
  /-- Each existing signed row child retains the remaining initial path. -/
  | node (index : Int) (path : List Int) (entry) (edges : List (EdgeValue Symbol Guard)) (depth free)
      (children : ∀ edge ∈ edges, ∀ child, select edge.children index = some child → Supported valid path child) :
      Supported valid (index :: path) (.node entry edges depth free)
  /-- A stored union retains every alternative at the same initial path. -/
  | union (path : List Int) (entry) (members : List (Value Symbol Guard)) (depth free)
      (children : ∀ child ∈ members, Supported valid path child) : Supported valid path (.union entry members depth free)

/-- An initial empty path requires the existing full hereditary predicate. -/
theorem Supported.root {valid : Guard → Prop} {value : Value Symbol Guard}
    (supported : Supported valid [] value) : Annotated valid value := by
  generalize empty : ([] : List Int) = path at supported
  induction supported with
  | plain path annotated => exact annotated
  | node => cases empty
  | union path entry members depth free children ih =>
      exact .union entry members depth free (fun child member => ih child member empty)

/-- The root mask is exactly hereditary annotation, with no completion premise. -/
theorem root_iff (valid : Guard → Prop) (value : Value Symbol Guard) :
    Supported valid [] value ↔ Annotated valid value := ⟨Supported.root, Supported.plain []⟩

/-- Each selected ordinary child inherits the literal signed tail mask. -/
theorem Supported.node_selected {valid : Guard → Prop} {index : Int} {path : List Int}
    {entry edges depth free} (supported : Supported valid (index :: path) (.node entry edges depth free))
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (child : Value Symbol Guard)
    (found : select edge.children index = some child) : Supported valid path child := by
  cases supported with
  | plain path annotated =>
      exact .plain _ ((SourceCurrentHereditaryConstructors.node_edge annotated edge member).2 child (select_member found))
  | node index path entry edges depth free children => exact children edge member child found

/-- Stored union alternatives inherit the same initial mask without a head call. -/
theorem Supported.union_member {valid : Guard → Prop} {path : List Int} {entry members depth free}
    (supported : Supported valid path (.union entry members depth free : Value Symbol Guard))
    (child : Value Symbol Guard) (member : child ∈ members) : Supported valid path child := by
  cases supported with
  | plain path annotated =>
      exact .plain _ (SourceCurrentHereditaryUnconstrained.union_member annotated child member)
  | union path entry members depth free children => exact children child member

/-- A Mu boundary has no finite-cap shortcut to a nonhereditary stored body. -/
theorem binder_iff (valid : Guard → Prop) (path : List Int) (entry) (body depth ordinary : Value Symbol Guard) :
    Supported valid path (.mu entry body depth ordinary) ↔ Annotated valid (.mu entry body depth ordinary) := by
  constructor
  · intro supported
    cases supported with
    | plain path annotated => exact annotated
  · exact Supported.plain path

/-- A reference annotation does not assert that a nonempty physical path can read it. -/
theorem reference (valid : Guard → Prop) (path : List Int) (name) :
    Supported valid path (.reference name : Value Symbol Guard) := .plain path (.reference name)

/-- Weakening the guard predicate preserves the initial positional mask. -/
theorem Supported.mono {first second : Guard → Prop} {path : List Int} {value : Value Symbol Guard}
    (supported : Supported first path value) (implies : ∀ guard, first guard → second guard) : Supported second path value := by
  induction supported with
  | plain path annotated => exact .plain path (SourceCurrentHereditaryUnconstrained.annotated_mono implies annotated)
  | node index path entry edges depth free children ih => exact .node index path entry edges depth free ih
  | union path entry members depth free children ih => exact .union path entry members depth free ih

/-- Extending a safe initial path keeps its endpoint inside a hereditary boundary. -/
theorem Supported.append {valid : Guard → Prop} {path : List Int} {value : Value Symbol Guard}
    (supported : Supported valid path value) (suffix : List Int) : Supported valid (path ++ suffix) value := by
  induction supported with
  | plain path annotated => exact .plain _ annotated
  | node index path entry edges depth free children ih => exact .node index (path ++ suffix) entry edges depth free ih
  | union path entry members depth free children ih => exact .union _ entry members depth free ih

/-- Enough actual child steps cross every finite nonhereditary ordinary layer. -/
theorem of_cap {valid : Guard → Prop} {depth : Nat} {value : Value Symbol Guard}
    (bounded : Cap valid depth value) (path : List Int) (long : depth ≤ path.length) : Supported valid path value := by
  induction bounded generalizing path with
  | plain depth annotated => exact .plain path annotated
  | node depth entry edges level free children ih =>
      cases path with
      | nil => simp only [List.length_nil] at long; omega
      | cons index path =>
          apply Supported.node index path entry edges level free
          intro edge member child found
          exact ih child (List.mem_flatMap.mpr ⟨edge, member, select_member found⟩) path (by simpa only [List.length_cons] using long)
  | union depth entry members level free children ih =>
      exact .union path entry members level free (fun child member => ih child member path long)

/-- A forest root checks every original value; a signed position checks only its actual child. -/
def ForestSupported (valid : Guard → Prop) (path : List Int) (values : List (Value Symbol Guard)) : Prop :=
  match path with
  | [] => ∀ value ∈ values, Annotated valid value
  | index :: path => ∀ value, select values index = some value → Supported valid path value

/-- A hereditary captured forest supports every signed path, including its union root. -/
theorem forest_plain (valid : Guard → Prop) (values : List (Value Symbol Guard))
    (annotated : ∀ value ∈ values, Annotated valid value) (path : List Int) : ForestSupported valid path values := by
  cases path with
  | nil => exact annotated
  | cons index path => exact fun value found => .plain path (annotated value (select_member found))

/-- A selected forest slot retains its literal tail mask. -/
theorem ForestSupported.selected {valid : Guard → Prop} {index : Int} {path : List Int}
    {values : List (Value Symbol Guard)} (supported : ForestSupported valid (index :: path) values)
    {value : Value Symbol Guard} (found : select values index = some value) : Supported valid path value := supported value found

/-- The forest index consumes one path element before the finite cap begins. -/
theorem forest_of_cap (valid : Guard → Prop) (depth : Nat) (values : List (Value Symbol Guard))
    (bounded : ∀ value ∈ values, Cap valid depth value) (index : Int) (path : List Int)
    (long : depth ≤ path.length) : ForestSupported valid (index :: path) values :=
  fun value found => of_cap (bounded value (select_member found)) path long

/-- Missing signed forest positions require no endpoint annotation. -/
theorem forest_missing (valid : Guard → Prop) (values : List (Value Symbol Guard)) (index : Int) (path : List Int)
    (missing : select values index = none) : ForestSupported valid (index :: path) values := by
  intro value found
  simp only [missing] at found

/-- Suffix extension also preserves the distinct forest-root contract. -/
theorem ForestSupported.append {valid : Guard → Prop} {path : List Int} {values : List (Value Symbol Guard)}
    (supported : ForestSupported valid path values) (suffix : List Int) : ForestSupported valid (path ++ suffix) values := by
  cases path with
  | nil => exact forest_plain valid values supported suffix
  | cons index path => exact fun value found => (supported value found).append suffix

/-- Every literal other-path operand inherits the supplied original-class mask. -/
theorem operand_paths (valid : Guard → Prop) (paths : EqualityNormalize.Class) (selected : EqualityNormalize.Path)
    (values : List (Value Symbol Guard))
    (supported : ∀ path ∈ paths, ForestSupported valid (path.map Int.ofNat) values) :
    ∀ path ∈ SourceEqualityClassTarget.operandPaths paths selected, ForestSupported valid path values := by
  intro path member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact supported original (List.mem_filter.mp present).1

/-- A nonempty bare-reference projection has no successful physical graph. -/
theorem no_reference_project [DecidableEq (EdgeKey Symbol Guard)] (index : Int) (path : List Int) (name)
    (before after : State Symbol Guard) (result : Value Symbol Guard) :
    ¬ Project (index :: path) (.reference name) before result after := by
  intro trace
  cases trace with
  | recursive recursive => cases recursive

/-- Actual zero-tail row projections return annotated selected endpoints in their original order. -/
theorem project_rows_root [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {index : Int} {edges : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    {results : List (Value Symbol Guard)} (actual : ProjectRows [] index edges before results after)
    (supported : ∀ edge ∈ edges, ∀ child, select edge.children index = some child → Supported valid [] child) :
    ∀ result ∈ results, Annotated valid result := by
  generalize empty : ([] : List Int) = path at actual
  induction actual with
  | nil => intro result member; cases member
  | missing absent rest ih =>
      exact ih empty (fun edge member => supported edge (List.mem_cons_of_mem _ member))
  | selected found first rest ih =>
      cases empty
      cases first
      intro result member
      rcases List.mem_cons.mp member with rfl | member
      · exact (supported _ List.mem_cons_self _ found).root
      · exact ih rfl (fun edge member => supported edge (List.mem_cons_of_mem _ member)) result member

/-- A nonhereditary own row prevents an empty endpoint mask even under a finite cap. -/
theorem root_guard_obstruction (valid : Guard → Prop) (entry) (edges : List (EdgeValue Symbol Guard)) (depth free)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (invalid : ¬ valid edge.entry.key.constraint) :
    ¬ Supported valid [] (.node entry edges depth free) := by
  intro supported
  exact invalid (SourceCurrentHereditaryConstructors.node_edge supported.root edge member).1

end MicroCFTA.SourceCurrentConstrainedCapPaths
