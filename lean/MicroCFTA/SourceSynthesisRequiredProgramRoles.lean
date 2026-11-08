import MicroCFTA.SourceSynthesisProgramBuildRolesGeneric
import MicroCFTA.SourceCurrentRequiredJointRowOrigins

/-!
# Program roles after actual annotation requirements

A requirement at child zero can change the Type annotation. Every other
child retains its value. One original row supplies these children and the
complete returned guard. The result includes Top rows and root unions.
These laws concern completed Required call graphs on an available heap.
They do not establish all reached Program roles in the complete driver.
-/
namespace MicroCFTA.SourceSynthesisRequiredProgramRoles
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue ProgramEdge)
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityRequiredCache (Ordinary)
open SourceCurrentRequiredGuardOrigins (RowOrigin)
open SourceCurrentLiteralRootParts (Row)
open InternedUnionHeadGuard (HeadSafe)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol : Type} {literal : String → Symbol}

/-- A Program value has no Mu or reference at a root union position. -/
theorem program_headSafe {value : Value Symbol Guard} (role : ProgramValue literal value) : HeadSafe value := by
  induction role using ProgramValue.rec (motive_2 := fun _ _ => True) with
  | empty => exact .empty
  | node entry rows depth free _ _ => exact .node entry rows depth free
  | union entry members depth free _ ih => exact .union entry members depth free ih
  | annotated => trivial
  | application => trivial
  | filter => trivial

/-- Every literal root row retains the complete Program certificate. -/
theorem literal_roles {value : Value Symbol Guard} {edge : EdgeValue Symbol Guard}
    (role : ProgramValue literal value) (origin : Row value edge) : ProgramEdge literal edge := by
  revert role
  induction origin with
  | node member =>
      intro role
      cases role with
      | node _ _ _ _ checked => exact checked _ member
  | union member _ ih =>
      intro role
      cases role with
      | union _ _ _ _ checked => exact ih (checked _ member)

private theorem tail_lookup {α : Type} (values : List α) (index : Nat) :
    values.tail[index]? = values[index + 1]? := by
  cases values <;> rfl

/-- A changed annotation preserves the other child roles, full guard, and row layout. -/
theorem rebuild_roles {original result : EdgeValue Symbol Guard} (role : ProgramEdge literal original)
    (origin : RowOrigin original result)
    (unchanged : ∀ index : Nat, index ≠ 0 → result.children[index]? = original.children[index]?) :
    ProgramEdge literal result := by
  have tails : result.children.tail = original.children.tail := by
    apply List.ext_getElem?
    intro index
    rw [tail_lookup, tail_lookup]
    exact unchanged (index + 1) (by omega)
  cases role with
  | annotated _ annotation guard children =>
      have count : result.children.length = 1 := by rw [origin.2.2, children]; rfl
      obtain ⟨annotation, output⟩ := List.length_eq_one_iff.mp count
      exact .annotated result annotation (origin.1.trans guard) output
  | application _ types marker function argument symbol guard children functionRole argumentRole =>
      have count : result.children.length = 4 := by rw [origin.2.2, children]; rfl
      cases output : result.children with
      | nil => simp only [output, List.length_nil] at count; omega
      | cons annotation rest =>
          have tail : rest = [marker, function, argument] := by simpa only [output, children, List.tail_cons] using tails
          exact .application result annotation marker function argument (origin.2.1.trans symbol)
            (origin.1.trans guard) (by rw [output, tail]) functionRole argumentRole
  | filter _ goal candidates symbol guard children candidateRole =>
      have count : result.children.length = 2 := by rw [origin.2.2, children]; rfl
      cases output : result.children with
      | nil => simp only [output, List.length_nil] at count; omega
      | cons annotation rest =>
          have tail : rest = [candidates] := by simpa only [output, children, List.tail_cons] using tails
          exact .filter result annotation candidates (origin.2.1.trans symbol)
            (origin.1.trans guard) (by rw [output, tail]) candidateRole

private theorem ordinary_roles {value : Value Symbol Guard} (ordinary : Ordinary value)
    (rows : ∀ edge ∈ nodeEdges value, ProgramEdge literal edge) : ProgramValue literal value := by
  cases value with
  | empty => exact .empty
  | node entry edges depth free => exact .node entry edges depth free rows
  | reference | union | mu => cases ordinary

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Completed physical head exposure preserves Program rows, including root unions. -/
theorem head_roles {input output : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head input before output after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (role : ProgramValue literal input) : ProgramValue literal output := by
  have origins := SourceCurrentRequiredJointRowOrigins.head_literal_rows actual semantic costs available (program_headSafe role)
  exact ordinary_roles origins.1 (fun edge member => literal_roles role (origins.2 edge member))

private theorem ordinary_required {entries : List (Int × Needed)} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : RequireNode (.node entries) input before output after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (ordinary : Ordinary input) : Ordinary output := by
  cases input with
  | empty =>
      cases actual with
      | identity => trivial
      | empty _ => trivial
      | recursive _ recursive => cases recursive
  | node entry edges depth free =>
      cases actual with
      | identity => trivial
      | ordinary _ rows built =>
          have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
          have effects := SourceCurrentRequiredHeapEffects.rows (fun _ => True) rows semantic costs
            (fun _ _ _ => trivial) resident
          have normal := SourceEqualityRequiredCache.node_ordinary _ _
            effects.2.1.ready.semantic.1.normal.facts effects.2.2.2.2
          simpa only [built] using normal
      | recursive _ recursive => cases recursive
  | reference | union | mu => cases ordinary

/-- Actual Required calls at the annotation preserve every Program field. -/
theorem required_roles {entries : List (Int × Needed)} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : RequireNode (.node entries) input before output after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (role : ProgramValue literal input)
    (annotationOnly : ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) entries = none) :
    ProgramValue literal output := by
  have safe := program_headSafe role
  have origins := SourceCurrentRequiredJointRowOrigins.required_literal_rows actual semantic costs available safe
  have restored : ∀ edge ∈ nodeEdges output, ProgramEdge literal edge := by
    intro edge member
    obtain ⟨original, found, origin, unchanged⟩ := origins edge member
    exact rebuild_roles (literal_roles role found) origin (fun index nonzero => unchanged index (annotationOnly index nonzero))
  cases actual with
  | identity => exact role
  | empty _ => exact .empty
  | ordinary nonempty rows built =>
      exact ordinary_roles (ordinary_required (.ordinary nonempty rows built) semantic costs available trivial) restored
  | recursive _ _ head body =>
      have exposed := SourceCurrentRequiredJointRowOrigins.head_literal_rows head semantic costs available safe
      have effects := SourceCurrentRequiredHeapEffects.head (fun _ => True) head semantic costs
        (fun _ _ _ => trivial) available
      exact ordinary_roles (ordinary_required body effects.2.1 effects.2.2.1 effects.2.2.2.2 exposed.1) restored

end MicroCFTA.SourceSynthesisRequiredProgramRoles
