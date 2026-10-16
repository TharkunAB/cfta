import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardProfiles
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
import MicroCFTA.InternedOrdinaryAbsenceReplay

/-!
# Hereditary guard bounds through actual constructors

Edge construction retains the complete requested constraint and children.
Node construction selects supplied rows after filtering and canonicalization.
Coherent cache hits retain those same complete records.
These facts bound every nested guard. They do not bound allocation requests.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardConstructors
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedRecordCoherence InternedFreshProbeKeys
open SourceCurrentAllocatedFiniteOrdinaryGuardProfiles
local notation "Guard" => SourceSymbolicIndex.Constraint
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
variable {Symbol Formula : Type} {limit : Limits}

/-- Selecting original rows retains every nested raw constraint bound. -/
theorem rows_subset (edges selected : List (EdgeValue Symbol (Guard Formula)))
    (profile : Rows limit edges) (included : ∀ edge ∈ selected, edge ∈ edges) : Rows limit selected :=
  rows_of_members limit selected (fun edge member => Rows.member edges profile edge (included edge member))

/-- Filtering rows retains each selected hereditary guard bound. -/
theorem rows_filter (test : EdgeValue Symbol (Guard Formula) → Bool)
    (edges : List (EdgeValue Symbol (Guard Formula))) (profile : Rows limit edges) :
    Rows limit (edges.filter test) :=
  rows_subset edges _ profile (fun _ member => (List.mem_filter.mp member).1)

/-- Canonical row selection retains the complete original constraints. -/
theorem rows_canonical (edges : List (EdgeValue Symbol (Guard Formula))) (profile : Rows limit edges) :
    Rows limit (canonicalEdges edges) :=
  rows_subset edges _ profile (fun edge member => canonicalEdges_member edges edge member)

/-- Empty-child removal and canonical selection retain every nested bound. -/
theorem normalized_rows (edges : List (EdgeValue Symbol (Guard Formula))) (profile : Rows limit edges) :
    Rows limit (canonicalEdges (surviving edges)) :=
  rows_canonical _ (rows_filter _ edges profile)

/-- Each actual returned child occurrence supplies its hereditary guard bound. -/
theorem children_of_all₂ {Input : Type} {inputs : List Input}
    {values : List (Value Symbol (Guard Formula))}
    (profiles : Language.All₂ (fun _ value => Node limit value) inputs values) :
    Children limit values := by
  induction profiles with
  | nil => trivial
  | cons first rest ih => exact ⟨first, ih⟩

/-- Each actual returned row occurrence supplies its hereditary guard bound. -/
theorem rows_of_all₂ {Input : Type} {inputs : List Input}
    {edges : List (EdgeValue Symbol (Guard Formula))}
    (profiles : Language.All₂ (fun _ edge => Edge limit edge) inputs edges) : Rows limit edges := by
  induction profiles with
  | nil => trivial
  | cons first rest ih => exact ⟨first, ih⟩

/-- Literal edge construction retains its requested constraint and complete child bounds. -/
theorem makeEdge [DecidableEq (EdgeKey Symbol (Guard Formula))]
    (symbol : Symbol) (guard : Guard Formula) (values : List (Value Symbol (Guard Formula)))
    (state : State Symbol (Guard Formula)) (coherent : Coherent state) (cached : Cached state)
    (available : ∀ value ∈ values, Available state value)
    (bounded : SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds limit guard)
    (profile : Children limit values) :
    Edge limit (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 := by
  cases result : (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 with
  | mk entry children =>
      have key := InternedOrdinaryAbsenceReplay.makeEdge_key symbol guard values state coherent
      have exactChildren := InternedShallowValues.makeEdge_children symbol guard values state coherent cached available
      rw [result] at key exactChildren
      change entry.key = _ at key
      change children = values at exactChildren
      change SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Bounds limit entry.key.constraint ∧ Children limit children
      rw [key, exactChildren]
      exact ⟨bounded, profile⟩

/-- Literal normalized node construction retains bounds from its resident source rows. -/
theorem makeNode [DecidableEq (EdgeKey Symbol (Guard Formula))]
    (edges : List (EdgeValue Symbol (Guard Formula))) (state : State Symbol (Guard Formula))
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) (profile : Rows limit edges) :
    Node limit (run (InternedConstructorTemplates.makeNode edges) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have bounded := normalized_rows edges profile
  unfold InternedConstructorTemplates.makeNode
  dsimp only
  split
  · trivial
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa only [same] using selected)
    simp only [run, exactResult, identifyNode, Node]
    simpa only [same] using bounded

/-- Concatenating the rows of a bounded forest retains every raw constraint bound. -/
theorem flattened_rows (values : List (Value Symbol (Guard Formula))) (profile : Children limit values) :
    Rows limit (values.flatMap nodeEdges) := by
  apply rows_of_members limit
  intro edge member
  obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
  exact Rows.member _ (Node.nodeEdges value (Children.member values profile value present)) edge included

/-- Literal ordinary union retains the bounds of all resident source operands. -/
theorem ordinaryUnion [DecidableEq (EdgeKey Symbol (Guard Formula))]
    (values : List (Value Symbol (Guard Formula))) (state : State Symbol (Guard Formula))
    (coherent : Coherent state) (linked : Linked state)
    (available : ∀ value ∈ values, Available state value) (profile : Children limit values) :
    Node limit (run (MergedOrdinaryHeight.ordinaryUnion values) state).1 := by
  apply makeNode _ state coherent linked _ (flattened_rows values profile)
  intro edge member
  obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
  exact resident_edges state linked value (available value present).resident edge included

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardConstructors
