import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeProfile

/-!
# Ordinary output profiles through actual constructors

Raw edge construction retains the requested resident children.
Node construction filters and canonicalizes the requested resident rows.
Coherent cache hits retain the same complete records.
Guards and cached metadata have no added restriction.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedRecordCoherence InternedFreshProbeKeys
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
variable {Symbol Guard : Type} {rowLimit arityLimit : Nat}

/-- Pointwise child profiles construct the complete ordered forest profile. -/
theorem children_of_members (values : List (Value Symbol Guard))
    (profile : ∀ value ∈ values, NodeShape rowLimit arityLimit value) :
    ChildrenShape rowLimit arityLimit values := by
  induction values with
  | nil => trivial
  | cons value rest ih =>
      exact ⟨profile value List.mem_cons_self,
        ih (fun child member => profile child (List.mem_cons_of_mem _ member))⟩

/-- Pointwise edge profiles construct the complete ordered row profile. -/
theorem rows_of_members (edges : List (EdgeValue Symbol Guard))
    (profile : ∀ edge ∈ edges, EdgeShape rowLimit arityLimit edge) :
    RowsShape rowLimit arityLimit edges := by
  induction edges with
  | nil => trivial
  | cons edge rest ih =>
      exact ⟨profile edge List.mem_cons_self,
        ih (fun row member => profile row (List.mem_cons_of_mem _ member))⟩

/-- Selecting original rows retains each complete child profile. -/
theorem rows_subset (edges selected : List (EdgeValue Symbol Guard))
    (profile : RowsShape rowLimit arityLimit edges)
    (included : ∀ edge ∈ selected, edge ∈ edges) : RowsShape rowLimit arityLimit selected :=
  rows_of_members selected (fun edge member => RowsShape.member edges profile edge (included edge member))

/-- Filtering rows retains every selected edge profile. -/
theorem rows_filter (test : EdgeValue Symbol Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (profile : RowsShape rowLimit arityLimit edges) : RowsShape rowLimit arityLimit (edges.filter test) :=
  rows_subset edges _ profile (fun _ member => (List.mem_filter.mp member).1)

/-- Canonical row selection retains each complete supplied edge profile. -/
theorem rows_canonical (edges : List (EdgeValue Symbol Guard))
    (profile : RowsShape rowLimit arityLimit edges) : RowsShape rowLimit arityLimit (canonicalEdges edges) :=
  rows_subset edges _ profile (fun edge member => canonicalEdges_member edges edge member)

/-- Sorting and deduplicating actual edge identities cannot increase the row count. -/
theorem canonical_length_le (edges : List (EdgeValue Symbol Guard)) :
    (canonicalEdges edges).length ≤ edges.length := by
  have bounded := (EnumerationBuilderCaches.canonicalIds_nodup (edges.map (fun edge => edge.entry.identity))).length_le_of_subset
    (fun identity member => (EnumerationBuilderCaches.canonicalIds_member _ identity).mp member)
  simpa only [← canonicalEdges_ids edges, List.length_map] using bounded

/-- Empty-child removal and canonical selection retain profiles and cannot add rows. -/
theorem normalized_rows (edges : List (EdgeValue Symbol Guard))
    (profile : RowsShape rowLimit arityLimit edges) :
    RowsShape rowLimit arityLimit (canonicalEdges (surviving edges)) ∧
      (canonicalEdges (surviving edges)).length ≤ edges.length :=
  ⟨rows_canonical _ (rows_filter _ edges profile),
    Nat.le_trans (canonical_length_le _) (List.length_filter_le _ _)⟩

/-- Ordered recursive node profiles give the returned child profile and exact list length. -/
theorem children_of_all₂ {Input : Type} {inputs : List Input} {values : List (Value Symbol Guard)}
    (profiles : Language.All₂ (fun _ value => NodeShape rowLimit arityLimit value) inputs values) :
    ChildrenShape rowLimit arityLimit values ∧ values.length = inputs.length := by
  refine ⟨?_, profiles.length_eq.symm⟩
  induction profiles with
  | nil => trivial
  | cons first rest ih => exact ⟨first, ih⟩

/-- Ordered recursive edge profiles give the returned row profile and exact list length. -/
theorem rows_of_all₂ {Input : Type} {inputs : List Input} {edges : List (EdgeValue Symbol Guard)}
    (profiles : Language.All₂ (fun _ edge => EdgeShape rowLimit arityLimit edge) inputs edges) :
    RowsShape rowLimit arityLimit edges ∧ edges.length = inputs.length := by
  refine ⟨?_, profiles.length_eq.symm⟩
  induction profiles with
  | nil => trivial
  | cons first rest ih => exact ⟨first, ih⟩

/-- Actual raw edge construction retains the requested child profile on misses and cache hits. -/
theorem makeEdge [DecidableEq (EdgeKey Symbol Guard)]
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state)
    (available : ∀ value ∈ values, Available state value)
    (profile : ChildrenShape rowLimit arityLimit values) (arityBound : values.length ≤ arityLimit) :
    EdgeShape rowLimit arityLimit (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 := by
  cases result : (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 with
  | mk entry children =>
      have exactChildren := InternedShallowValues.makeEdge_children symbol guard values state coherent cached available
      rw [result] at exactChildren
      simp only [EdgeValue.children] at exactChildren
      subst children
      exact ⟨arityBound, profile⟩

/-- Actual normalized node construction retains bounded resident rows on misses and cache hits. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (profile : RowsShape rowLimit arityLimit edges) (rowBound : edges.length ≤ rowLimit) :
    NodeShape rowLimit arityLimit (run (InternedConstructorTemplates.makeNode edges) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  obtain ⟨selectedProfile, selectedLength⟩ := normalized_rows edges profile
  unfold InternedConstructorTemplates.makeNode
  dsimp only
  split
  · trivial
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa only [same] using selected)
    simp only [run, exactResult, identifyNode, NodeShape]
    exact ⟨Nat.le_trans (by simpa only [same] using selectedLength) rowBound,
      by simpa only [same] using selectedProfile⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputConstructors
