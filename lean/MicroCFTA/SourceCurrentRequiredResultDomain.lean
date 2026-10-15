import MicroCFTA.SourceCurrentRequiredTipSupport
import MicroCFTA.SourceCurrentRequiredLanguageEffects
import MicroCFTA.SourceEqualityProjectionPathDomain

/-!
# Structural domains for reconstructed required-path results

Closed subtrees need no gate certificate. Open ordinary prefixes retain
domains only at selected stored child requirements. New ordinary records
do not need to exist in an earlier gate heap. The domain distinguishes
terminal requirements from intermediate ordinary prefixes.
-/
namespace MicroCFTA.SourceCurrentRequiredResultDomain
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentRequiredSupport (Tip)
open SourceEqualityProjectionPathDomain (NodeClosed ForestClosed)

/-- A required result is closed, or is an ordinary prefix with supported selected children. -/
inductive NodeDomain {Symbol Guard : Type} : Needed → Value Symbol Guard → Prop where
  | closed {value : Value Symbol Guard} (closed : value.free = []) : NodeDomain needed value
  | ordinary {edges : List (EdgeValue Symbol Guard)} (nonempty : entries ≠ [])
      (children : ∀ edge ∈ edges, ∀ index needed,
        SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some needed →
        ∀ child, edge.children[index]? = some child → NodeDomain needed child) :
      NodeDomain (.node entries) (.node entry edges depth free)

/-- Each present selected result retains the domain of its exact stored child requirement. -/
def ForestDomain (needed : Needed) (values : List (Value Symbol Guard)) : Prop :=
  match needed with
  | .node entries => ∀ index child, SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some child →
      ∀ value, values[index]? = some value → NodeDomain child value

/-- Reconstructed row children retain the same source requirement and positions. -/
def RowsDomain (needed : Needed) (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ edges, ForestDomain needed edge.children

/-- Actual child scans retain each selected result domain at its original offset. -/
def ChildrenDomain (entries : List (Int × Needed)) (offset : Nat) (values : List (Value Symbol Guard)) : Prop :=
  ∀ query needed, SourceEqualityNeededMap.lookup (Int.ofNat (offset + query)) entries = some needed →
    ∀ value, values[query]? = some value → NodeDomain needed value

/-- A terminal result domain implies actual cached free-list closedness. -/
theorem NodeDomain.empty_closed {value : Value Symbol Guard} (domain : NodeDomain (.node []) value) : value.free = [] := by
  cases domain with
  | closed closed => exact closed
  | ordinary nonempty => exact False.elim (nonempty rfl)

/-- A result list has the head requirement and the domain at the next original offset. -/
theorem children_cons {entries : List (Int × Needed)} {offset : Nat} {value : Value Symbol Guard}
    {values : List (Value Symbol Guard)}
    (first : ∀ needed, SourceEqualityNeededMap.lookup (Int.ofNat offset) entries = some needed → NodeDomain needed value)
    (rest : ChildrenDomain entries (offset + 1) values) : ChildrenDomain entries offset (value :: values) := by
  intro query needed found child selected
  cases query with
  | zero =>
      have same : value = child := Option.some.inj selected
      subst child
      exact first needed (by simpa using found)
  | succ query =>
      exact rest query needed (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found) child selected

private theorem makeNode_edge_member [DecidableEq (EdgeKey Symbol Guard)]
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state)
    (resident : Edges state edges) :
    ∀ edge ∈ InternedEdgeResidency.nodeEdges (run (makeNode edges) state).1, edge ∈ edges := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), InternedEdgeResidency.EdgeResident state edge := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · simp only [run, InternedEdgeResidency.nodeEdges, List.not_mem_nil, false_implies, implies_true]
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := InternedEdgeResidency.identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa only [same] using selected)
    simp only [run, readback, identifyNode, InternedEdgeResidency.nodeEdges]
    intro edge member
    have kept : edge ∈ canonicalEdges (surviving edges) := by rw [same]; exact member
    exact (List.mem_filter.mp (canonicalEdges_member (surviving edges) edge kept)).1

/-- Actual canonical node reconstruction retains every selected child domain of its resident rows. -/
theorem makeNode_domain [DecidableEq (EdgeKey Symbol Guard)]
    (entries : List (Int × Needed)) (nonempty : entries ≠ []) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state) (resident : Edges state edges)
    (domain : RowsDomain (.node entries) edges) : NodeDomain (.node entries) (run (makeNode edges) state).1 := by
  have ordinary := SourceEqualityRequiredCache.node_ordinary edges state facts resident
  generalize same : (run (makeNode edges) state).1 = value at ordinary ⊢
  cases value with
  | empty => exact .closed rfl
  | reference | union | mu => cases ordinary
  | node entry rows depth free =>
      apply NodeDomain.ordinary nonempty
      intro edge member index child found value selected
      exact domain edge (makeNode_edge_member edges state facts resident edge (by rw [same]; exact member))
        index child found value selected

private theorem closed_path [DecidableEq (EdgeKey Symbol Guard)]
    (path : List Int) (value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticReady state) (available : Available state value) (closed : value.free = []) : NodeClosed path value := by
  induction path generalizing value with
  | nil => simpa only [NodeClosed] using closed
  | cons index path ih =>
      cases value with
      | empty => simp only [NodeClosed]
      | reference | union | mu => simpa only [NodeClosed] using closed
      | node entry edges depth free =>
          rw [NodeClosed]
          intro edge member child selected
          have childClosed := MergedColdReaderClosed.node_children_closed state semantic.ready.semantic.1.normal.facts
            entry edges depth free available closed edge member child (SourceEqualityProjectionGraph.select_member selected)
          have childAvailable := available.children child (List.mem_flatMap.mpr
            ⟨edge, member, SourceEqualityProjectionGraph.select_member selected⟩)
          exact ih child childAvailable childClosed

private theorem select_natural (values : List A) (index : Nat) :
    SourceEqualityProjectionGraph.select values (Int.ofNat index) = values[index]? := by
  simp only [SourceEqualityProjectionGraph.select, Int.ofNat_eq_natCast]
  rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index))]
  rfl

/-- Each maximal tip of a structural result has the existing closed selected-path domain. -/
theorem NodeDomain.tip_closed [DecidableEq (EdgeKey Symbol Guard)]
    {needed : Needed} {path : EqualityNormalize.Path} (tip : Tip needed path)
    {value : Value Symbol Guard} (domain : NodeDomain needed value)
    {state : State Symbol Guard} (semantic : SemanticReady state) (available : Available state value) :
    NodeClosed (path.map Int.ofNat) value := by
  induction tip generalizing value with
  | leaf => simpa only [List.map_nil, NodeClosed] using domain.empty_closed
  | @child index entries needed path found rest ih =>
      cases domain with
      | closed closed => exact closed_path _ _ state semantic available closed
      | ordinary nonempty children =>
          rw [List.map_cons, NodeClosed]
          intro edge member child selected
          have natural : edge.children[index]? = some child := by simpa only [select_natural] using selected
          have childDomain := children edge member _ _ found child natural
          have childAvailable := available.children child (List.mem_flatMap.mpr
            ⟨edge, member, List.mem_of_getElem? natural⟩)
          exact ih childDomain childAvailable

/-- Every proper maximal result-forest tip has the existing actual forest projection domain. -/
theorem forest_tip_closed [DecidableEq (EdgeKey Symbol Guard)]
    {needed : Needed} {index : Nat} {path : EqualityNormalize.Path} {values : List (Value Symbol Guard)}
    (tip : Tip needed (index :: path)) (domain : ForestDomain needed values)
    {state : State Symbol Guard} (semantic : SemanticReady state) (available : Values state values) :
    ForestClosed ((index :: path).map Int.ofNat) values := by
  cases tip with
  | child found rest =>
      intro value selected
      have natural : values[index]? = some value := by simpa only [select_natural] using selected
      exact NodeDomain.tip_closed rest (domain index _ found value natural) semantic
        (available value (List.mem_of_getElem? natural))

end MicroCFTA.SourceCurrentRequiredResultDomain
