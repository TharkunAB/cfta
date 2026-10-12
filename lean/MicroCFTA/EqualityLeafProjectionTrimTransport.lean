import MicroCFTA.EqualityLeafProjectionTrim
import MicroCFTA.EqualityLeafProjectionCachePullback

/-!
# Trimming represented rows into the actual resident cache

Dead original rows need no runtime requests. Every retained original row
is resident in the actual parent. Its available children reconstruct there
without replaying proof-only row allocations.
-/
namespace MicroCFTA.EqualityLeafProjectionTrimTransport
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedEdgeResidency
open EqualityLeafProjectionSyntax (Tree Edge)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionPhysical EqualityLeafProjectionTrim

/-- A later occurrence witness can be trimmed into the cache retaining its exact physical result. -/
def Pullback [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (tree : Tree (Tag Symbol Guard) Leaf) : Prop :=
  ∀ before after, Facts before → Facts after →
    ∀ value, Available before value → Represents leaf tree after value →
      ∃ trimmed, Trim trimmed tree ∧ Represents leaf trimmed before value

/-- Strict child pullback retains the exact original source positions. -/
theorem forest [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (trees : List (Tree (Tag Symbol Guard) Leaf))
    (each : ∀ tree ∈ trees, Pullback leaf tree)
    (before after : State Symbol Guard) (beforeFacts : Facts before) (afterFacts : Facts after)
    (values : List (Value Symbol Guard)) (available : ∀ value ∈ values, Available before value)
    (represented : RepresentsForest leaf trees after values) :
    ∃ trimmed, TrimForest trimmed trees ∧ RepresentsForest leaf trimmed before values := by
  induction trees generalizing values with
  | nil =>
      have same : values = [] := (congrArg (fun result : List (Value Symbol Guard) × State Symbol Guard => result.1) represented).symm
      subst values
      exact ⟨[], .nil, rfl⟩
  | cons first rest ih =>
      obtain ⟨value, tail, rfl, headRep, tailRep⟩ := forest_decompose leaf first rest after afterFacts.coherent.valid values represented
      obtain ⟨head, headTrim, headClosed⟩ := each first (by simp) before after beforeFacts afterFacts value
        (available value (by simp)) headRep
      obtain ⟨remaining, tailTrim, tailClosed⟩ := ih (fun tree member => each tree (by simp [member])) tail
        (fun value member => available value (by simp [member])) tailRep
      exact ⟨head :: remaining, .cons headTrim tailTrim, forest_intro leaf head remaining before value tail headClosed tailClosed⟩

/-- Dead rows are removed before child pullback. Every live row reuses its exact resident edge record. -/
theorem rows [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leafAvailable : LeafAvailable leaf)
    (edges : List (Edge (Tag Symbol Guard) Leaf))
    (each : ∀ edge ∈ edges, ∀ child ∈ edge.children, Pullback leaf child)
    (before after : State Symbol Guard) (beforeFacts : Facts before) (afterFacts : Facts after)
    (values : List (EdgeValue Symbol Guard))
    (resident : ∀ edge ∈ values, dead edge = false → EdgeResident before edge)
    (represented : RepresentsEdges leaf edges after values) :
    ∃ trimmed, TrimEdges trimmed edges ∧ RepresentsEdges leaf trimmed before (surviving values) := by
  induction edges generalizing values with
  | nil =>
      have same : values = [] := (congrArg (fun result : List (EdgeValue Symbol Guard) × State Symbol Guard => result.1) represented).symm
      subst values
      exact ⟨[], .nil, rfl⟩
  | cons first rest ih =>
      cases first with
      | mk tag children =>
          obtain ⟨nodes, edge, tail, rfl, childrenRep, edgeClosed, tailRep⟩ :=
            edges_decompose leaf tag children rest after afterFacts.coherent.valid values represented
          obtain ⟨remaining, tailTrim, tailClosed⟩ := ih
            (fun edge member child present => each edge (by simp [member]) child present) tail
            (fun edge member live => resident edge (by simp [member]) live) tailRep
          cases live : dead edge with
          | true =>
              refine ⟨remaining, .drop tailTrim, ?_⟩
              unfold dead at live
              simpa only [surviving, List.filter_cons, live, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using tailClosed
          | false =>
              have edgeResident := resident edge (by simp) live
              have availableAfter := forest_available leaf leafAvailable children after afterFacts nodes childrenRep
              have fields := edge_fields tag nodes after afterFacts availableAfter edge edgeClosed
              have childrenAvailable : ∀ node ∈ nodes, Available before node := by
                intro node member
                exact beforeFacts.cached.edges edge.entry.key edge edgeResident node (fields.2.2 ▸ member)
              obtain ⟨trimmed, childrenTrim, childrenClosed⟩ := forest leaf children
                (fun child member => each (.mk tag children) (by simp) child member)
                before after beforeFacts afterFacts nodes childrenAvailable childrenRep
              have requested := EqualityLeafProjectionNullaryEdit.resident_edge_replay edge before beforeFacts.coherent edgeResident
              rw [fields.1, fields.2.1, fields.2.2] at requested
              refine ⟨.mk tag trimmed :: remaining, .keep childrenTrim tailTrim, ?_⟩
              have reconstructed := edges_intro leaf tag trimmed remaining before nodes edge (surviving tail) childrenClosed requested tailClosed
              unfold dead at live
              simpa only [surviving, List.filter_cons, live, Bool.not_false, ↓reduceIte] using reconstructed

/-- Filtering dead rows is already part of the exact source node request. -/
theorem makeNode_surviving (edges : List (EdgeValue Symbol Guard)) : makeNode (surviving edges) = makeNode edges := by
  have same : surviving (surviving edges) = surviving edges := by simp [surviving, List.filter_filter]
  simp only [makeNode, same]

/-- A parent witness trims into its actual resident cache from strict-child pullback. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard)) (leafAvailable : LeafAvailable leaf)
    (edges : List (Edge (Tag Symbol Guard) Leaf))
    (each : ∀ edge ∈ edges, ∀ child ∈ edge.children, Pullback leaf child)
    (before after : State Symbol Guard) (beforeFacts : Facts before) (afterFacts : Facts after)
    (value : Value Symbol Guard) (available : Available before value)
    (represented : Represents leaf (.node edges) after value) :
    ∃ trimmed, Trim trimmed (.node edges) ∧ Represents leaf trimmed before value := by
  obtain ⟨original, originalClosed, parentClosed⟩ := node_decompose leaf edges after afterFacts.coherent.valid value represented
  have rowFacts := compileEdges_available leaf leafAvailable edges after afterFacts
  rw [originalClosed] at rowFacts
  have outgoing := makeNode_edges original after afterFacts.coherent afterFacts.linked (fun edge member => (rowFacts.2 edge member).1)
  rw [parentClosed] at outgoing
  have liveResident : ∀ edge ∈ original, dead edge = false → EdgeResident before edge := by
    intro edge member live
    apply resident_edges before beforeFacts.linked value available.resident edge
    rw [outgoing]
    exact (normalized_member after afterFacts.coherent original (fun edge member => (rowFacts.2 edge member).1) edge).mpr ⟨member, live⟩
  obtain ⟨trimmed, rowsTrim, rowsClosed⟩ := rows leaf leafAvailable edges each before after beforeFacts afterFacts original liveResident originalClosed
  have parentEarlier := EqualityLeafProjectionCachePullback.makeNode_pullback original before after beforeFacts.coherent
    afterFacts.coherent value available.resident parentClosed
  refine ⟨.node trimmed, .node rowsTrim, ?_⟩
  apply node_intro leaf trimmed before value (surviving original) rowsClosed
  rw [makeNode_surviving]
  exact parentEarlier

end MicroCFTA.EqualityLeafProjectionTrimTransport
