import MicroCFTA.SourceCurrentSecondaryProjectionComplete
import MicroCFTA.SourceSecondaryGateHeadHeap
import MicroCFTA.SourceEqualityAnnotationProjection

/-!
# Physical annotations through anchored natural-path projection

Actual selected children retain support at the completed gate anchor.
Current projection heaps need semantic readiness and retained anchor records.
Ordered child effects supply each next heap. Actual head reads preserve
annotations before recursive heads continue through ordinary rows.
The empty forest path retains its explicit whole-forest closedness premise.
-/
namespace MicroCFTA.SourceCurrentSecondaryProjectionHeap
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceEqualityAnnotationHeap (Heap)
open SourceCurrentSecondaryProjectionSupport
open SourceCurrentSecondaryProjectionComplete (ForestSupport)
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready

private theorem select_natural (values : List A) (index : Nat) :
    select values (Int.ofNat index) = values[index]? := by
  simp only [select, Int.ofNat_eq_natCast]
  rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index))]
  rfl

private theorem rows_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (path : EqualityNormalize.Path) (index : Nat)
    (childHeap : ∀ (value result : Value Symbol Guard) (before after : State Symbol Guard),
      Project (path.map Int.ofNat) value before result after → SemanticReady before → Available before value →
      Grows anchor before → Support unconstrained anchor path value → Heap annotation before → Heap annotation after)
    {edges : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    {results : List (Value Symbol Guard)}
    (actual : ProjectRows (path.map Int.ofNat) (Int.ofNat index) edges before results after)
    (semantic : SemanticReady before) (resident : Edges before edges) (growth : Grows anchor before)
    (supported : ∀ edge ∈ edges, ∀ child, edge.children[index]? = some child →
      Support unconstrained anchor path child) (fields : Heap annotation before) : Heap annotation after := by
  induction edges generalizing before results after with
  | nil => cases actual; exact fields
  | cons edge edges ih =>
      cases actual with
      | missing absent rest =>
          exact ih rest semantic (fun original member => resident original (List.mem_cons_of_mem _ member)) growth
            (fun original member => supported original (List.mem_cons_of_mem _ member)) fields
      | @selected _ child _ _ result middle _ results _ _ found first rest =>
          have selected : edge.children[index]? = some child := by simpa only [select_natural] using found
          have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
            (resident edge List.mem_cons_self) child (List.mem_of_getElem? selected)
          have childSupport := supported edge List.mem_cons_self child selected
          have firstEffects := SourceCurrentSecondaryProjectionComplete.node_verified unconstrained anchor
            anchorSemantic anchorReady first semantic childAvailable growth childSupport
          have middleFields := childHeap child result before middle first semantic childAvailable growth childSupport fields
          exact ih rest firstEffects.2.1
            (fun original member => InternedEdgeResidency.edge_grows before middle firstEffects.1.growth original
              (resident original (List.mem_cons_of_mem _ member)))
            (grows_trans growth firstEffects.1.growth)
            (fun original member => supported original (List.mem_cons_of_mem _ member)) middleFields

private theorem ordinary_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (path : EqualityNormalize.Path) (index : Nat)
    (childHeap : ∀ (value result : Value Symbol Guard) (before after : State Symbol Guard),
      Project (path.map Int.ofNat) value before result after → SemanticReady before → Available before value →
      Grows anchor before → Support unconstrained anchor path value → Heap annotation before → Heap annotation after)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project ((index :: path).map Int.ofNat) value before result after)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (ordinary : Ordinary value)
    (supported : ∀ edge ∈ InternedEdgeResidency.nodeEdges value, ∀ child,
      edge.children[index]? = some child → Support unconstrained anchor path child)
    (fields : Heap annotation before) : Heap annotation after := by
  cases value with
  | empty =>
      cases actual with
      | empty => exact fields
      | recursive impossible => cases impossible
  | reference | union | mu => cases ordinary
  | node entry edges depth free =>
      cases actual with
      | ordinary rows joined =>
          have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked
            _ available.resident
          have selectedSupport : ∀ edge ∈ edges, ∀ child, edge.children[index]? = some child →
              Support unconstrained anchor path child := by
            simpa only [InternedEdgeResidency.nodeEdges] using supported
          have rowEffects := SourceCurrentSecondaryProjectionComplete.rows_verified unconstrained anchor
            anchorSemantic anchorReady rows semantic resident growth selectedSupport
          have middleFields := rows_heap annotation unconstrained anchor anchorSemantic anchorReady path index
            childHeap rows semantic resident growth selectedSupport fields
          exact SourceEqualityAnnotationProjection.union annotation joined rowEffects.2.1
            rowEffects.2.2.1 rowEffects.2.2.2 middleFields
      | recursive impossible => cases impossible

/-- Actual supported node projection preserves physical annotations in its exact returned heap. -/
theorem node_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {path : EqualityNormalize.Path} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project (path.map Int.ofNat) value before result after)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (supported : Support unconstrained anchor path value) (fields : Heap annotation before) : Heap annotation after := by
  induction path generalizing value result before after with
  | nil => cases actual; exact fields
  | cons index path ih =>
      have childHeap : ∀ (value result : Value Symbol Guard) (before after : State Symbol Guard),
          Project (path.map Int.ofNat) value before result after → SemanticReady before → Available before value →
          Grows anchor before → Support unconstrained anchor path value → Heap annotation before → Heap annotation after := by
        intro value result before after actual semantic available growth supported fields
        exact ih actual semantic available growth supported fields
      rcases supported with closed | ⟨anchorAvailable, gate⟩
      · exact SourceEqualityAnnotationProjection.node annotation actual semantic available closed fields
      · cases value with
        | empty =>
            cases actual with
            | empty => exact fields
            | recursive impossible => cases impossible
        | reference | union => cases gate
        | node entry edges depth free =>
            exact ordinary_heap annotation unconstrained anchor anchorSemantic anchorReady path index childHeap
              actual semantic available growth True.intro
              (by
                intro edge member child found
                exact ordinary_selected_support (Or.inr ⟨anchorAvailable, gate⟩) anchorSemantic semantic available
                  edge member child found) fields
        | mu entry body depth ordinary =>
            cases actual with
            | recursive recursive head body =>
                have headEffects := SourceCurrentSecondaryProjectionSupport.head_verified gate anchorSemantic anchorAvailable
                  semantic available growth head
                have middleFields := SourceSecondaryGateHeadHeap.warm_head_heap annotation
                  (warm_head gate anchorSemantic anchorAvailable _ growth) semantic available fields head
                exact ordinary_heap annotation unconstrained anchor anchorSemantic anchorReady path index childHeap
                  body headEffects.2.1 headEffects.2.2.1 (grows_trans growth headEffects.1.growth) headEffects.2.2.2
                  (head_selected_support gate anchorSemantic anchorAvailable semantic available growth head) middleFields

/-- Supported forest projection preserves annotations, including the explicit closed root-union case. -/
theorem forest_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {path : EqualityNormalize.Path} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : Forest (path.map Int.ofNat) values before result after)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (supported : ForestSupport unconstrained anchor path values) (fields : Heap annotation before) :
    Heap annotation after := by
  cases path with
  | nil =>
      cases actual with
      | root joined => exact SourceEqualityAnnotationProjection.union annotation joined semantic available supported fields
  | cons index path =>
      cases actual with
      | missing => exact fields
      | selected found body =>
          have selected := found
          rw [select_natural] at selected
          exact node_heap annotation unconstrained anchor anchorSemantic anchorReady body semantic
            (available _ (List.mem_of_getElem? selected)) growth (supported _ selected) fields

/-- A false proper gate derives annotation preservation through its actual later forest projection. -/
theorem false_path_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : EqualityNormalize.Path}
    {values : List (Value Symbol Guard)} {initial final caller after : State Symbol Guard} {result : Value Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.PathTrace unconstrained values path initial false final)
    (nonroot : path ≠ []) (initialSemantic : SemanticReady initial)
    (initialReady : GateReady initial) (initialAvailable : Values initial values)
    (callerSemantic : SemanticReady caller) (callerAvailable : Values caller values) (growth : Grows final caller)
    (fields : Heap annotation caller) (actual : Forest (path.map Int.ofNat) values caller result after) :
    Heap annotation after := by
  have anchored := SourceCurrentSecondaryProjectionAnchor.path_anchor unconstrained gate
    initialSemantic initialReady initialAvailable
  exact forest_heap annotation unconstrained final anchored.1 anchored.2.1 actual callerSemantic callerAvailable growth
    (SourceCurrentSecondaryProjectionComplete.false_path_support anchored.2.2.2.2 nonroot anchored.2.2.2.1) fields

end MicroCFTA.SourceCurrentSecondaryProjectionHeap
