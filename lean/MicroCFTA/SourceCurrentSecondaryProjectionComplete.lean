import MicroCFTA.SourceCurrentSecondaryProjectionSupport
import MicroCFTA.SourceCurrentSecondaryProjectionEndpoint
import MicroCFTA.SourceCurrentSecondaryProjectionAnchor
import MicroCFTA.SourceEqualityProjectionAPI

/-!
# Finite selected projection from secondary gate certificates

Each selected child keeps a certificate in the completed gate heap.
Projection can allocate in later heaps. Those heaps retain semantic
readiness and the anchor records. The endpoint cost invariant belongs
only to the anchor. The induction decreases the natural path length.
-/
namespace MicroCFTA.SourceCurrentSecondaryProjectionComplete
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceCurrentSecondaryProjectionSupport

/-- Forest roots need closed operands; proper paths need support only for their selected value. -/
def ForestSupport [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (path : EqualityNormalize.Path) (values : List (Value Symbol Guard)) : Prop :=
  match path with
  | [] => ClosedValues values
  | index :: path => ∀ value, values[index]? = some value → Support unconstrained anchor path value

private theorem select_natural (values : List A) (index : Nat) :
    select values (Int.ofNat index) = values[index]? := by
  simp only [select, Int.ofNat_eq_natCast]
  rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index))]
  rfl

private theorem rows_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (path : EqualityNormalize.Path) (index : Nat)
    (childComplete : ∀ (value : Value Symbol Guard) before, SemanticReady before → Available before value →
      Grows anchor before → Support unconstrained anchor path value →
      ∃ result after, Project (path.map Int.ofNat) value before result after ∧ Keeps before after ∧
        SemanticReady after ∧ Available after result ∧ result.free = [])
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before edges) (growth : Grows anchor before)
    (supported : ∀ edge ∈ edges, ∀ child, edge.children[index]? = some child →
      Support unconstrained anchor path child) :
    ∃ results after, ProjectRows (path.map Int.ofNat) (Int.ofNat index) edges before results after ∧
      Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ClosedValues results := by
  induction edges generalizing before with
  | nil =>
      exact ⟨[], before, .nil, pure_keeps before semantic.ready, semantic,
        by simp [Values], by simp [ClosedValues]⟩
  | cons edge edges ih =>
      cases found : edge.children[index]? with
      | none =>
          obtain ⟨results, after, rest, kept, ready, available, closed⟩ := ih before semantic
            (fun value member => resident value (List.mem_cons_of_mem _ member)) growth
            (fun value member => supported value (List.mem_cons_of_mem _ member))
          exact ⟨results, after, .missing (by simpa only [select_natural] using found) rest,
            kept, ready, available, closed⟩
      | some child =>
          have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
            (resident edge List.mem_cons_self) child (List.mem_of_getElem? found)
          obtain ⟨result, middle, first, firstKept, middleReady, resultAvailable, resultClosed⟩ :=
            childComplete child before semantic childAvailable growth (supported edge List.mem_cons_self child found)
          obtain ⟨results, after, rest, restKept, finalReady, resultsAvailable, resultsClosed⟩ :=
            ih middle middleReady
              (fun original member => InternedEdgeResidency.edge_grows before middle firstKept.growth original
                (resident original (List.mem_cons_of_mem _ member)))
              (grows_trans growth firstKept.growth)
              (fun original member => supported original (List.mem_cons_of_mem _ member))
          refine ⟨result :: results, after,
            .selected (by simpa only [select_natural] using found) first rest,
            firstKept.trans restKept, finalReady, ?_, ?_⟩
          · intro value member
            rcases List.mem_cons.mp member with rfl | member
            · exact restKept.available _ resultAvailable
            · exact resultsAvailable value member
          · intro value member
            rcases List.mem_cons.mp member with rfl | member
            · exact resultClosed
            · exact resultsClosed value member

private theorem ordinary_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (path : EqualityNormalize.Path) (index : Nat)
    (childComplete : ∀ (value : Value Symbol Guard) before, SemanticReady before → Available before value →
      Grows anchor before → Support unconstrained anchor path value →
      ∃ result after, Project (path.map Int.ofNat) value before result after ∧ Keeps before after ∧
        SemanticReady after ∧ Available after result ∧ result.free = [])
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (growth : Grows anchor before) (ordinary : Ordinary value)
    (supported : ∀ edge ∈ InternedEdgeResidency.nodeEdges value, ∀ child,
      edge.children[index]? = some child → Support unconstrained anchor path child) :
    ∃ result after, Project ((index :: path).map Int.ofNat) value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  cases value with
  | empty =>
      exact ⟨.empty, before, .empty, pure_keeps before semantic.ready, semantic, available, rfl⟩
  | reference | union | mu => cases ordinary
  | node entry edges depth free =>
      obtain ⟨values, middle, rows, firstKept, middleReady, valuesAvailable, valuesClosed⟩ :=
        rows_complete unconstrained anchor path index childComplete edges before semantic
          (InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident)
          growth (by simpa only [InternedEdgeResidency.nodeEdges] using supported)
      obtain ⟨result, after, joined, restKept, finalReady, resultAvailable, resultClosed⟩ :=
        SourceEqualityProjectionUnion.complete values middle middleReady valuesAvailable valuesClosed
      exact ⟨result, after, .ordinary rows joined, firstKept.trans restKept,
        finalReady, resultAvailable, resultClosed⟩

/-- Anchor certificates derive finite actual projection in any retained semantic caller heap. -/
theorem node_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (path : EqualityNormalize.Path) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (supported : Support unconstrained anchor path value) :
    ∃ result after, Project (path.map Int.ofNat) value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  induction path generalizing value before with
  | nil =>
      have closed : value.free = [] := by
        rcases supported with closed | ⟨anchorAvailable, gate⟩
        · exact closed
        · exact SourceCurrentSecondaryProjectionEndpoint.endpoint_closed unconstrained gate anchorReady anchorAvailable
      exact ⟨value, before, .root, pure_keeps before semantic.ready, semantic, available, closed⟩
  | cons index path ih =>
      rcases supported with closed | ⟨anchorAvailable, gate⟩
      · exact SourceEqualityProjectionComplete.complete ((index :: path).map Int.ofNat)
          value before semantic available closed
      · cases value with
        | empty =>
            exact ⟨.empty, before, .empty, pure_keeps before semantic.ready, semantic, available, rfl⟩
        | reference | union => cases gate
        | node entry edges depth free =>
            exact ordinary_complete unconstrained anchor path index ih _ before semantic available growth True.intro
              (by
                intro edge member child found
                exact ordinary_selected_support (Or.inr ⟨anchorAvailable, gate⟩) anchorSemantic semantic available
                  edge member child found)
        | mu entry body depth ordinary =>
            obtain ⟨exposed, middle, head, firstKept, middleReady, exposedAvailable, ordinary⟩ :=
              SourceCurrentSecondaryProjectionSupport.head_complete gate anchorSemantic anchorAvailable before semantic available growth
            obtain ⟨result, after, projected, restKept, finalReady, resultAvailable, resultClosed⟩ :=
              ordinary_complete unconstrained anchor path index ih exposed middle middleReady exposedAvailable
                (grows_trans growth firstKept.growth) ordinary
                (by
                  intro edge member child found
                  exact head_selected_support gate anchorSemantic anchorAvailable semantic available growth head
                    edge member child found)
            exact ⟨result, after, .recursive True.intro head projected, firstKept.trans restKept,
              finalReady, resultAvailable, resultClosed⟩

/-- Every actual completed projection has the effects of the derived finite projection. -/
theorem node_verified [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {path : EqualityNormalize.Path} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project (path.map Int.ofNat) value before result after)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (supported : Support unconstrained anchor path value) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] := by
  obtain ⟨value, final, completed, kept, ready, resident, closed⟩ :=
    node_complete unconstrained anchor anchorSemantic anchorReady path value before semantic available growth supported
  obtain ⟨sameValue, sameState⟩ := SourceEqualityProjectionAPI.node_unique completed actual
  cases sameValue
  cases sameState
  exact ⟨kept, ready, resident, closed⟩

/-- Ordered actual row projections retain closed available results and exact intermediate effects. -/
theorem rows_verified [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {path : EqualityNormalize.Path} {index : Nat} {edges : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} {results : List (Value Symbol Guard)}
    (actual : ProjectRows (path.map Int.ofNat) (Int.ofNat index) edges before results after)
    (semantic : SemanticReady before) (resident : Edges before edges) (growth : Grows anchor before)
    (supported : ∀ edge ∈ edges, ∀ child, edge.children[index]? = some child →
      Support unconstrained anchor path child) :
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ClosedValues results := by
  induction edges generalizing before results after with
  | nil =>
      cases actual
      exact ⟨pure_keeps _ semantic.ready, semantic, by simp [Values], by simp [ClosedValues]⟩
  | cons edge edges ih =>
      cases actual with
      | missing absent rest =>
          exact ih rest semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member)) growth
            (fun edge member => supported edge (List.mem_cons_of_mem _ member))
      | @selected _ child _ _ result middle _ results _ _ found first rest =>
          have selected : edge.children[index]? = some child := by simpa only [select_natural] using found
          have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
            (resident edge List.mem_cons_self) child (List.mem_of_getElem? selected)
          have firstEffects := node_verified unconstrained anchor anchorSemantic anchorReady first semantic childAvailable growth
            (supported edge List.mem_cons_self child selected)
          have restEffects := ih rest firstEffects.2.1
            (fun original member => InternedEdgeResidency.edge_grows before middle firstEffects.1.growth original
              (resident original (List.mem_cons_of_mem _ member)))
            (grows_trans growth firstEffects.1.growth)
            (fun original member => supported original (List.mem_cons_of_mem _ member))
          refine ⟨firstEffects.1.trans restEffects.1, restEffects.2.1, ?_, ?_⟩
          · intro value member
            rcases List.mem_cons.mp member with rfl | member
            · exact restEffects.1.available _ firstEffects.2.2.1
            · exact restEffects.2.2.1 value member
          · intro value member
            rcases List.mem_cons.mp member with rfl | member
            · exact firstEffects.2.2.2
            · exact restEffects.2.2.2 value member

/-- A supported natural forest path derives finite actual projection in its current retained heap. -/
theorem forest_complete [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (path : EqualityNormalize.Path) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (supported : ForestSupport unconstrained anchor path values) :
    ∃ result after, Forest (path.map Int.ofNat) values before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  cases path with
  | nil =>
      obtain ⟨result, after, joined, rest⟩ := SourceEqualityProjectionUnion.complete values before semantic available supported
      exact ⟨result, after, .root joined, rest⟩
  | cons index path =>
      cases found : values[index]? with
      | none =>
          exact ⟨.empty, before, .missing (by simpa only [select_natural] using found),
            pure_keeps before semantic.ready, semantic, empty_available before, rfl⟩
      | some value =>
          obtain ⟨result, after, body, rest⟩ := node_complete unconstrained anchor anchorSemantic anchorReady path value before
            semantic (available value (List.mem_of_getElem? found)) growth (supported value found)
          exact ⟨result, after, .selected (by simpa only [select_natural] using found) body, rest⟩

/-- Every actual forest projection has the effects of the derived finite supported projection. -/
theorem forest_verified [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {path : EqualityNormalize.Path} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : Forest (path.map Int.ofNat) values before result after)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (supported : ForestSupport unconstrained anchor path values) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] := by
  obtain ⟨value, final, completed, kept, ready, resident, closed⟩ :=
    forest_complete unconstrained anchor anchorSemantic anchorReady path values before semantic available growth supported
  obtain ⟨sameValue, sameState⟩ := SourceEqualityProjectionAPI.forest_unique completed actual
  cases sameValue
  cases sameState
  exact ⟨kept, ready, resident, closed⟩

/-- A false proper forest gate supplies the support of its exact selected original value. -/
theorem false_path_support [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {anchor : State Symbol Guard}
    {path : EqualityNormalize.Path} {values : List (Value Symbol Guard)}
    (gate : SourceCurrentSecondaryTrace.PathTrace unconstrained values path anchor false anchor)
    (nonroot : path ≠ []) (available : Values anchor values) :
    ForestSupport unconstrained anchor path values := by
  cases path with
  | nil => exact False.elim (nonroot rfl)
  | cons index path =>
      cases gate with
      | child trace =>
          intro value found
          exact Or.inr ⟨available value (List.mem_of_getElem? found), SourceCurrentSecondaryReplay.false_selected trace found⟩

/-- An actual completed false node gate derives finite projection after later retained caller effects. -/
theorem false_node_complete [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    {initial final caller : State Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.NodeTrace unconstrained path value initial false final)
    (initialSemantic : SemanticReady initial) (initialReady : InternedFreshOrdinaryMemoGateTrace.Ready initial)
    (initialAvailable : Available initial value) (callerSemantic : SemanticReady caller)
    (callerAvailable : Available caller value) (growth : Grows final caller) :
    ∃ result after, Project (path.map Int.ofNat) value caller result after ∧ Keeps caller after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  have anchor := SourceCurrentSecondaryProjectionAnchor.node_anchor unconstrained gate initialSemantic initialReady initialAvailable
  exact node_complete unconstrained final anchor.1 anchor.2.1 path value caller callerSemantic callerAvailable growth
    (Or.inr ⟨anchor.2.2.2.1, anchor.2.2.2.2⟩)

/-- A false proper forest gate derives finite projection without a whole-forest closedness premise. -/
theorem false_path_complete [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : EqualityNormalize.Path}
    {values : List (Value Symbol Guard)} {initial final caller : State Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.PathTrace unconstrained values path initial false final)
    (nonroot : path ≠ []) (initialSemantic : SemanticReady initial)
    (initialReady : InternedFreshOrdinaryMemoGateTrace.Ready initial) (initialAvailable : Values initial values)
    (callerSemantic : SemanticReady caller) (callerAvailable : Values caller values) (growth : Grows final caller) :
    ∃ result after, Forest (path.map Int.ofNat) values caller result after ∧ Keeps caller after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  have anchor := SourceCurrentSecondaryProjectionAnchor.path_anchor unconstrained gate initialSemantic initialReady initialAvailable
  exact forest_complete unconstrained final anchor.1 anchor.2.1 path values caller callerSemantic callerAvailable growth
    (false_path_support anchor.2.2.2.2 nonroot anchor.2.2.2.1)

/-- Every actual later projection after a false proper gate has the derived closed-result effects. -/
theorem false_path_verified [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {path : EqualityNormalize.Path}
    {values : List (Value Symbol Guard)} {initial final caller after : State Symbol Guard} {result : Value Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.PathTrace unconstrained values path initial false final)
    (nonroot : path ≠ []) (initialSemantic : SemanticReady initial)
    (initialReady : InternedFreshOrdinaryMemoGateTrace.Ready initial) (initialAvailable : Values initial values)
    (callerSemantic : SemanticReady caller) (callerAvailable : Values caller values) (growth : Grows final caller)
    (actual : Forest (path.map Int.ofNat) values caller result after) :
    Keeps caller after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] := by
  obtain ⟨value, state, completed, kept, ready, resident, closed⟩ := false_path_complete gate nonroot
    initialSemantic initialReady initialAvailable callerSemantic callerAvailable growth
  obtain ⟨sameValue, sameState⟩ := SourceEqualityProjectionAPI.forest_unique completed actual
  cases sameValue
  cases sameState
  exact ⟨kept, ready, resident, closed⟩

end MicroCFTA.SourceCurrentSecondaryProjectionComplete
